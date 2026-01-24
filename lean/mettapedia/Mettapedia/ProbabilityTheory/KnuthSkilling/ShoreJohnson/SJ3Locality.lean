import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.GradientSeparability
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.TheoremI
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.AppendixMinimizer
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.TwoBlock

/-!
# SJ3 -> locality (work in progress)

This file is a focused workspace for the Shore–Johnson Appendix A step:

*SJ3 (subset independence) -> locality of the shift2 derivative.*

In our main development (`GradientSeparability.lean`), locality is currently kept
as an explicit assumption (`DerivLocalAssumption`), scoped to EV-minimizers, and upgraded to
all interior points via an explicit richness premise (`EVRichness`).

Here we start the derivation of that minimizer-scoped locality from SJ3 using the existing
two-block (`twoBlock`) and expected-value (`EVConstraintSet`) infrastructure.

Important: this is an **in-progress** proof file and is not imported by the main library yet.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.SJ3Locality

open Classical

open Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Inference
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Objective
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Constraints
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.GradientSeparability
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.TheoremI
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.AppendixMinimizer
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.TwoBlock

/-!
## Target statement (minimizer-scoped locality)

`DerivLocalAssumption F hDiff` is intentionally a statement *about derivatives at minimizers*:
it only assumes `q` and `q'` are minimizers for *some* EV constraint sets.

To derive it from SJ3, we will need:

1. a way to embed an EV inference problem into a two-block problem where the “irrelevant” block
   can be varied independently,
2. a stationarity/KKT layer tying minimizers to first-order equations (see `TheoremIRegularity`),
3. a derivative-transport lemma connecting the two-block embedding back to the original shift2
   derivative along a chosen coordinate pair.

At present, (3) is the key missing infrastructure.
-/

/-! ## Symmetry infrastructure (SJ Lemma II, objective-level)

In the Shore–Johnson Appendix, permutation invariance is used to replace `F` by a symmetric
objective (average over all permutations), which has the same minimizers.

For the derivative-level locality proof, it is technically convenient to assume *objective*
permutation invariance directly, and then transport shift2 derivatives under permutations.
This matches the effect of the symmetrization step, without duplicating its construction here.
-/

/-! ## Two-block transport helpers

We re-export the core two-block/shift2 lemmas here for use in the SJ3-locality derivation.
These are proved in `TwoBlock.lean` and are stated with explicit positivity
assumptions to remain mathlib-grade.
-/

theorem shift2ProbClamp_twoBlock_left_of_mem
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
        (_root_.Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Appendix.shift2Prob
          P₁ i j hij u hu0 hu1) P₂ := by
  simpa using
    (TwoBlock.shift2ProbClamp_twoBlock_inl_of_mem
      (w := w) (hw0 := hw0) (hw1 := hw1)
      (P₁ := P₁) (P₂ := P₂) (i := i) (j := j) (hij := hij) (u := u) (hu0 := hu0) (hu1 := hu1))

theorem hasDerivAt_shift2ProbClamp_scaled_left
    {F : ObjectiveFunctional} {n : ℕ} (p q : ProbDist n)
    (i j : Fin n) (hij : i ≠ j) (w u0 : ℝ)
    (hqi : q.p i = w * u0) {L : ℝ}
    (h : HasDerivAt (fun t => F.D (shift2ProbClamp q i j hij t) p) L (q.p i)) :
    HasDerivAt (fun u => F.D (shift2ProbClamp q i j hij (w * u)) p) (w * L) u0 := by
  simpa using
    (TwoBlock.hasDerivAt_shift2ProbClamp_scaled
      (p := p) (q := q) (i := i) (j := j) (hij := hij) (w := w) (u0 := u0) (hqi := hqi)
      (L := L) h)

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
  simpa using
    (TwoBlock.hasDerivAt_twoBlock_left_shift2ProbClamp
      (w := w) (hw0 := hw0) (hw1 := hw1) (P₁ := P₁) (P₂ := P₂) (p := p)
      (i := i) (j := j) (hij := hij) (u0 := u0) (hqi := hqi) (hu0 := hu0) (hu1 := hu1)
      (L := L) h)

/-- Objective-level permutation invariance: values are unchanged under relabeling. -/
def ObjectivePermuteInvariant (F : ObjectiveFunctional) : Prop :=
  ∀ {n : ℕ} (σ : Equiv.Perm (Fin n)) (p q : ProbDist n),
    F.D (ProbDist.permute σ q) (ProbDist.permute σ p) = F.D q p

/-- Derivative-level permutation invariance for shift2 derivatives. -/
def DerivPermuteInvariant (F : ObjectiveFunctional) (hDiff : HasShift2Deriv F) : Prop :=
  ∀ {n : ℕ} (σ : Equiv.Perm (Fin n)) (p q : ProbDist n)
    (i j : Fin n) (hij : i ≠ j)
    (hp : ∀ k, 0 < p.p k) (hq : ∀ k, 0 < q.p k),
    Classical.choose (hDiff.deriv_exists p q i j hij hp hq) =
      Classical.choose (hDiff.deriv_exists
        (ProbDist.permute σ p) (ProbDist.permute σ q)
        (σ i) (σ j) (σ.injective.ne_iff.mpr hij)
        (fun k => hp (σ.symm k)) (fun k => hq (σ.symm k)))

/-- If the objective is permutation-invariant, then shift2 derivatives transport under permutations.

This is the derivative-level shadow of the SJ symmetrization step (Lemma II).
-/
theorem derivPermuteInvariant_of_objectivePermuteInvariant
    (F : ObjectiveFunctional) (hDiff : HasShift2Deriv F)
    (hPerm : ObjectivePermuteInvariant F) :
    DerivPermuteInvariant F hDiff := by
  intro n σ p q i j hij hp hq
  -- Define the two 1D curves and show they are identical by permutation-invariance.
  let φ := fun t => F.D (shift2ProbClamp q i j hij t) p
  let ψ := fun t =>
    F.D (shift2ProbClamp (ProbDist.permute σ q) (σ i) (σ j) (σ.injective.ne_iff.mpr hij) t)
      (ProbDist.permute σ p)
  have hφψ : φ = ψ := by
    funext t
    -- Permute the clamped shift2 curve and use invariance of F.D.
    have hperm :
        ProbDist.permute σ (shift2ProbClamp q i j hij t) =
          shift2ProbClamp (ProbDist.permute σ q) (σ i) (σ j)
            (σ.injective.ne_iff.mpr hij) t :=
      _root_.Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.AppendixMinimizer.permute_shift2ProbClamp
        (σ := σ) (q := q) (i := i) (j := j) (hij := hij) (t := t)
    -- Rewrite using objective invariance.
    simpa [φ, ψ, hperm] using (hPerm (σ := σ) (p := p) (q := shift2ProbClamp q i j hij t)).symm
  -- Since the functions are equal, their derivatives at the corresponding points are equal.
  have hDeriv₁ :
      HasDerivAt φ (Classical.choose (hDiff.deriv_exists p q i j hij hp hq)) (q.p i) :=
    Classical.choose_spec (hDiff.deriv_exists p q i j hij hp hq)
  have hDeriv₂ :
      HasDerivAt ψ
        (Classical.choose
          (hDiff.deriv_exists
            (ProbDist.permute σ p) (ProbDist.permute σ q)
            (σ i) (σ j) (σ.injective.ne_iff.mpr hij)
            (fun k => hp (σ.symm k)) (fun k => hq (σ.symm k))))
        ((ProbDist.permute σ q).p (σ i)) :=
    Classical.choose_spec
      (hDiff.deriv_exists
        (ProbDist.permute σ p) (ProbDist.permute σ q)
        (σ i) (σ j) (σ.injective.ne_iff.mpr hij)
        (fun k => hp (σ.symm k)) (fun k => hq (σ.symm k)))
  -- The evaluation points agree after permutation.
  have hpoint : (ProbDist.permute σ q).p (σ i) = q.p i := by
    simp [ProbDist.permute_apply]
  -- Transport derivatives across definitional equality of curves.
  have hDeriv₂' :
      HasDerivAt φ
        (Classical.choose
          (hDiff.deriv_exists
            (ProbDist.permute σ p) (ProbDist.permute σ q)
            (σ i) (σ j) (σ.injective.ne_iff.mpr hij)
            (fun k => hp (σ.symm k)) (fun k => hq (σ.symm k))))
        (q.p i) := by
    simpa [hφψ, hpoint] using hDeriv₂
  exact (hDeriv₁.unique hDeriv₂')

theorem twoBlock_permute_swap_eq
    {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m)
    (i : Fin n) (j : Fin m)
    (hij : w * P₁.p i = (1 - w) * P₂.p j) :
    ProbDist.permute (Equiv.swap (inlFin (n := n) (m := m) i) (inrFin (n := n) (m := m) j))
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂) =
      ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) P₁ P₂ := by
  apply ProbDist.ext
  intro k
  classical
  by_cases hk_i : k = inlFin (n := n) (m := m) i
  · subst hk_i
    simp [ProbDist.permute_apply, hij, twoBlock_apply_inl, twoBlock_apply_inr]
  by_cases hk_j : k = inrFin (n := n) (m := m) j
  · subst hk_j
    simp [ProbDist.permute_apply, hij, twoBlock_apply_inl, twoBlock_apply_inr]
  have hswap :
      (Equiv.swap (inlFin (n := n) (m := m) i) (inrFin (n := n) (m := m) j)) k = k := by
    exact
      (Equiv.swap_apply_of_ne_of_ne (a := inlFin (n := n) (m := m) i)
        (b := inrFin (n := n) (m := m) j) (x := k) hk_i hk_j)
  simp [ProbDist.permute_apply, hswap]

/-- **Two-block derivative transport (minimal analytic lemma)**:
embedding a system into a two-block construction does not change the shift2 derivative
within each block.

This is strictly weaker than full ratio-invariance and is the exact transport fact
used in the SJ3 → locality proof. -/
structure DerivTwoBlockTransport (F : ObjectiveFunctional) (hDiff : HasShift2Deriv F) : Prop where
  left :
    ∀ {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
      (p q : ProbDist n) (p' q' : ProbDist m)
      (i j : Fin n) (hij : i ≠ j)
      (hp : ∀ k, 0 < p.p k) (hq : ∀ k, 0 < q.p k)
      (hpComb :
        ∀ k,
          0 <
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p').p k)
      (hqComb :
        ∀ k,
          0 <
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q').p k),
      Classical.choose
          (hDiff.deriv_exists
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p')
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q')
            (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j)
            (by
              intro h
              exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h))
            hpComb hqComb) =
        Classical.choose (hDiff.deriv_exists p q i j hij hp hq)
  right :
    ∀ {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
      (p q : ProbDist n) (p' q' : ProbDist m)
      (i' j' : Fin m) (hi'j' : i' ≠ j')
      (hp' : ∀ k, 0 < p'.p k) (hq' : ∀ k, 0 < q'.p k)
      (hpComb :
        ∀ k,
          0 <
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p').p k)
      (hqComb :
        ∀ k,
          0 <
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q').p k),
      Classical.choose
          (hDiff.deriv_exists
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p')
            (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q')
            (inrFin (n := n) (m := m) i') (inrFin (n := n) (m := m) j')
            (by
              intro h
              exact hi'j' ((inrFin_eq_inrFin (n := n) (m := m)).1 h))
            hpComb hqComb) =
        Classical.choose (hDiff.deriv_exists p' q' i' j' hi'j' hp' hq')

/-- Ratio invariance implies the two-block transport property. -/
theorem derivTwoBlockTransport_of_ratio
    (F : ObjectiveFunctional) (hDiff : HasShift2Deriv F)
    (hRatio : DerivRatioInvariant F hDiff) :
    DerivTwoBlockTransport F hDiff := by
  refine ⟨?left, ?right⟩
  · intro n m w hw0 hw1 p q p' q' i j hij hp hq hpComb hqComb
    have hij_inl :
        inlFin (n := n) (m := m) i ≠ inlFin (n := n) (m := m) j := by
      intro h
      exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h)
    have hwne : w ≠ 0 := ne_of_gt hw0
    have hratio_i :
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q').p
            (inlFin (n := n) (m := m) i) /
          (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p').p
            (inlFin (n := n) (m := m) i) =
          q.p i / p.p i := by
      simp [twoBlock_apply_inl, mul_div_mul_left, hwne]
    have hratio_j :
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q').p
            (inlFin (n := n) (m := m) j) /
          (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p').p
            (inlFin (n := n) (m := m) j) =
          q.p j / p.p j := by
      simp [twoBlock_apply_inl, mul_div_mul_left, hwne]
    exact
      hRatio
        (p := ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p')
        (q := ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q')
        (p' := p) (q' := q)
        (i := inlFin (n := n) (m := m) i) (j := inlFin (n := n) (m := m) j)
        (i' := i) (j' := j) (hij := hij_inl) (hi'j' := hij)
        (hp := hpComb) (hq := hqComb) (hp' := hp) (hq' := hq)
        hratio_i hratio_j
  · intro n m w hw0 hw1 p q p' q' i' j' hi'j' hp' hq' hpComb hqComb
    have hi'j'_inr :
        inrFin (n := n) (m := m) i' ≠ inrFin (n := n) (m := m) j' := by
      intro h
      exact hi'j' ((inrFin_eq_inrFin (n := n) (m := m)).1 h)
    have h1wne : 1 - w ≠ 0 := ne_of_gt (sub_pos.mpr hw1)
    have hratio_i :
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q').p
            (inrFin (n := n) (m := m) i') /
          (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p').p
            (inrFin (n := n) (m := m) i') =
          q'.p i' / p'.p i' := by
      simp [twoBlock_apply_inr, mul_div_mul_left, h1wne]
    have hratio_j :
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q').p
            (inrFin (n := n) (m := m) j') /
          (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p').p
            (inrFin (n := n) (m := m) j') =
          q'.p j' / p'.p j' := by
      simp [twoBlock_apply_inr, mul_div_mul_left, h1wne]
    exact
      hRatio
        (p := ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p')
        (q := ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q')
        (p' := p') (q' := q')
        (i := inrFin (n := n) (m := m) i') (j := inrFin (n := n) (m := m) j')
        (i' := i') (j' := j') (hij := hi'j'_inr) (hi'j' := hi'j')
        (hp := hpComb) (hq := hqComb) (hp' := hp') (hq' := hq')
        hratio_i hratio_j

theorem eq_twoBlock_of_isMinimizer_twoBlock_ev_of_realizesEV
    {I : Inference.InferenceMethod} {F : ObjectiveFunctional}
    (hSJ : Inference.ShoreJohnsonAxioms I) (hF : RealizesEV I F) :
    ∀ {n m : ℕ} (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
      (p₁ : ProbDist n) (p₂ : ProbDist m)
      (cs₁ : EVConstraintSet n) (cs₂ : EVConstraintSet m)
      (q₁ : ProbDist n) (q₂ : ProbDist m) (q : ProbDist (n + m)),
      IsMinimizer F p₁ (toConstraintSet cs₁) q₁ →
      IsMinimizer F p₂ (toConstraintSet cs₂) q₂ →
      IsMinimizer F (Inference.ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p₁ p₂)
        (toConstraintSet (twoBlockConstraints (n := n) (m := m) w cs₁ cs₂)) q →
      q = Inference.ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q₁ q₂ := by
  intro n m w hw0 hw1 p₁ p₂ cs₁ cs₂ q₁ q₂ q hq₁ hq₂ hq
  have heq :
      toConstraintSet (twoBlockConstraints (n := n) (m := m) w cs₁ cs₂) =
        Inference.ConstraintSet.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
          (toConstraintSet cs₁) (toConstraintSet cs₂) :=
    twoBlockConstraints_equiv_set (n := n) (m := m) w hw0 hw1 cs₁ cs₂
  have hInf₁ : I.Infer p₁ (toConstraintSet cs₁) q₁ :=
    (hF.infer_iff_minimizer_ev (p := p₁) (cs := cs₁) (q := q₁)).2 hq₁
  have hInf₂ : I.Infer p₂ (toConstraintSet cs₂) q₂ :=
    (hF.infer_iff_minimizer_ev (p := p₂) (cs := cs₂) (q := q₂)).2 hq₂
  have hInf' :
      I.Infer (Inference.ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p₁ p₂)
        (toConstraintSet (twoBlockConstraints (n := n) (m := m) w cs₁ cs₂)) q := by
    rcases hq with ⟨hq_mem, hq_le⟩
    refine (hF.infer_iff_minimizer_ev (p := _)
      (cs := twoBlockConstraints (n := n) (m := m) w cs₁ cs₂) (q := q)).2 ?_
    refine ⟨?_, hq_le⟩
    simpa [heq] using hq_mem
  have hInf :
      I.Infer (Inference.ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p₁ p₂)
        (Inference.ConstraintSet.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
          (toConstraintSet cs₁) (toConstraintSet cs₂)) q := by
    simpa [heq] using hInf'
  exact hSJ.subset_independent_twoBlock w (le_of_lt hw0) (le_of_lt hw1) p₁ p₂
    (toConstraintSet cs₁) (toConstraintSet cs₂) q₁ q₂ q hInf₁ hInf₂ hInf

theorem sj3_implies_derivLocalAssumption_of_transport
    (I : InferenceMethod) (F : ObjectiveFunctional)
    (hSJ : ShoreJohnsonAxioms I)
    (hRealize : RealizesEV I F)
    (hReg : TheoremIRegularity F)
    (hPerm : ObjectivePermuteInvariant F)
    (hTransport : DerivTwoBlockTransport F ⟨hReg.has_shift2_deriv⟩) :
    DerivLocalAssumption F ⟨hReg.has_shift2_deriv⟩ := by
  intro n m p q p' q' i j i' j' hij hi'j' hp hq hp' hq' hMin hMin' h_qi h_pi h_qj h_pj

  /-
  TODO (high-level plan):

  - Unpack `hMin : IsEVMinimizer F p q` and `hMin' : IsEVMinimizer F p' q'` to get EV constraint sets
    `cs` and `cs'` for which `q` and `q'` are minimizers.

  - Use permutations to reduce to the case where the distinguished indices are `(0,1)` in each system.
    This will require a “permute transport” lemma for shift2 derivatives of `F.D` under `ProbDist.permute`.

  - Embed both problems into a larger two-block system with a freely-variable “irrelevant” block and
    apply SJ3 (via `eq_twoBlock_of_isMinimizer_twoBlock_ev`) to show the relevant 2-block posterior
    is independent of the irrelevant block.

  - Use the stationarity/KKT layer from `TheoremIRegularity` to express the shift2 derivative at the
    combined minimizer in terms of only the relevant block’s data; then transport back to the
    original (unembedded) derivative.

  Additional assumption used here:
  - **Two-block derivative transport** (`DerivTwoBlockTransport`): embedding into a
    two-block system does not change derivatives within each block. This is the
    minimal analytic lemma sufficient for SJ3 → locality and follows from
    full ratio-invariance.
  -/

  -- Step 1: Unpack the EV-minimizers.
  rcases hMin with ⟨cs, hmin⟩
  rcases hMin' with ⟨cs', hmin'⟩

  -- Step 2: Build a two-block problem and use SJ3 to identify its minimizer.
  -- We fix a nontrivial block mass `w = 1/2`.
  let w : ℝ := (1 / 2 : ℝ)
  have hw0 : 0 < w := by
    norm_num
  have hw1 : w < 1 := by
    norm_num

  let pComb : ProbDist (n + m) :=
    ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) p p'
  let CComb : EVConstraintSet (n + m) :=
    twoBlockConstraints (n := n) (m := m) w cs cs'

  -- Existence/uniqueness of inferred posterior for the combined constraint set.
  obtain ⟨qComb, hInfComb, huniqComb⟩ :=
    hSJ.unique (p := pComb) (C := toConstraintSet CComb)

  -- Translate inference into minimizerhood for the combined EV constraints.
  have hminComb : IsMinimizer F pComb (toConstraintSet CComb) qComb :=
    (hRealize.infer_iff_minimizer_ev (p := pComb) (cs := CComb) (q := qComb)).1 hInfComb

  -- SJ3 identifies the combined minimizer as a two-block posterior.
  have hCombEq :
      qComb =
        ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q' :=
    eq_twoBlock_of_isMinimizer_twoBlock_ev_of_realizesEV
      (hSJ := hSJ) (hF := hRealize) (w := w) (hw0 := hw0) (hw1 := hw1)
      (p₁ := p) (p₂ := p') (cs₁ := cs) (cs₂ := cs')
      (q₁ := q) (q₂ := q') (q := qComb) hmin hmin' hminComb

  -- Step 3: Use permutation invariance + two-block transport to relate derivatives.
  let hDiff : HasShift2Deriv F := ⟨hReg.has_shift2_deriv⟩
  have hPermDeriv : DerivPermuteInvariant F hDiff :=
    derivPermuteInvariant_of_objectivePermuteInvariant F hDiff hPerm
  have hTransport' : DerivTwoBlockTransport F hDiff := by
    exact hTransport

  -- Positivity on the combined distributions.
  have hpComb : ∀ k, 0 < pComb.p k := by
    intro k
    classical
    cases h : (finSumFinEquiv (m := n) (n := m)).symm k with
    | inl i0 =>
        have hk : k = inlFin (n := n) (m := m) i0 := by
          simpa [inlFin] using
            congrArg (fun s => (finSumFinEquiv (m := n) (n := m)) s) h
        subst hk
        exact twoBlock_pos_inl_of_pos (w := w) (hw0 := hw0) (hw1 := hw1) (P₁ := p) (P₂ := p') i0 hp
    | inr j0 =>
        have hk : k = inrFin (n := n) (m := m) j0 := by
          simpa [inrFin] using
            congrArg (fun s => (finSumFinEquiv (m := n) (n := m)) s) h
        subst hk
        exact twoBlock_pos_inr_of_pos (w := w) (hw0 := hw0) (hw1 := hw1) (P₁ := p) (P₂ := p') j0 hp'

  have hqComb : ∀ k, 0 < qComb.p k := by
    intro k
    classical
    cases h : (finSumFinEquiv (m := n) (n := m)).symm k with
    | inl i0 =>
        have hk : k = inlFin (n := n) (m := m) i0 := by
          simpa [inlFin] using
            congrArg (fun s => (finSumFinEquiv (m := n) (n := m)) s) h
        subst hk
        simpa [hCombEq] using
          (twoBlock_pos_inl_of_pos (w := w) (hw0 := hw0) (hw1 := hw1) (P₁ := q) (P₂ := q') i0 hq)
    | inr j0 =>
        have hk : k = inrFin (n := n) (m := m) j0 := by
          simpa [inrFin] using
            congrArg (fun s => (finSumFinEquiv (m := n) (n := m)) s) h
        subst hk
        simpa [hCombEq] using
          (twoBlock_pos_inr_of_pos (w := w) (hw0 := hw0) (hw1 := hw1) (P₁ := q) (P₂ := q') j0 hq')

  -- Swap permutations for matching coordinates.
  let σi : Equiv.Perm (Fin (n + m)) :=
    Equiv.swap (inlFin (n := n) (m := m) i) (inrFin (n := n) (m := m) i')
  let σj : Equiv.Perm (Fin (n + m)) :=
    Equiv.swap (inlFin (n := n) (m := m) j) (inrFin (n := n) (m := m) j')

  have hpiw : w * p.p i = (1 - w) * p'.p i' := by
    have hhalf : 1 - w = w := by
      norm_num [w]
    calc
      w * p.p i = (1 - w) * p.p i := by simp [hhalf]
      _ = (1 - w) * p'.p i' := by simp [h_pi]
  have hpjw : w * p.p j = (1 - w) * p'.p j' := by
    have hhalf : 1 - w = w := by
      norm_num [w]
    calc
      w * p.p j = (1 - w) * p.p j := by simp [hhalf]
      _ = (1 - w) * p'.p j' := by simp [h_pj]
  have hqiw : w * q.p i = (1 - w) * q'.p i' := by
    have hhalf : 1 - w = w := by
      norm_num [w]
    calc
      w * q.p i = (1 - w) * q.p i := by simp [hhalf]
      _ = (1 - w) * q'.p i' := by simp [h_qi]
  have hqjw : w * q.p j = (1 - w) * q'.p j' := by
    have hhalf : 1 - w = w := by
      norm_num [w]
    calc
      w * q.p j = (1 - w) * q.p j := by simp [hhalf]
      _ = (1 - w) * q'.p j' := by simp [h_qj]

  have hpComb_perm_i : ProbDist.permute σi pComb = pComb := by
    dsimp [pComb, σi]
    exact
      (twoBlock_permute_swap_eq (w := w) (hw0 := hw0) (hw1 := hw1)
        (P₁ := p) (P₂ := p') (i := i) (j := i') hpiw)
  have hpComb_perm_j : ProbDist.permute σj pComb = pComb := by
    dsimp [pComb, σj]
    exact
      (twoBlock_permute_swap_eq (w := w) (hw0 := hw0) (hw1 := hw1)
        (P₁ := p) (P₂ := p') (i := j) (j := j') hpjw)

  have hqComb_perm_i : ProbDist.permute σi qComb = qComb := by
    dsimp [σi]
    simpa [hCombEq] using
      (twoBlock_permute_swap_eq (w := w) (hw0 := hw0) (hw1 := hw1)
        (P₁ := q) (P₂ := q') (i := i) (j := i') hqiw)
  have hqComb_perm_j : ProbDist.permute σj qComb = qComb := by
    dsimp [σj]
    simpa [hCombEq] using
      (twoBlock_permute_swap_eq (w := w) (hw0 := hw0) (hw1 := hw1)
        (P₁ := q) (P₂ := q') (i := j) (j := j') hqjw)

  -- Index inequality helpers.
  have hij_inl : inlFin (n := n) (m := m) i ≠ inlFin (n := n) (m := m) j := by
    intro h
    exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h)
  have hi'j'_inr : inrFin (n := n) (m := m) i' ≠ inrFin (n := n) (m := m) j' := by
    intro h
    exact hi'j' ((inrFin_eq_inrFin (n := n) (m := m)).1 h)
  have h_inr_inl : inrFin (n := n) (m := m) i' ≠ inlFin (n := n) (m := m) j := by
    intro h
    exact (inlFin_ne_inrFin (n := n) (m := m) j i') h.symm

  -- Step 3a: permutation invariance inside the combined system.
  have hL1 :
      Classical.choose (hDiff.deriv_exists pComb qComb
        (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j) hij_inl hpComb hqComb) =
      Classical.choose (hDiff.deriv_exists pComb qComb
        (inrFin (n := n) (m := m) i') (inlFin (n := n) (m := m) j) h_inr_inl hpComb hqComb) := by
    have hperm :=
      hPermDeriv (σ := σi) (p := pComb) (q := qComb)
        (i := inlFin (n := n) (m := m) i) (j := inlFin (n := n) (m := m) j)
        (hij := hij_inl) (hp := hpComb) (hq := hqComb)
    -- Simplify the permuted distributions and swapped indices.
    have hσi_i :
        σi (inlFin (n := n) (m := m) i) = inrFin (n := n) (m := m) i' := by
      simp [σi]
    have hσi_j :
        σi (inlFin (n := n) (m := m) j) = inlFin (n := n) (m := m) j := by
      have hji :
          inlFin (n := n) (m := m) j ≠ inlFin (n := n) (m := m) i := by
        intro h
        exact hij ((inlFin_eq_inlFin (n := n) (m := m)).1 h).symm
      have hji' :
          inlFin (n := n) (m := m) j ≠ inrFin (n := n) (m := m) i' := by
        exact inlFin_ne_inrFin (n := n) (m := m) j i'
      simpa [σi] using
        (Equiv.swap_apply_of_ne_of_ne (a := inlFin (n := n) (m := m) i)
          (b := inrFin (n := n) (m := m) i') (x := inlFin (n := n) (m := m) j) hji hji')
    -- Rewrite with the permutation invariance.
    simpa [hpComb_perm_i, hqComb_perm_i, hσi_i, hσi_j] using hperm

  have hL2 :
      Classical.choose (hDiff.deriv_exists pComb qComb
        (inrFin (n := n) (m := m) i') (inlFin (n := n) (m := m) j) h_inr_inl hpComb hqComb) =
      Classical.choose (hDiff.deriv_exists pComb qComb
        (inrFin (n := n) (m := m) i') (inrFin (n := n) (m := m) j') hi'j'_inr hpComb hqComb) := by
    have hperm :=
      hPermDeriv (σ := σj) (p := pComb) (q := qComb)
        (i := inrFin (n := n) (m := m) i') (j := inlFin (n := n) (m := m) j)
        (hij := h_inr_inl) (hp := hpComb) (hq := hqComb)
    have hσj_i :
        σj (inrFin (n := n) (m := m) i') = inrFin (n := n) (m := m) i' := by
      have hia :
          inrFin (n := n) (m := m) i' ≠ inlFin (n := n) (m := m) j := by
        intro h
        exact (inlFin_ne_inrFin (n := n) (m := m) j i') h.symm
      have hib :
          inrFin (n := n) (m := m) i' ≠ inrFin (n := n) (m := m) j' := by
        intro h
        exact hi'j' ((inrFin_eq_inrFin (n := n) (m := m)).1 h)
      simpa [σj] using
        (Equiv.swap_apply_of_ne_of_ne (a := inlFin (n := n) (m := m) j)
          (b := inrFin (n := n) (m := m) j') (x := inrFin (n := n) (m := m) i') hia hib)
    have hσj_j :
        σj (inlFin (n := n) (m := m) j) = inrFin (n := n) (m := m) j' := by
      simp [σj]
    simpa [hpComb_perm_j, hqComb_perm_j, hσj_i, hσj_j] using hperm

  have hLcomb :
      Classical.choose (hDiff.deriv_exists pComb qComb
        (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j) hij_inl hpComb hqComb) =
      Classical.choose (hDiff.deriv_exists pComb qComb
        (inrFin (n := n) (m := m) i') (inrFin (n := n) (m := m) j') hi'j'_inr hpComb hqComb) :=
    hL1.trans hL2

  -- Step 3b: two-block transport transfers combined derivatives back to the original systems.
  have hTransport_left' :
      Classical.choose (hDiff.deriv_exists pComb
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q')
        (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j) hij_inl
        (by
          intro k
          simpa [pComb] using hpComb k)
        (by
          intro k
          simpa [hCombEq] using hqComb k)) =
      Classical.choose (hDiff.deriv_exists p q i j hij hp hq) := by
    simpa [pComb] using
      (hTransport'.left (w := w) (hw0 := hw0) (hw1 := hw1)
        (p := p) (q := q) (p' := p') (q' := q')
        (i := i) (j := j) (hij := hij)
        (hp := hp) (hq := hq)
        (hpComb := by
          intro k
          simpa [pComb] using hpComb k)
        (hqComb := by
          intro k
          simpa [hCombEq] using hqComb k))

  have hTransport_left :
      Classical.choose (hDiff.deriv_exists pComb qComb
        (inlFin (n := n) (m := m) i) (inlFin (n := n) (m := m) j) hij_inl hpComb hqComb) =
      Classical.choose (hDiff.deriv_exists p q i j hij hp hq) := by
    simpa [hCombEq] using hTransport_left'

  have hTransport_right' :
      Classical.choose (hDiff.deriv_exists pComb
        (ProbDist.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) q q')
        (inrFin (n := n) (m := m) i') (inrFin (n := n) (m := m) j') hi'j'_inr
        (by
          intro k
          simpa [pComb] using hpComb k)
        (by
          intro k
          simpa [hCombEq] using hqComb k)) =
      Classical.choose (hDiff.deriv_exists p' q' i' j' hi'j' hp' hq') := by
    simpa [pComb] using
      (hTransport'.right (w := w) (hw0 := hw0) (hw1 := hw1)
        (p := p) (q := q) (p' := p') (q' := q')
        (i' := i') (j' := j') (hi'j' := hi'j')
        (hp' := hp') (hq' := hq')
        (hpComb := by
          intro k
          simpa [pComb] using hpComb k)
        (hqComb := by
          intro k
          simpa [hCombEq] using hqComb k))

  have hTransport_right :
      Classical.choose (hDiff.deriv_exists pComb qComb
        (inrFin (n := n) (m := m) i') (inrFin (n := n) (m := m) j') hi'j'_inr hpComb hqComb) =
      Classical.choose (hDiff.deriv_exists p' q' i' j' hi'j' hp' hq') := by
    simpa [hCombEq] using hTransport_right'

  exact hTransport_left.symm.trans (hLcomb.trans hTransport_right)

theorem sj3_implies_derivLocalAssumption
    (I : InferenceMethod) (F : ObjectiveFunctional)
    (hSJ : ShoreJohnsonAxioms I)
    (hRealize : RealizesEV I F)
    (hReg : TheoremIRegularity F)
    (hPerm : ObjectivePermuteInvariant F)
    (hRatio :
      _root_.Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.GradientSeparability.DerivRatioInvariant
        F ⟨hReg.has_shift2_deriv⟩) :
    DerivLocalAssumption F ⟨hReg.has_shift2_deriv⟩ := by
  have hTransport :
      DerivTwoBlockTransport F ⟨hReg.has_shift2_deriv⟩ :=
    derivTwoBlockTransport_of_ratio F ⟨hReg.has_shift2_deriv⟩ hRatio
  intro n m p q p' q' i j i' j' hij hi'j' hp hq hp' hq' hMin hMin' h_qi h_pi h_qj h_pj
  exact
    (sj3_implies_derivLocalAssumption_of_transport
      (I := I) (F := F) (hSJ := hSJ) (hRealize := hRealize)
      (hReg := hReg) (hPerm := hPerm) (hTransport := hTransport)
      (p := p) (q := q) (p' := p') (q' := q')
      (i := i) (j := j) (i' := i') (j' := j')
      (hij := hij) (hi'j' := hi'j')
      (hp := hp) (hq := hq) (hp' := hp') (hq' := hq')
      hMin hMin' h_qi h_pi h_qj h_pj)

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.SJ3Locality
