import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Appendix
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Objective

/-!
# Shore–Johnson Appendix: minimizer calculus along `shift2`

This file contains a small, **Lean-friendly** calculus lemma used in the Shore–Johnson Appendix A
derivation:

If `q` minimizes an objective over a constraint set, and if a `shift2` curve stays inside the
constraint set (e.g. because all constraint coefficients agree on the shifted coordinates), then
the objective restricted to that curve has a local minimum at `t = q_i`. Hence, whenever the
1D derivative exists there, it must be `0` (Fermat's theorem).

This is a building block for the Shore–Johnson Theorem I proof (see `TheoremI.lean`).
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.AppendixMinimizer

open Classical

open Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Appendix
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Constraints
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Objective

/-! ## A totalized `shift2Prob` curve via clamping -/

noncomputable def shift2Clamp {n : ℕ} (q : ProbDist n) (i j : Fin n) (t : ℝ) : ℝ :=
  max 0 (min t (q.p i + q.p j))

theorem shift2Clamp_eq_of_mem {n : ℕ} (q : ProbDist n) (i j : Fin n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ q.p i + q.p j) :
    shift2Clamp q i j t = t := by
  dsimp [shift2Clamp]
  have hmin : min t (q.p i + q.p j) = t := min_eq_left ht1
  -- `max 0 t = t` since `0 ≤ t`.
  simp [hmin, max_eq_right ht0]

/-- A `shift2Prob` curve defined for all `t : ℝ` by clamping to the valid interval. -/
noncomputable def shift2ProbClamp {n : ℕ} (q : ProbDist n) (i j : Fin n) (hij : i ≠ j) (t : ℝ) :
    ProbDist n :=
  let t' := shift2Clamp q i j t
  have ht0 : 0 ≤ t' := by
    dsimp [t', shift2Clamp]
    exact le_max_left _ _
  have ht1 : t' ≤ q.p i + q.p j := by
    dsimp [t', shift2Clamp]
    refine max_le ?_ (min_le_right _ _)
    exact add_nonneg (q.nonneg i) (q.nonneg j)
  shift2Prob q i j hij t' ht0 ht1

theorem shift2ProbClamp_apply {n : ℕ} (q : ProbDist n) (i j k : Fin n) (hij : i ≠ j) (t : ℝ) :
    (shift2ProbClamp q i j hij t).p k = shift2 q.p i j (shift2Clamp q i j t) k := by
  -- `shift2ProbClamp` is `shift2Prob` at the clamped parameter.
  classical
  dsimp [shift2ProbClamp]
  simp [shift2Prob]

/-! ## Symmetry under index swap -/

/-- The shift2Clamp function is symmetric in the sum: clamp ranges are equal. -/
theorem shift2Clamp_sum_comm {n : ℕ} (q : ProbDist n) (i j : Fin n) :
    q.p i + q.p j = q.p j + q.p i := add_comm _ _

/-- For t in the valid range, shift2ProbClamp is symmetric under index swap with reflected parameter. -/
theorem shift2ProbClamp_swap {n : ℕ} (q : ProbDist n) (i j : Fin n) (hij : i ≠ j)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ q.p i + q.p j) :
    shift2ProbClamp q i j hij t = shift2ProbClamp q j i hij.symm (q.p i + q.p j - t) := by
  -- Both sides use shift2 with parameters that satisfy the swap identity
  apply ProbDist.ext
  intro k
  -- For t in range, shift2Clamp q i j t = t
  have hclamp_ij : shift2Clamp q i j t = t := shift2Clamp_eq_of_mem q i j t ht0 ht1
  -- For (q_i + q_j - t) in range [0, q_i + q_j], shift2Clamp equals identity
  have ht0' : 0 ≤ q.p i + q.p j - t := by linarith
  have ht1' : q.p i + q.p j - t ≤ q.p j + q.p i := by linarith
  have hclamp_ji : shift2Clamp q j i (q.p i + q.p j - t) = q.p i + q.p j - t :=
    shift2Clamp_eq_of_mem q j i (q.p i + q.p j - t) ht0' ht1'
  -- Now use the shift2_swap identity from Appendix
  simp only [shift2ProbClamp_apply, hclamp_ij, hclamp_ji]
  exact congr_fun (shift2_swap q.p i j t hij) k

/-- The curve value at t = q_i is symmetric: both shift2ProbClamp curves pass through q. -/
theorem shift2ProbClamp_at_qi_eq_q {n : ℕ} (q : ProbDist n) (i j : Fin n) (hij : i ≠ j) :
    shift2ProbClamp q i j hij (q.p i) = q := by
  apply ProbDist.ext
  intro k
  have ht0 : 0 ≤ q.p i := q.nonneg i
  have ht1 : q.p i ≤ q.p i + q.p j := by linarith [q.nonneg j]
  have hclamp : shift2Clamp q i j (q.p i) = q.p i := shift2Clamp_eq_of_mem q i j (q.p i) ht0 ht1
  simp only [shift2ProbClamp_apply, hclamp]
  exact congr_fun (shift2_self q.p i j hij) k

/-! ## Compatibility with permutations -/

theorem shift2Clamp_permute {n : ℕ} (σ : Equiv.Perm (Fin n)) (q : ProbDist n) (i j : Fin n)
    (t : ℝ) :
    shift2Clamp (Inference.ProbDist.permute σ q) (σ i) (σ j) t = shift2Clamp q i j t := by
  -- Both clamps depend only on `t` and the sum `q_i + q_j`, which is permutation-invariant.
  dsimp [shift2Clamp, Inference.ProbDist.permute]
  simp

theorem permute_shift2ProbClamp {n : ℕ} (σ : Equiv.Perm (Fin n)) (q : ProbDist n)
    (i j : Fin n) (hij : i ≠ j) (t : ℝ) :
    Inference.ProbDist.permute σ (shift2ProbClamp q i j hij t) =
      shift2ProbClamp (Inference.ProbDist.permute σ q) (σ i) (σ j)
        (σ.injective.ne_iff.mpr hij) t := by
  classical
  apply ProbDist.ext
  intro k
  -- Unfold both sides to `shift2` on coordinate functions.
  simp only [Inference.ProbDist.permute_apply, shift2ProbClamp_apply]
  -- The clamped parameter is invariant under permutation.
  have hclamp :
      shift2Clamp (Inference.ProbDist.permute σ q) (σ i) (σ j) t =
        shift2Clamp q i j t :=
    shift2Clamp_permute (σ := σ) (q := q) (i := i) (j := j) (t := t)
  -- Now split cases on whether `k` hits the shifted coordinates.
  by_cases hki : k = σ i
  · subst hki
    simp [shift2, hclamp]
  · by_cases hkj : k = σ j
    · subst hkj
      have hji : j ≠ i := by
        simpa using hij.symm
      simp [shift2, hclamp, hji, Inference.ProbDist.permute_apply]
    · -- Otherwise, it's an "other" coordinate.
      have hk_i : σ⁻¹ k ≠ i := by
        intro hk
        apply hki
        simpa using congrArg σ hk
      have hk_j : σ⁻¹ k ≠ j := by
        intro hk
        apply hkj
        simpa using congrArg σ hk
      simp [shift2, hki, hkj, hk_i, hk_j, Inference.ProbDist.permute_apply]

/-! ## Constraint preservation for expected-value constraints -/

theorem satisfies_shift2ProbClamp_of_coeff_eq {n : ℕ}
    (c : EVConstraint n) (q : ProbDist n) (i j : Fin n) (hij : i ≠ j) (t : ℝ)
    (hcoeff : c.coeff i = c.coeff j) :
    satisfies c (shift2ProbClamp q i j hij t) ↔ satisfies c q := by
  -- Reduce to the vector-level lemma `satisfiesFn_shift2_of_coeff_eq`.
  simpa [satisfies, satisfiesFn, shift2ProbClamp_apply] using
    (satisfiesFn_shift2_of_coeff_eq (c := c) (q := q.p) (i := i) (j := j)
      (t := shift2Clamp q i j t) hij hcoeff)

theorem satisfiesSet_shift2ProbClamp_of_coeff_eq {n : ℕ}
    (cs : EVConstraintSet n) (q : ProbDist n) (i j : Fin n) (hij : i ≠ j) (t : ℝ)
    (hcoeff : ∀ c ∈ cs, c.coeff i = c.coeff j) :
    satisfiesSet cs (shift2ProbClamp q i j hij t) ↔ satisfiesSet cs q := by
  constructor
  · intro h c hc
    have := h c hc
    exact (satisfies_shift2ProbClamp_of_coeff_eq (c := c) (q := q) (i := i) (j := j) (hij := hij)
      (t := t) (hcoeff := hcoeff c hc)).1 this
  · intro h c hc
    have := h c hc
    exact (satisfies_shift2ProbClamp_of_coeff_eq (c := c) (q := q) (i := i) (j := j) (hij := hij)
      (t := t) (hcoeff := hcoeff c hc)).2 this

/-! ## Fermat along feasible `shift2` directions -/

theorem hasDerivAt_D_eq_zero_of_isMinimizer_shift2ProbClamp
    {n : ℕ} (F : ObjectiveFunctional) (p q : ProbDist n) (cs : EVConstraintSet n)
    (hq : IsMinimizer F p (toConstraintSet cs) q)
    (i j : Fin n) (hij : i ≠ j)
    (hcoeff : ∀ c ∈ cs, c.coeff i = c.coeff j)
    (r : ℝ)
    (hDeriv : HasDerivAt (fun t : ℝ => F.D (shift2ProbClamp q i j hij t) p) r (q.p i)) :
    r = 0 := by
  -- The curve stays in the constraint set for all `t`.
  have hmem : ∀ t : ℝ, shift2ProbClamp q i j hij t ∈ toConstraintSet cs := by
    intro t
    -- membership is `satisfiesSet`.
    have : satisfiesSet cs (shift2ProbClamp q i j hij t) ↔ satisfiesSet cs q :=
      satisfiesSet_shift2ProbClamp_of_coeff_eq (cs := cs) (q := q) (i := i) (j := j)
        (hij := hij) (t := t) hcoeff
    have hq_mem : satisfiesSet cs q := by
      exact hq.1
    exact (mem_toConstraintSet cs _).2 ((this.2 hq_mem))
  -- The curve passes through `q` at `t = q.p i`.
  have hcurve0 : shift2ProbClamp q i j hij (q.p i) = q := by
    apply ProbDist.ext
    intro k
    have ht0 : 0 ≤ q.p i := q.nonneg i
    have ht1 : q.p i ≤ q.p i + q.p j := by linarith [q.nonneg j]
    have hclamp : shift2Clamp q i j (q.p i) = q.p i :=
      shift2Clamp_eq_of_mem (q := q) (i := i) (j := j) (t := q.p i) ht0 ht1
    by_cases hki : k = i
    · subst hki
      simp [shift2ProbClamp_apply, hclamp, shift2_apply_i]
    · by_cases hkj : k = j
      · subst hkj
        simp [shift2ProbClamp_apply, hclamp, shift2_apply_j, hij]
      · simp [shift2ProbClamp_apply, hclamp, shift2_apply_other, hki, hkj]
  -- Hence the objective along the curve has a (global, hence local) minimum at `t = q_i`.
  have hloc : IsLocalMin (fun t : ℝ => F.D (shift2ProbClamp q i j hij t) p) (q.p i) := by
    refine (Filter.Eventually.of_forall ?_)
    intro t
    have ht_mem : shift2ProbClamp q i j hij t ∈ toConstraintSet cs := hmem t
    have ht_le := hq.2 (shift2ProbClamp q i j hij t) ht_mem
    simpa [hcurve0] using ht_le
  -- Fermat.
  exact hloc.hasDerivAt_eq_zero hDeriv

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.AppendixMinimizer
