import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonAppendixMinimizer
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonAppendixObjective
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.ShoreJohnsonObjective

/-!
# Shore–Johnson Appendix (Theorem I): explicit regularity/richness bridge

This file packages a **Lean-friendly** assumption bundle capturing the regularity/richness
requirements used in Shore–Johnson’s Appendix argument (Theorem I).

The goal is to derive the **sum-form objective equivalence**:

`ObjEquivEV F (ofAtom d)`

without smuggling it as a bare axiom.  We instead assume an explicit *stationarity criterion*
and a *shift2-derivative representation* that mirror the Appendix calculus.

This keeps the dependency surface honest while remaining workable in Lean.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendixTheoremI

open Classical

open Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendixMinimizer
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonConstraints
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonObjective

/-! ## Pairwise coefficient equality and stationarity condition -/

def PairwiseCoeffEq {n : ℕ} (cs : EVConstraintSet n) (i j : Fin n) : Prop :=
  ∀ c ∈ cs, c.coeff i = c.coeff j

def GEqualOnCoeffs {n : ℕ} (g : ℝ → ℝ → ℝ) (p q : ProbDist n) (cs : EVConstraintSet n) : Prop :=
  ∀ i j : Fin n, i ≠ j → PairwiseCoeffEq cs i j →
    g (q.p i) (p.p i) = g (q.p j) (p.p j)

/-!
`StationaryEV` is a Lean-friendly first-order condition for expected-value constraints:
there exist Lagrange multipliers such that the coordinate kernel `g(q_i,p_i)` is affine in the
constraint coefficient vectors.

This is the correct replacement for “all feasible shift2 derivatives vanish”, which is too weak
to characterize minimizers for general expected-value constraints.
-/

def StationaryEV {n : ℕ} (g : ℝ → ℝ → ℝ) (p q : ProbDist n) (cs : EVConstraintSet n) : Prop :=
  ∃ (β : ℝ) (lam : Fin cs.length → ℝ),
    ∀ i : Fin n, g (q.p i) (p.p i) = β + ∑ k : Fin cs.length, (lam k) * (cs.get k).coeff i

theorem gEqualOnCoeffs_of_stationaryEV {n : ℕ}
    {g : ℝ → ℝ → ℝ} {p q : ProbDist n} {cs : EVConstraintSet n}
    (h : StationaryEV g p q cs) :
    GEqualOnCoeffs g p q cs := by
  rcases h with ⟨β, lam, hβ⟩
  intro i j hij hcoeff
  have hi := hβ i
  have hj := hβ j
  -- The constraint sums agree since every coefficient agrees on `i` and `j`.
  have hsum :
      (∑ k : Fin cs.length, lam k * (cs.get k).coeff i) =
        ∑ k : Fin cs.length, lam k * (cs.get k).coeff j := by
    refine Finset.sum_congr rfl ?_
    intro k _
    have hk : (cs.get k).coeff i = (cs.get k).coeff j := by
      -- `List.get` always yields an element of the list.
      exact hcoeff (cs.get k) (List.get_mem cs k)
    -- Rewrite the `i` coefficient to the `j` coefficient.
    rw [hk]
  -- Transport the equality through the `β + sum` representations.
  calc
    g (q.p i) (p.p i) = β + (∑ k : Fin cs.length, lam k * (cs.get k).coeff i) := hi
    _ = β + (∑ k : Fin cs.length, lam k * (cs.get k).coeff j) := by rw [hsum]
    _ = g (q.p j) (p.p j) := hj.symm

/-! ## Appendix-style regularity/richness assumptions -/

structure SJAppendixAssumptions (F : ObjectiveFunctional) (d : ℝ → ℝ → ℝ) where
  /-- Coordinate kernel in the Appendix-style gradient representation. -/
  g : ℝ → ℝ → ℝ
  /-- (Optional bookkeeping) a scalar multiplier depending on `(p,q)` but not on coordinates,
  matching Shore–Johnson’s projected-gradient discussion. -/
  scale : ∀ {n : ℕ}, ProbDist n → ProbDist n → ℝ
  /-- The multiplier is never zero (so it can be cancelled). -/
  scale_ne : ∀ {n : ℕ} (p q : ProbDist n), scale p q ≠ 0
  /-- Shift2 derivative for the objective `F` (Appendix A1, *difference* form). -/
  F_shift2_deriv :
    ∀ {n : ℕ} (p q : ProbDist n) (i j : Fin n) (hij : i ≠ j),
      HasDerivAt (fun t => F.D (shift2ProbClamp q i j hij t) p)
        (scale p q * (g (q.p i) (p.p i) - g (q.p j) (p.p j))) (q.p i)
  /-- Regularity/richness axiom: for expected-value constraint sets, first-order stationarity
  is equivalent to being a minimizer of `F`. -/
  stationary_iff_isMinimizer_F :
    ∀ {n : ℕ} (p : ProbDist n) (_hp : ∀ i, 0 < p.p i)
      (cs : EVConstraintSet n) (q : ProbDist n),
      q ∈ toConstraintSet cs →
      (∀ i, 0 < q.p i) →
        (StationaryEV g p q cs ↔ IsMinimizer F p (toConstraintSet cs) q)
  /-- Same stationarity characterization for the sum-form objective `ofAtom d`. -/
  stationary_iff_isMinimizer_ofAtom :
    ∀ {n : ℕ} (p : ProbDist n) (_hp : ∀ i, 0 < p.p i)
      (cs : EVConstraintSet n) (q : ProbDist n),
      q ∈ toConstraintSet cs →
      (∀ i, 0 < q.p i) →
        (StationaryEV g p q cs ↔ IsMinimizer (ofAtom d) p (toConstraintSet cs) q)

/-! ## From Appendix shift2 calculus to equal-coordinate kernels -/

theorem gEqualOnCoeffs_of_isMinimizer_F {F : ObjectiveFunctional} {d : ℝ → ℝ → ℝ}
    (h : SJAppendixAssumptions F d) {n : ℕ} (p q : ProbDist n) (cs : EVConstraintSet n)
    (hq : IsMinimizer F p (toConstraintSet cs) q) {i j : Fin n} (hij : i ≠ j)
    (hcoeff : PairwiseCoeffEq cs i j) :
    h.g (q.p i) (p.p i) = h.g (q.p j) (p.p j) := by
  -- Apply Fermat along the feasible `shift2ProbClamp` curve.
  have hDeriv :=
    h.F_shift2_deriv (p := p) (q := q) (i := i) (j := j) hij
  have hzero :
      h.scale p q * (h.g (q.p i) (p.p i) - h.g (q.p j) (p.p j)) = 0 := by
    exact
      hasDerivAt_D_eq_zero_of_isMinimizer_shift2ProbClamp
        (F := F) (p := p) (q := q) (cs := cs) hq (i := i) (j := j) hij hcoeff
        (r := h.scale p q * (h.g (q.p i) (p.p i) - h.g (q.p j) (p.p j))) hDeriv
  -- Cancel the nonzero scale factor.
  have hsub :
      h.g (q.p i) (p.p i) - h.g (q.p j) (p.p j) = 0 := by
    rcases mul_eq_zero.1 hzero with hscale0 | hdiff
    · exact False.elim (h.scale_ne p q hscale0)
    · exact hdiff
  exact sub_eq_zero.1 hsub

/-! ## Consequences: `F` and `ofAtom d` agree on *positive* minimizers -/

theorem isMinimizer_iff_isMinimizer_ofAtom_of_pos
    {F : ObjectiveFunctional} {d : ℝ → ℝ → ℝ} (h : SJAppendixAssumptions F d)
    {n : ℕ} (p : ProbDist n) (hp : ∀ i, 0 < p.p i)
    (cs : EVConstraintSet n) (q : ProbDist n)
    (hq : q ∈ toConstraintSet cs) (hqPos : ∀ i, 0 < q.p i) :
    IsMinimizer F p (toConstraintSet cs) q ↔ IsMinimizer (ofAtom d) p (toConstraintSet cs) q := by
  have hF : StationaryEV h.g p q cs ↔ IsMinimizer F p (toConstraintSet cs) q :=
    h.stationary_iff_isMinimizer_F (p := p) hp (cs := cs) (q := q) hq hqPos
  have hAtom : StationaryEV h.g p q cs ↔ IsMinimizer (ofAtom d) p (toConstraintSet cs) q :=
    h.stationary_iff_isMinimizer_ofAtom (p := p) hp (cs := cs) (q := q) hq hqPos
  exact hF.symm.trans hAtom

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendixTheoremI
