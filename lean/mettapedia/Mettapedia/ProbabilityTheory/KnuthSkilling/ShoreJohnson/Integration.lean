import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.GradientSeparability

/-!
# Integration step (scaffolding)

This file packages the **analytic integration step** from Appendix A:
given a gradient representation `g`, produce an atom divergence `d` such that
`F(q,p) = ∑ d(q_i, p_i) + const(p)`, hence `F` is objective-equivalent to `ofAtom d`.

The actual construction of `d` from `g` is the remaining analytic task; here we
record the exact assumptions needed and the objective-equivalence consequence.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Integration

open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Objective
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.GradientSeparability
open Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy

/-- **Integration assumptions**: a candidate atom `d` whose derivative matches the
gradient kernel `g`, together with a constant shift term independent of `q`. -/
structure IntegrationAssumptions (F : ObjectiveFunctional) (gr : GradientRepresentation F) where
  d : ℝ → ℝ → ℝ
  d_deriv :
    ∀ q p : ℝ, 0 < q → 0 < p → HasDerivAt (fun t => d t p) (gr.g q p) q
  const : ∀ {n : ℕ}, ProbDist n → ℝ
  F_eq :
    ∀ {n : ℕ} (p q : ProbDist n),
      F.D q p = (∑ i : Fin n, d (q.p i) (p.p i)) + const p

/-- From the integration assumptions we obtain objective equivalence to an atom-sum objective. -/
theorem objEquiv_of_integrationAssumptions
    (F : ObjectiveFunctional) (gr : GradientRepresentation F)
    (h : IntegrationAssumptions F gr) :
    ObjEquiv F (ofAtom h.d) := by
  intro n p C
  ext q
  constructor
  · intro hq
    refine ⟨hq.1, ?_⟩
    intro q' hq'
    have hle := hq.2 q' hq'
    have hle' :
        (∑ i : Fin n, h.d (q.p i) (p.p i)) + h.const p ≤
          (∑ i : Fin n, h.d (q'.p i) (p.p i)) + h.const p := by
      simpa [h.F_eq (p := p) (q := q), h.F_eq (p := p) (q := q')] using hle
    have hle'' :
        (∑ i : Fin n, h.d (q.p i) (p.p i)) ≤
          (∑ i : Fin n, h.d (q'.p i) (p.p i)) :=
      (add_le_add_iff_right (h.const p)).1 hle'
    simpa [ofAtom] using hle''
  · intro hq
    refine ⟨hq.1, ?_⟩
    intro q' hq'
    have hle := hq.2 q' hq'
    have hle' :
        (∑ i : Fin n, h.d (q.p i) (p.p i)) + h.const p ≤
          (∑ i : Fin n, h.d (q'.p i) (p.p i)) + h.const p :=
      by simpa [ofAtom] using hle
    have hle'' :
        F.D q p ≤ F.D q' p := by
      simpa [h.F_eq (p := p) (q := q), h.F_eq (p := p) (q := q')] using hle'
    exact hle''

/-- Integration step packaged as existence of a sum-form objective equivalent to `F`. -/
theorem exists_sumForm_of_integrationAssumptions
    (F : ObjectiveFunctional) (gr : GradientRepresentation F)
    (h : IntegrationAssumptions F gr) :
    ∃ d : ℝ → ℝ → ℝ, ObjEquiv F (ofAtom d) := by
  exact ⟨h.d, objEquiv_of_integrationAssumptions F gr h⟩

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Integration
