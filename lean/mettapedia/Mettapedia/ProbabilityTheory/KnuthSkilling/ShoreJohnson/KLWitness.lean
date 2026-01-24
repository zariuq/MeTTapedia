import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.GradientSeparability
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.AppendixKL

/-!
# KL witness for ratio-invariance

This file provides a concrete witness that the KL atom objective satisfies the
ratio-invariant derivative axiom used in the SJ3 → locality step.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.KLWitness

open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Objective
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.KL

open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.AppendixKL.KLStationary
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.GradientSeparability

/-- First-argument derivative of `klAtom` in the positive regime. -/
noncomputable def klAtomDeriv (q p : ℝ) : ℝ :=
  Real.log (q / p) + 1

lemma hasDerivAt_klAtom_pos (q p : ℝ) (hq : 0 < q) (hp : 0 < p) :
    HasDerivAt (fun t => klAtom t p) (klAtomDeriv q p) q := by
  simpa [klAtomDeriv] using (hasDerivAt_klAtom q p hq hp)

lemma klAtomDeriv_ratio (q p q' p' : ℝ) (h : q / p = q' / p') :
    klAtomDeriv q p = klAtomDeriv q' p' := by
  simp [klAtomDeriv, h]

/-- KL atom objective satisfies ratio-invariant derivatives. -/
theorem derivRatioInvariant_klAtom :
    DerivRatioInvariant (ofAtom klAtom)
      ⟨(ExtractGRegularity.ofAtom klAtom klAtomDeriv hasDerivAt_klAtom_pos).has_shift2_deriv⟩ := by
  exact derivRatioInvariant_ofAtom klAtom klAtomDeriv hasDerivAt_klAtom_pos klAtomDeriv_ratio

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.KLWitness
