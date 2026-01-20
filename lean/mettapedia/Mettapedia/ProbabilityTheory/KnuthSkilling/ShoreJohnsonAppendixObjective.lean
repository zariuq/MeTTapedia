import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendix
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonObjective

/-!
# Shore–Johnson Appendix: objective-level calculus helpers

This file connects the coordinate-shift calculus (`ShoreJohnsonAppendix.lean`) to the
sum-of-atoms objective `ofAtom d`.  It provides clean “partial-derivative equality” lemmas
that will be used in the Shore–Johnson Appendix proof of the separable sum form.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendixObjective

open Mettapedia.ProbabilityTheory.KnuthSkilling.InformationEntropy
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendix
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonObjective

/-- `ofAtom d` is a coordinate-wise sum with `φ_i(x) = d(x, p_i)`. -/
theorem ofAtom_eq_sumObjectiveCoord {n : ℕ} (d : ℝ → ℝ → ℝ)
    (p q : ProbDist n) :
    (ofAtom d).D q p =
      sumObjectiveCoord (fun i : Fin n => fun x => d x (p.p i)) q.p := by
  simp [ofAtom, sumObjectiveCoord]

theorem hasDerivAt_ofAtom_shift2_coord {n : ℕ}
    (d : ℝ → ℝ → ℝ) (p : ProbDist n) (q : ProbDist n)
    (i j : Fin n) (t : ℝ) (hij : i ≠ j)
    (d'i d'j : ℝ)
    (hdi : HasDerivAt (fun x => d x (p.p i)) d'i t)
    (hdj : HasDerivAt (fun x => d x (p.p j)) d'j (q.p i + q.p j - t)) :
    HasDerivAt (fun u =>
      sumObjectiveCoord (fun k : Fin n => fun x => d x (p.p k)) (shift2 q.p i j u))
      (d'i - d'j) t := by
  exact hasDerivAt_sumObjectiveCoord_shift2
    (φ := fun k : Fin n => fun x => d x (p.p k))
    (q := q.p) (i := i) (j := j) (t := t) hij d'i d'j hdi hdj

theorem shift2_critical_eq_ofAtom {n : ℕ}
    (d : ℝ → ℝ → ℝ) (p : ProbDist n) (q : ProbDist n)
    (i j : Fin n) (hij : i ≠ j)
    (d'i d'j : ℝ)
    (hdi : HasDerivAt (fun x => d x (p.p i)) d'i (q.p i))
    (hdj : HasDerivAt (fun x => d x (p.p j)) d'j (q.p j))
    (hcrit : HasDerivAt (fun u => sumObjectiveCoord
        (fun i : Fin n => fun x => d x (p.p i)) (shift2 q.p i j u)) 0 (q.p i)) :
    d'i = d'j := by
  exact shift2_critical_eq_coord
    (φ := fun i : Fin n => fun x => d x (p.p i))
    (q := q.p) (i := i) (j := j) hij d'i d'j hdi hdj hcrit

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendixObjective
