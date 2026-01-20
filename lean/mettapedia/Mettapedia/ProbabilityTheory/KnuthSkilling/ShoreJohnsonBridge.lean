import Mettapedia.ProbabilityTheory.KnuthSkilling.InformationEntropy
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonTheorem

/-!
# Shore–Johnson → KL (project glue)

This file packages the **Lean-friendly Shore–Johnson core** already proved in:

- `Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonTheorem`

into a form that is easy to *reuse* in the Knuth–Skilling Appendix C / “Path C” story.

What this file **does**:
* Relates the atom-level KL conclusion (`d = C · klAtom`) to the project’s finite KL divergence
  definition on `ProbDist (Fin n)` from `InformationEntropy.lean`.

What this file **does not** (yet) do:
* Formalize Shore–Johnson’s full operator-level Theorem I appendix proof (SJ1–SJ4 ⇒ objective form).
  That is a significantly larger multivariate-analytic development; we keep our current
  dependency surface honest and explicit.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonBridge

open Classical
open Real
open Finset BigOperators

open Mettapedia.ProbabilityTheory.KnuthSkilling.InformationEntropy
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonKL

/-! ## Finite KL divergence is the sum of KL atoms -/

theorem sum_klAtom_eq_klDivergence {n : ℕ} (P Q : ProbDist n)
    (hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i) :
    (∑ i : Fin n, klAtom (P.p i) (Q.p i)) = klDivergence P Q hQ_pos := by
  simp [klAtom, klDivergence]

/-! ## Transport a Shore–Johnson “atom” characterization to the finite KL formula -/

theorem sum_d_eq_const_mul_klDivergence_of_pos {n : ℕ}
    (d : ℝ → ℝ → ℝ) (C : ℝ)
    (hC : ∀ w u : ℝ, 0 < w → 0 < u → d w u = C * klAtom w u)
    (P Q : ProbDist n)
    (hP_pos : ∀ i, 0 < P.p i)
    (hQ_pos' : ∀ i, 0 < Q.p i) :
    (∑ i : Fin n, d (P.p i) (Q.p i)) = C * klDivergence P Q (fun i _ => hQ_pos' i) := by
  have hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i := fun i _ => hQ_pos' i
  calc
    (∑ i : Fin n, d (P.p i) (Q.p i))
        = ∑ i : Fin n, C * klAtom (P.p i) (Q.p i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            exact hC (P.p i) (Q.p i) (hP_pos i) (hQ_pos' i)
    _ = C * (∑ i : Fin n, klAtom (P.p i) (Q.p i)) := by
          simpa using
            (Finset.mul_sum (s := (Finset.univ : Finset (Fin n))) (a := C)
              (f := fun i : Fin n => klAtom (P.p i) (Q.p i))).symm
    _ = C * klDivergence P Q hQ_pos := by
          simp [sum_klAtom_eq_klDivergence (P := P) (Q := Q) hQ_pos]

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonBridge
