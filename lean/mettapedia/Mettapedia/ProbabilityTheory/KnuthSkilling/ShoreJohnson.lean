import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonProof

/-!
# Shore–Johnson core lemma (1980): system independence ⇒ log on probabilities

This file exports a small but central piece of Shore–Johnson’s 1980 argument:

If an “atomic divergence” `d : ℝ → ℝ → ℝ` is

- **regular at 0** (`d 0 x = 0`), and
- **system independent** in the sense that the sum `∑ d(p_i,q_i)` is additive over product
  distributions,

then Dirac-delta test distributions force a **multiplicative Cauchy equation** for
`g(q) := d 1 q` on the probability domain `0 < q ≤ 1`.  With a minimal regularity gate
(Borel measurability of `g`), we obtain the logarithmic form `g(q) = C * log q`.

This is the clean point of contact with Knuth–Skilling Appendix C: both derivations reduce to
Cauchy-type functional equations, and both require an explicit “anti-pathology” regularity gate
to exclude Hamel-basis solutions.

We do **not** attempt a full formalization of Shore–Johnson Theorem 1 (global KL uniqueness) here.

For a stronger (but still explicitly-scoped) KL uniqueness statement—showing that any **ratio-form**
atom divergence `d(w,u)=w*g(w/u)` satisfying a multiplicative Cauchy equation is a constant multiple
of the KL atom (with a measurability regularity gate), and that uniqueness fails without such
regularity—see `Mettapedia/ProbabilityTheory/KnuthSkilling/ShoreJohnsonKL.lean`.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson

open Real

open Mettapedia.ProbabilityTheory.KnuthSkilling.InformationEntropy
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonProof
open Mettapedia.ProbabilityTheory.KnuthSkilling.VariationalTheorem

/-- Shore–Johnson’s “system independence” axiom, phrased at the atomic (summand) level. -/
structure SJSystemIndependenceAtom (d : ℝ → ℝ → ℝ) : Prop where
  regularAtom : RegularAtom d
  add_over_products :
    ∀ {n m : ℕ} [NeZero n] [NeZero m], ∀ P Q : ProbDist n, ∀ R S : ProbDist m,
      ∑ ij : Fin n × Fin m, d ((P ⊗ R).p ij) ((Q ⊗ S).p ij) =
        (∑ i : Fin n, d (P.p i) (Q.p i)) + (∑ j : Fin m, d (R.p j) (S.p j))

/-- **Main Shore–Johnson lemma used in this project**.

Under atomic system independence and measurability, `q ↦ d(1,q)` is forced to be logarithmic on
the probability domain `0 < q ≤ 1`. -/
theorem d_one_eq_const_mul_log_of_measurable
    (d : ℝ → ℝ → ℝ) (hSJ : SJSystemIndependenceAtom d)
    (hMeas : Measurable (d 1)) :
    ∃ C : ℝ, ∀ q : ℝ, 0 < q → q ≤ 1 → d 1 q = C * log q :=
  dirac_extraction_log_of_measurable d hSJ.regularAtom hSJ.add_over_products hMeas

/-- Repackage the log conclusion as a KS-style `entropyDerivative` (with `B = 0`). -/
theorem d_one_eq_entropyDerivative_of_measurable
    (d : ℝ → ℝ → ℝ) (hSJ : SJSystemIndependenceAtom d)
    (hMeas : Measurable (d 1)) :
    ∃ C : ℝ, ∀ q : ℝ, 0 < q → q ≤ 1 → d 1 q = entropyDerivative 0 C q := by
  rcases d_one_eq_const_mul_log_of_measurable d hSJ hMeas with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro q hq_pos hq_le1
  simpa [entropyDerivative] using hC q hq_pos hq_le1

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson
