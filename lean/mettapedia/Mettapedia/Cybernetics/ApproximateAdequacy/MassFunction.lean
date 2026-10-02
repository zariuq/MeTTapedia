import Mettapedia.Cybernetics.ApproximateAdequacy.CouplingBound
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite distributions and Mathlib's probability mass functions

The chains of this development carry distributions valued in an ordered
field, so that couplings can subtract and certificates can be checked in
`ℚ`.  Over `ℝ` they are exactly Mathlib's probability mass functions on a
finite type.

* A real finite distribution is a `PMF` (`IsDistribution.toPMF`) with the same
  point masses (`IsDistribution.toReal_toPMF`) and the same support
  (`IsDistribution.support_toPMF`).
* A `PMF` on a finite type is a real finite distribution
  (`isDistribution_toReal`), and the two passages are inverse
  (`IsDistribution.toPMF_toReal`, `toReal_toPMF_eq`).
* The successor distributions of a real chain are `PMF`s
  (`LabelledMarkovChain.kernel`), and the support transitions used by
  approximate bisimulation are membership in their supports
  (`LabelledMarkovChain.supportStep_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open scoped ENNReal

variable {S : Type*} [Fintype S] {μ : S → ℝ}

/-- **A real finite distribution as a probability mass function.** -/
noncomputable def IsDistribution.toPMF (distribution : IsDistribution μ) : PMF S :=
  PMF.ofFintype (fun x => ENNReal.ofReal (μ x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => distribution.nonneg x,
      distribution.sum_eq_one, ENNReal.ofReal_one])

theorem IsDistribution.toPMF_apply (distribution : IsDistribution μ) (x : S) :
    distribution.toPMF x = ENNReal.ofReal (μ x) :=
  rfl

theorem IsDistribution.toReal_toPMF (distribution : IsDistribution μ) (x : S) :
    (distribution.toPMF x).toReal = μ x :=
  ENNReal.toReal_ofReal (distribution.nonneg x)

theorem IsDistribution.support_toPMF (distribution : IsDistribution μ) :
    distribution.toPMF.support = {x | μ x ≠ 0} := by
  ext x
  rw [PMF.mem_support_iff, distribution.toPMF_apply, Set.mem_ofPred_eq, ne_eq, ne_eq,
    ENNReal.ofReal_eq_zero, not_le]
  exact ⟨fun positive => positive.ne', fun nonzero => lt_of_le_of_ne (distribution.nonneg x)
    (Ne.symm nonzero)⟩

/-- **A probability mass function on a finite type is a real finite
distribution.** -/
theorem isDistribution_toReal (p : PMF S) : IsDistribution fun x => (p x).toReal where
  nonneg _ := ENNReal.toReal_nonneg
  sum_eq_one := by
    have total : ∑ x, p x = 1 := by
      rw [← tsum_fintype (L := .unconditional S)]
      exact p.tsum_coe
    rw [← ENNReal.toReal_sum fun x _ => p.apply_ne_top x, total, ENNReal.toReal_one]

theorem IsDistribution.toPMF_toReal (p : PMF S) : (isDistribution_toReal p).toPMF = p := by
  ext x
  rw [IsDistribution.toPMF_apply, ENNReal.ofReal_toReal (p.apply_ne_top x)]

theorem toReal_toPMF_eq (distribution : IsDistribution μ) :
    (fun x => (distribution.toPMF x).toReal) = μ :=
  funext distribution.toReal_toPMF

variable {A Atom : Type*}

/-- **The successor distributions of a real chain, as probability mass
functions.** -/
noncomputable def LabelledMarkovChain.kernel (P : LabelledMarkovChain ℝ A Atom S) (a : A)
    (s : S) : PMF S :=
  (P.isDistribution a s).toPMF

/-- **Support transitions are membership in the support of the kernel.** -/
theorem LabelledMarkovChain.supportStep_iff (P : LabelledMarkovChain ℝ A Atom S) (a : A)
    (s x : S) : P.supportStep a s x ↔ x ∈ (P.kernel a s).support := by
  rw [LabelledMarkovChain.kernel, IsDistribution.support_toPMF]
  exact Iff.rfl

end Mettapedia.Cybernetics.ApproximateAdequacy
