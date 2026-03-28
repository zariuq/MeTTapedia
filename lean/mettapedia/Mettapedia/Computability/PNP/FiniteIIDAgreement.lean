import Mettapedia.Computability.PNP.FiniteConsistencyBound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ENNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# P vs NP background theory: finite weighted agreement mass

This file takes the first step beyond uniform sampling.  Rather than counting
point samples or using only the uniform distribution on a finite input type, we
let one finite probability mass function weight the inputs.

For one predictor `predict` against one target `target`, we define:

* the one-step agreement mass under a `PMF`,
* the mass of a length-`m` sample,
* the total mass of samples on which `predict` agrees with `target`
  everywhere.

The main theorem is exact:

`consistentSampleMass = agreementMass ^ m`.

This is the weighted analogue of the finite counting theorem from
`FiniteConsistencyBound.lean`, and it is the right base lemma for later
distributional or i.i.d. family-level bounds.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal
open scoped BigOperators

universe u v

section WeightedAgreement

variable {Input : Type u} {Output : Type v}
variable [Fintype Input] [DecidableEq Output]

/-- The total input mass on which `predict` agrees with `target`. -/
noncomputable def agreementMass
    (μ : PMF Input) (target predict : Input → Output) : ℝ≥0∞ :=
  ∑ a : AgreementPoints target predict, μ a.1

/-- The product mass of one length-`m` point sample under independent draws from `μ`. -/
noncomputable def sampleMass
    (μ : PMF Input) {m : ℕ} (sample : PointSample Input m) : ℝ≥0∞ :=
  ∏ i, μ (sample i)

/-- The total mass of length-`m` samples on which `predict` agrees with `target`
at every sampled point. -/
noncomputable def consistentSampleMass
    (μ : PMF Input) (target predict : Input → Output) (m : ℕ) : ℝ≥0∞ :=
  ∑ sample : ConsistentSamples target predict m, sampleMass μ sample.1

theorem consistentSampleMass_eq_agreementMass_pow
    (μ : PMF Input) (target predict : Input → Output) (m : ℕ) :
    consistentSampleMass μ target predict m = agreementMass μ target predict ^ m := by
  classical
  unfold consistentSampleMass agreementMass sampleMass
  calc
    (∑ sample : ConsistentSamples target predict m, ∏ i, μ (sample.1 i))
      = ∑ g : Fin m → AgreementPoints target predict, ∏ i, μ (g i).1 := by
          refine Fintype.sum_equiv
            (consistentSamplesEquivAgreementFunctions target predict m)
            (fun sample : ConsistentSamples target predict m => ∏ i, μ (sample.1 i))
            (fun g : Fin m → AgreementPoints target predict => ∏ i, μ (g i).1)
            ?_
          intro sample
          rfl
    _ = (∑ a : AgreementPoints target predict, μ a.1) ^ m := by
          symm
          simpa using
            (Finset.sum_pow'
              (s := Finset.univ)
              (f := fun a : AgreementPoints target predict => μ a.1)
              (n := m))

theorem consistentSampleMass_le_pow_of_agreementMass_le
    (μ : PMF Input) (target predict : Input → Output) (m : ℕ) {q : ℝ≥0∞}
    (hq : agreementMass μ target predict ≤ q) :
    consistentSampleMass μ target predict m ≤ q ^ m := by
  rw [consistentSampleMass_eq_agreementMass_pow]
  exact (pow_left_mono m) hq

end WeightedAgreement

end Mettapedia.Computability.PNP
