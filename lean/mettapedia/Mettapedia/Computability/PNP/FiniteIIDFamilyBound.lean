import Mettapedia.Computability.PNP.FiniteIIDAgreement

/-!
# P vs NP background theory: finite weighted family bounds

This file lifts the one-predictor weighted agreement law from
`FiniteIIDAgreement.lean` to a whole finite encoded family.

For a finite `PMF μ`, a target `f`, and an encoded family `H`, we define the
total `μ^m`-mass of deceptive samples: length-`m` samples on which some bad code
still agrees with all target labels.  The main theorems are:

* the deceptive mass is bounded by the sum of the bad-code agreement masses,
* if every bad code has one-step agreement mass at most `q`, then the deceptive
  mass is at most `|Code(H)| * q^m`.

This is the clean weighted union-bound layer that should sit between the current
finite combinatorial groundwork and any later PAC-style or asymptotic argument.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal
open scoped BigOperators

universe u v w

namespace EncodedFamily

section WeightedFamilyBound

variable {Input : Type u} {Output : Type v}
variable [Fintype Input] [DecidableEq Output]
variable (H : EncodedFamily Input Output)

instance instDecidableAgreesWithTarget
    (target predict : Input → Output) {m : ℕ} (sample : PointSample Input m) :
    Decidable (AgreesWithTarget target predict sample) := by
  classical
  unfold AgreesWithTarget
  infer_instance

instance instDecidableIsDeceptiveSample
    (target : Input → Output) {m : ℕ} (sample : PointSample Input m) :
    Decidable (H.IsDeceptiveSample target sample) := by
  classical
  unfold EncodedFamily.IsDeceptiveSample
  infer_instance

/-- The total `μ^m`-mass of deceptive samples for `target`. -/
noncomputable def deceptiveSampleMass
    (μ : PMF Input) (target : Input → Output) (m : ℕ) : ℝ≥0∞ :=
  ∑ sample : H.DeceptiveSamples target m, sampleMass μ sample.1

/-- The weighted deceptive mass as a full sample-space sum with an indicator. -/
theorem deceptiveSampleMass_eq_sum_indicator
    (μ : PMF Input) (target : Input → Output) (m : ℕ) :
    H.deceptiveSampleMass μ target m =
      ∑ sample : PointSample Input m,
        if H.IsDeceptiveSample target sample then sampleMass μ sample else 0 := by
  classical
  unfold deceptiveSampleMass
  simpa [Finset.sum_filter] using
    (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset (PointSample Input m)))
      (f := fun sample : PointSample Input m => sampleMass μ sample)
      (p := fun sample => H.IsDeceptiveSample target sample))

/-- The weighted deceptive mass is bounded by the sum of the weighted consistent
sample masses of the bad codes. -/
theorem deceptiveSampleMass_le_badCodeConsistentMassSum
    (μ : PMF Input) (target : Input → Output) (m : ℕ) :
    H.deceptiveSampleMass μ target m ≤
      ∑ c : H.BadCodes target, consistentSampleMass μ target (H.decode c.1) m := by
  classical
  rw [H.deceptiveSampleMass_eq_sum_indicator]
  calc
    (∑ sample : PointSample Input m,
        if H.IsDeceptiveSample target sample then sampleMass μ sample else 0)
      ≤
        ∑ sample : PointSample Input m,
          ∑ c : H.BadCodes target,
            if AgreesWithTarget target (H.decode c.1) sample then sampleMass μ sample else 0 := by
            refine Finset.sum_le_sum ?_
            intro sample _
            by_cases hdec : H.IsDeceptiveSample target sample
            · rcases hdec with ⟨c, hcneq, hcagree⟩
              have hdec' : H.IsDeceptiveSample target sample := ⟨c, hcneq, hcagree⟩
              let cbad : H.BadCodes target := ⟨c, hcneq⟩
              have hsingle :
                  sampleMass μ sample ≤
                    ∑ d : H.BadCodes target,
                      if AgreesWithTarget target (H.decode d.1) sample then
                        sampleMass μ sample
                      else 0 := by
                simpa [cbad, hcagree] using
                  (Finset.single_le_sum
                    (f := fun d : H.BadCodes target =>
                      if AgreesWithTarget target (H.decode d.1) sample then
                        sampleMass μ sample
                      else 0)
                    (fun d _ => by
                      by_cases hd : AgreesWithTarget target (H.decode d.1) sample <;>
                        simp [hd])
                    (Finset.mem_univ cbad))
              calc
                (if H.IsDeceptiveSample target sample then sampleMass μ sample else 0)
                  = sampleMass μ sample := by simp [hdec']
                _ ≤ ∑ d : H.BadCodes target,
                    if AgreesWithTarget target (H.decode d.1) sample then
                      sampleMass μ sample
                    else 0 := hsingle
            · simp [hdec]
    _ = ∑ c : H.BadCodes target,
          ∑ sample : PointSample Input m,
            if AgreesWithTarget target (H.decode c.1) sample then sampleMass μ sample else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ c : H.BadCodes target, consistentSampleMass μ target (H.decode c.1) m := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [show
              (∑ sample : PointSample Input m,
                if AgreesWithTarget target (H.decode c.1) sample then sampleMass μ sample else 0) =
                consistentSampleMass μ target (H.decode c.1) m from by
                  symm
                  unfold consistentSampleMass
                  simpa [Finset.sum_filter] using
                    (Finset.sum_subtype_eq_sum_filter
                      (s := (Finset.univ : Finset (PointSample Input m)))
                      (f := fun sample : PointSample Input m => sampleMass μ sample)
                      (p := fun sample =>
                        AgreesWithTarget target (H.decode c.1) sample))]

/-- The weighted deceptive mass is bounded by the sum of the bad-code
one-step agreement masses raised to the sample length. -/
theorem deceptiveSampleMass_le_badCodeAgreementMassSum
    (μ : PMF Input) (target : Input → Output) (m : ℕ) :
    H.deceptiveSampleMass μ target m ≤
      ∑ c : H.BadCodes target, agreementMass μ target (H.decode c.1) ^ m := by
  calc
    H.deceptiveSampleMass μ target m
      ≤ ∑ c : H.BadCodes target, consistentSampleMass μ target (H.decode c.1) m :=
        H.deceptiveSampleMass_le_badCodeConsistentMassSum μ target m
    _ = ∑ c : H.BadCodes target, agreementMass μ target (H.decode c.1) ^ m := by
      refine Finset.sum_congr rfl ?_
      intro c _
      rw [consistentSampleMass_eq_agreementMass_pow]

/-- Uniform weighted union bound: if every bad code has one-step agreement mass
at most `q`, then the total deceptive mass is at most `|Code(H)| * q^m`. -/
theorem deceptiveSampleMass_le_codeCard_mul_pow_of_agreementMass_le
    (μ : PMF Input) (target : Input → Output) (m : ℕ) {q : ℝ≥0∞}
    (hq : ∀ c : H.BadCodes target, agreementMass μ target (H.decode c.1) ≤ q) :
    H.deceptiveSampleMass μ target m ≤ (Fintype.card H.Code : ℝ≥0∞) * q ^ m := by
  have hbad :
      ∑ c : H.BadCodes target, agreementMass μ target (H.decode c.1) ^ m
        ≤ ∑ _c : H.BadCodes target, q ^ m := by
    refine Finset.sum_le_sum ?_
    intro c _
    exact (pow_left_mono m) (hq c)
  have hcard :
      (Fintype.card (H.BadCodes target) : ℝ≥0∞) * q ^ m ≤
        (Fintype.card H.Code : ℝ≥0∞) * q ^ m := by
    have hbadCard :
        (Fintype.card (H.BadCodes target) : ℝ≥0∞) ≤ Fintype.card H.Code := by
      exact_mod_cast (Fintype.card_subtype_le (fun c : H.Code => H.decode c ≠ target))
    exact mul_le_mul_left hbadCard (q ^ m)
  calc
    H.deceptiveSampleMass μ target m
      ≤ ∑ c : H.BadCodes target, agreementMass μ target (H.decode c.1) ^ m :=
        H.deceptiveSampleMass_le_badCodeAgreementMassSum μ target m
    _ ≤ ∑ _c : H.BadCodes target, q ^ m := hbad
    _ = (Fintype.card (H.BadCodes target) : ℝ≥0∞) * q ^ m := by simp
    _ ≤ (Fintype.card H.Code : ℝ≥0∞) * q ^ m := hcard

end WeightedFamilyBound

end EncodedFamily

end Mettapedia.Computability.PNP
