import Mettapedia.Computability.PNP.FiniteIIDFamilyBound
import Mettapedia.Computability.PNP.FiniteUniformRate

/-!
# P vs NP background theory: finite weighted recovery bounds

This file turns the weighted deceptive-family bound into a weighted recovery
statement for ERM.

The main results are:

* the total `μ^m`-mass of the whole sample space is `1`,
* the nondeceptive and deceptive weighted masses partition that total mass,
* if the target is realized by the family, exact ERM recovery has at least the
  nondeceptive mass,
* therefore exact recovery has lower bounds of the form
  `1 - deceptiveMass`, `1 - ∑ bad α_h^m`, and `1 - |Code(H)| q^m`.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal
open scoped BigOperators

universe u v

namespace EncodedFamily

section WeightedRecovery

variable {Input : Type u} {Output : Type v}
variable [Fintype Input] [DecidableEq Output]
variable (H : EncodedFamily Input Output)

/-- The total `μ^m`-mass of nondeceptive samples. -/
noncomputable def nondeceptiveSampleMass
    (μ : PMF Input) (target : Input → Output) (m : ℕ) : ℝ≥0∞ :=
  ∑ sample : H.NondeceptiveSamples target m, sampleMass μ sample.1

/-- The total `μ^m`-mass of exact ERM recovery samples. -/
noncomputable def exactRecoverySampleMass
    [Nonempty H.Code]
    (μ : PMF Input) (target : Input → Output) (m : ℕ) : ℝ≥0∞ :=
  ∑ sample : H.ExactRecoverySamples target m, sampleMass μ sample.1

noncomputable instance instDecidableExactRecoverySample
    [Nonempty H.Code]
    (target : Input → Output) {m : ℕ} (sample : PointSample Input m) :
    Decidable (H.empiricalRiskPredictor (labeledByTarget target sample) = target) := by
  classical
  infer_instance

theorem nondeceptiveSampleMass_eq_sum_indicator
    (μ : PMF Input) (target : Input → Output) (m : ℕ) :
    H.nondeceptiveSampleMass μ target m =
      ∑ sample : PointSample Input m,
        if ¬ H.IsDeceptiveSample target sample then sampleMass μ sample else 0 := by
  classical
  unfold nondeceptiveSampleMass
  simpa [Finset.sum_filter] using
    (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset (PointSample Input m)))
      (f := fun sample : PointSample Input m => sampleMass μ sample)
      (p := fun sample => ¬ H.IsDeceptiveSample target sample))

theorem exactRecoverySampleMass_eq_sum_indicator
    [Nonempty H.Code]
    (μ : PMF Input) (target : Input → Output) (m : ℕ) :
    H.exactRecoverySampleMass μ target m =
      ∑ sample : PointSample Input m,
        if H.empiricalRiskPredictor (labeledByTarget target sample) = target then
          sampleMass μ sample
        else 0 := by
  classical
  unfold exactRecoverySampleMass
  simpa [Finset.sum_filter] using
    (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset (PointSample Input m)))
      (f := fun sample : PointSample Input m => sampleMass μ sample)
      (p := fun sample =>
        H.empiricalRiskPredictor (labeledByTarget target sample) = target))

theorem sampleMass_sum_eq_one
    (μ : PMF Input) (m : ℕ) :
    (∑ sample : PointSample Input m, sampleMass μ sample) = 1 := by
  classical
  unfold sampleMass
  calc
    (∑ sample : PointSample Input m, ∏ i, μ (sample i))
      = (∑ a : Input, μ a) ^ m := by
          symm
          simpa using
            (Finset.sum_pow'
              (s := Finset.univ)
              (f := fun a : Input => μ a)
              (n := m))
    _ = 1 ^ m := by
          congr 1
          calc
            (∑ a : Input, μ a) = μ.toOuterMeasure (Set.univ : Set Input) := by
              rw [μ.toOuterMeasure_apply_fintype]
              simp
            _ = 1 := by
              simpa using
                (μ.toOuterMeasure_apply_eq_one_iff (s := (Set.univ : Set Input))).2
                  (by simp)
    _ = 1 := by simp

theorem nondeceptiveSampleMass_add_deceptiveSampleMass
    (μ : PMF Input) (target : Input → Output) (m : ℕ) :
    H.nondeceptiveSampleMass μ target m + H.deceptiveSampleMass μ target m = 1 := by
  classical
  rw [H.nondeceptiveSampleMass_eq_sum_indicator, H.deceptiveSampleMass_eq_sum_indicator]
  calc
    ((∑ sample : PointSample Input m,
        if ¬ H.IsDeceptiveSample target sample then sampleMass μ sample else 0) +
      (∑ sample : PointSample Input m,
        if H.IsDeceptiveSample target sample then sampleMass μ sample else 0))
      = ∑ sample : PointSample Input m,
          ((if ¬ H.IsDeceptiveSample target sample then sampleMass μ sample else 0) +
            (if H.IsDeceptiveSample target sample then sampleMass μ sample else 0)) := by
              rw [Finset.sum_add_distrib]
    _ = ∑ sample : PointSample Input m, sampleMass μ sample := by
          refine Finset.sum_congr rfl ?_
          intro sample _
          by_cases hdec : H.IsDeceptiveSample target sample <;> simp [hdec]
    _ = 1 := sampleMass_sum_eq_one μ m

theorem one_sub_deceptiveSampleMass_le_nondeceptiveSampleMass
    (μ : PMF Input) (target : Input → Output) (m : ℕ) :
    1 - H.deceptiveSampleMass μ target m ≤ H.nondeceptiveSampleMass μ target m := by
  apply tsub_le_iff_right.2
  simpa [add_comm] using
    (le_of_eq (H.nondeceptiveSampleMass_add_deceptiveSampleMass μ target m).symm)

theorem exactRecoverySampleMass_ge_nondeceptiveSampleMass
    [Nonempty H.Code]
    (μ : PMF Input) (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target) :
    H.nondeceptiveSampleMass μ target m ≤ H.exactRecoverySampleMass μ target m := by
  classical
  rw [H.nondeceptiveSampleMass_eq_sum_indicator, H.exactRecoverySampleMass_eq_sum_indicator]
  refine Finset.sum_le_sum ?_
  intro sample _
  by_cases hdec : H.IsDeceptiveSample target sample
  · simp [hdec]
  · have hexact :
        H.empiricalRiskPredictor (labeledByTarget target sample) = target :=
      H.empiricalRiskPredictor_eq_target_of_not_deceptive target sample htarget hdec
    simp [hdec, hexact]

theorem exactRecoverySampleMass_ge_one_sub_deceptiveSampleMass
    [Nonempty H.Code]
    (μ : PMF Input) (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target) :
    1 - H.deceptiveSampleMass μ target m ≤ H.exactRecoverySampleMass μ target m := by
  exact le_trans
    (H.one_sub_deceptiveSampleMass_le_nondeceptiveSampleMass μ target m)
    (H.exactRecoverySampleMass_ge_nondeceptiveSampleMass μ target m htarget)

theorem exactRecoverySampleMass_ge_one_sub_badCodeAgreementMassSum
    [Nonempty H.Code]
    (μ : PMF Input) (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target) :
    1 - ∑ c : H.BadCodes target, agreementMass μ target (H.decode c.1) ^ m ≤
      H.exactRecoverySampleMass μ target m := by
  have hdeceptive :
      H.deceptiveSampleMass μ target m ≤
        ∑ c : H.BadCodes target, agreementMass μ target (H.decode c.1) ^ m :=
    H.deceptiveSampleMass_le_badCodeAgreementMassSum μ target m
  have hone :
      1 - ∑ c : H.BadCodes target, agreementMass μ target (H.decode c.1) ^ m
        ≤ 1 - H.deceptiveSampleMass μ target m := by
    exact tsub_le_tsub_left hdeceptive 1
  exact le_trans hone <|
    H.exactRecoverySampleMass_ge_one_sub_deceptiveSampleMass μ target m htarget

theorem exactRecoverySampleMass_ge_one_sub_codeCard_mul_pow_of_agreementMass_le
    [Nonempty H.Code]
    (μ : PMF Input) (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target)
    {q : ℝ≥0∞}
    (hq : ∀ c : H.BadCodes target, agreementMass μ target (H.decode c.1) ≤ q) :
    1 - (Fintype.card H.Code : ℝ≥0∞) * q ^ m ≤
      H.exactRecoverySampleMass μ target m := by
  have hdeceptive :
      H.deceptiveSampleMass μ target m ≤ (Fintype.card H.Code : ℝ≥0∞) * q ^ m :=
    H.deceptiveSampleMass_le_codeCard_mul_pow_of_agreementMass_le μ target m hq
  have hone :
      1 - (Fintype.card H.Code : ℝ≥0∞) * q ^ m
        ≤ 1 - H.deceptiveSampleMass μ target m := by
    exact tsub_le_tsub_left hdeceptive 1
  exact le_trans hone <|
    H.exactRecoverySampleMass_ge_one_sub_deceptiveSampleMass μ target m htarget

end WeightedRecovery

end EncodedFamily

end Mettapedia.Computability.PNP
