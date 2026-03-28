import Mettapedia.Computability.PNP.FiniteUniformRecovery
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Cast.Order

/-!
# P vs NP background theory: finite uniform rates

This file turns the purely combinatorial sample-counting results into rational
uniform densities on the finite point-sample space.  It still avoids measure
theory: the "probabilities" here are just cardinality ratios in `ℚ`.

The key outcomes are:

* an upper bound on the deceptive-sample rate under uniform sampling,
* a complementary non-deceptive rate identity,
* a lower bound on the exact ERM recovery rate when the target is realized,
* strict positivity of that recovery rate once the finite threshold from
  `FiniteUniformRecovery.lean` is met.
-/

namespace Mettapedia.Computability.PNP

universe u v

namespace EncodedFamily

section UniformRate

variable {Input : Type u} {Output : Type v}
variable [Fintype Input] [DecidableEq Output]
variable (H : EncodedFamily Input Output)

/-- Samples outside the deceptive set. -/
abbrev NondeceptiveSamples (target : Input → Output) (m : ℕ) :=
  { sample : PointSample Input m // ¬ H.IsDeceptiveSample target sample }

noncomputable instance nondeceptiveSamplesFintype
    (target : Input → Output) (m : ℕ) :
    Fintype (H.NondeceptiveSamples target m) :=
  Fintype.ofFinite _

/-- Samples on which the chosen ERM predictor exactly matches the target. -/
abbrev ExactRecoverySamples [Nonempty H.Code] (target : Input → Output) (m : ℕ) :=
  { sample : PointSample Input m //
      H.empiricalRiskPredictor (labeledByTarget target sample) = target }

noncomputable instance exactRecoverySamplesFintype [Nonempty H.Code]
    (target : Input → Output) (m : ℕ) :
    Fintype (H.ExactRecoverySamples target m) :=
  Fintype.ofFinite _

/-- Uniform density of deceptive samples, expressed as a rational cardinality
ratio on the finite point-sample space. -/
noncomputable def deceptiveRate
    (target : Input → Output) (m : ℕ) : ℚ :=
  Fintype.card (H.DeceptiveSamples target m) / Fintype.card (PointSample Input m)

/-- Uniform density of non-deceptive samples. -/
noncomputable def nondeceptiveRate
    (target : Input → Output) (m : ℕ) : ℚ :=
  Fintype.card (H.NondeceptiveSamples target m) / Fintype.card (PointSample Input m)

/-- Uniform density of exact ERM recovery samples. -/
noncomputable def exactRecoveryRate [Nonempty H.Code]
    (target : Input → Output) (m : ℕ) : ℚ :=
  Fintype.card (H.ExactRecoverySamples target m) / Fintype.card (PointSample Input m)

omit [DecidableEq Output] in
theorem card_nondeceptiveSamples
    (target : Input → Output) (m : ℕ) :
    Fintype.card (H.NondeceptiveSamples target m) =
      Fintype.card (PointSample Input m) -
        Fintype.card (H.DeceptiveSamples target m) := by
  classical
  simpa only [NondeceptiveSamples, DeceptiveSamples] using
    (Fintype.card_subtype_compl
      (p := fun sample : PointSample Input m => H.IsDeceptiveSample target sample))

theorem deceptiveRate_le
    [Nonempty Input]
    (target : Input → Output) (m : ℕ) :
    H.deceptiveRate target m ≤
      (((Fintype.card H.Code : ℚ) * ((Fintype.card Input : ℚ) - 1) ^ m) /
        Fintype.card (PointSample Input m)) := by
  have hInput : 1 ≤ Fintype.card Input :=
    Nat.succ_le_of_lt Fintype.card_pos
  have hcard :
      (Fintype.card (H.DeceptiveSamples target m) : ℚ) ≤
        (Fintype.card H.Code : ℚ) * ((Fintype.card Input : ℚ) - 1) ^ m := by
    calc
      (Fintype.card (H.DeceptiveSamples target m) : ℚ)
        ≤ (((Fintype.card H.Code * (Fintype.card Input - 1) ^ m : ℕ) : ℚ)) := by
            exact Nat.cast_le.mpr (H.card_deceptiveSamples_le target m)
      _ = (Fintype.card H.Code : ℚ) * ((Fintype.card Input : ℚ) - 1) ^ m := by
            rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hInput, Nat.cast_one]
  unfold deceptiveRate
  exact div_le_div_of_nonneg_right hcard (by positivity)

theorem deceptiveRate_le_bound
    [Nonempty Input]
    (target : Input → Output) (m : ℕ) :
    H.deceptiveRate target m ≤
      (((Fintype.card H.Code : ℚ) * ((Fintype.card Input : ℚ) - 1) ^ m) /
        ((Fintype.card Input : ℚ) ^ m)) := by
  simpa [card_pointSample Input m, Nat.cast_pow] using H.deceptiveRate_le target m

omit [DecidableEq Output] in
theorem nondeceptiveRate_eq_one_sub_deceptiveRate
    [Nonempty Input]
    (target : Input → Output) (m : ℕ) :
    H.nondeceptiveRate target m = 1 - H.deceptiveRate target m := by
  have hle :
      Fintype.card (H.DeceptiveSamples target m) ≤
        Fintype.card (PointSample Input m) :=
    Fintype.card_subtype_le (fun sample : PointSample Input m =>
      H.IsDeceptiveSample target sample)
  have hcard :
      (Fintype.card (H.NondeceptiveSamples target m) : ℚ) =
        (Fintype.card (PointSample Input m) : ℚ) -
          Fintype.card (H.DeceptiveSamples target m) := by
    calc
      (Fintype.card (H.NondeceptiveSamples target m) : ℚ)
        = (((Fintype.card (PointSample Input m) -
              Fintype.card (H.DeceptiveSamples target m) : ℕ) : ℚ)) := by
              exact congrArg (fun n : ℕ => (n : ℚ)) (H.card_nondeceptiveSamples target m)
      _ = (Fintype.card (PointSample Input m) : ℚ) -
            Fintype.card (H.DeceptiveSamples target m) := by
              rw [Nat.cast_sub hle]
  have hposNat :
      0 < Fintype.card (PointSample Input m) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨fun _ : Fin m => Classical.choice ‹Nonempty Input›⟩
  have hpos :
      (0 : ℚ) < Fintype.card (PointSample Input m) := by
    exact_mod_cast hposNat
  have hne : (Fintype.card (PointSample Input m) : ℚ) ≠ 0 :=
    ne_of_gt hpos
  unfold nondeceptiveRate deceptiveRate
  rw [hcard, sub_div]
  have hunit :
      ((Fintype.card (PointSample Input m) : ℚ) /
        Fintype.card (PointSample Input m)) = 1 := by
    field_simp [hne]
  rw [hunit]

theorem card_nondeceptiveSamples_le_exactRecoverySamples
    [Nonempty H.Code]
    (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target) :
    Fintype.card (H.NondeceptiveSamples target m) ≤
      Fintype.card (H.ExactRecoverySamples target m) := by
  classical
  refine Fintype.card_le_of_embedding ?_
  refine
    { toFun := fun sample =>
        ⟨sample.1,
          H.empiricalRiskPredictor_eq_target_of_not_deceptive
            target sample.1 htarget sample.2⟩
      inj' := ?_ }
  intro a b h
  apply Subtype.ext
  simpa using congrArg Subtype.val h

theorem exactRecoveryRate_ge_nondeceptiveRate
    [Nonempty H.Code]
    (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target) :
    H.nondeceptiveRate target m ≤ H.exactRecoveryRate target m := by
  unfold nondeceptiveRate exactRecoveryRate
  refine div_le_div_of_nonneg_right ?_ ?_
  · exact_mod_cast
      H.card_nondeceptiveSamples_le_exactRecoverySamples target m htarget
  · positivity

theorem exactRecoveryRate_ge_one_sub_deceptiveRate
    [Nonempty Input] [Nonempty H.Code]
    (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target) :
    1 - H.deceptiveRate target m ≤ H.exactRecoveryRate target m := by
  rw [← H.nondeceptiveRate_eq_one_sub_deceptiveRate target m]
  exact H.exactRecoveryRate_ge_nondeceptiveRate target m htarget

theorem exactRecoveryRate_pos_of_bound_lt
    [Nonempty Input] [Nonempty H.Code]
    (target : Input → Output) (m : ℕ)
    (htarget : ∃ c : H.Code, H.decode c = target)
    (hbound :
      Fintype.card H.Code * (Fintype.card Input - 1) ^ m <
        Fintype.card Input ^ m) :
    0 < H.exactRecoveryRate target m := by
  classical
  rcases
      H.exists_sample_empiricalRiskPredictor_eq_target_of_bound_lt
        target m htarget hbound with ⟨sample, hsample⟩
  unfold exactRecoveryRate
  have hnumNat :
      0 < Fintype.card (H.ExactRecoverySamples target m) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨sample, hsample⟩⟩
  have hnum :
      (0 : ℚ) < Fintype.card (H.ExactRecoverySamples target m) := by
    exact_mod_cast hnumNat
  have hdenNat :
      0 < Fintype.card (PointSample Input m) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨fun _ : Fin m => Classical.choice ‹Nonempty Input›⟩
  have hden :
      (0 : ℚ) < Fintype.card (PointSample Input m) := by
    exact_mod_cast hdenNat
  exact div_pos hnum hden

end UniformRate

end EncodedFamily

end Mettapedia.Computability.PNP
