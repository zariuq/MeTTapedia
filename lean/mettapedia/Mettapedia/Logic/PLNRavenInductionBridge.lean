import Mettapedia.Logic.RavenAsymmetricInduction
import Mettapedia.Logic.PLNBayesInversionBridge

/-!
# Raven Asymmetric Induction as Guarded Bayes Inversion

`RavenAsymmetricInduction.lean` is the book-facing evidence-count example:
observing black ravens confirms `Raven -> Black`, while the inverse
`Black -> Raven` is diluted by all other black observations.

This file welds that example to the generic WM-PLN Bayes/Inversion surface.  The
inverse raven strength is exactly the Bayes inversion of the forward strength
through the observed base rate, with the same explicit admissibility guard used
by `PLNBayesInversionBridge`.  This is a point-strength bridge, not an interval
tightness theorem.
-/

namespace Mettapedia.Logic.PLN

namespace RavenInductionBridge

open Mettapedia.Logic.RavenAsymmetricInduction
open Mettapedia.Logic.EvidenceQuantale.BinaryEvidence

/-- In the black-observation subpopulation, the observed raven base rate is
`R / (R + M)`, where `R` is the number of black ravens and `M` the number of
black non-ravens. -/
noncomputable def ravenObservationBaseRate (R M : ℕ) : ℝ :=
  (R : ℝ) / ((R : ℝ) + (M : ℝ))

/-- The forward count-strength `Raven -> Black` is real-valued `1` whenever at
least one raven has been observed. -/
theorem ravenBlackStrength_toReal_eq_one (R : ℕ) (hR : 0 < R) :
    (toStrength (ravenBlackEvidence R)).toReal = (1 : ℝ) := by
  rw [strength_ravenBlack R hR]
  norm_num

/-- The inverse count-strength `Black -> Raven` is the observed raven base rate
inside the black-observation subpopulation. -/
theorem blackRavenStrength_toReal_eq_baseRate (R M : ℕ) (h : 0 < R + M) :
    (toStrength (blackRavenEvidence R M)).toReal =
      ravenObservationBaseRate R M := by
  rw [strength_blackRaven R M h]
  unfold ravenObservationBaseRate
  rw [ENNReal.toReal_div]
  rw [ENNReal.toReal_add (ENNReal.natCast_ne_top R) (ENNReal.natCast_ne_top M)]
  simp

/-- The Raven induction instance satisfies the guarded Bayes/Inversion side
conditions when the observed black population has at least one raven.

The joint constraint reduces to `P(Raven) <= P(Black) = 1`, i.e. the base-rate
ratio is a probability. -/
theorem ravenInduction_bayesInversion_admissible (R M : ℕ) (hR : 0 < R) :
    BayesInversionAdmissible
      (toStrength (ravenBlackEvidence R)).toReal
      (ravenObservationBaseRate R M)
      1 := by
  rw [ravenBlackStrength_toReal_eq_one R hR]
  unfold BayesInversionAdmissible ravenObservationBaseRate
  have hden_pos : 0 < (R : ℝ) + (M : ℝ) := by
    exact_mod_cast Nat.add_pos_left hR M
  have hbase_nonneg : 0 ≤ (R : ℝ) / ((R : ℝ) + (M : ℝ)) := by
    positivity
  have hbase_le_one : (R : ℝ) / ((R : ℝ) + (M : ℝ)) ≤ 1 := by
    rw [div_le_one hden_pos]
    exact_mod_cast Nat.le_add_right R M
  constructor <;> try constructor <;> try constructor <;> try constructor <;>
    try constructor <;> try constructor
  · norm_num
  · norm_num
  · exact hbase_nonneg
  · exact hbase_le_one
  · norm_num
  · norm_num
  · simpa using hbase_le_one

/-- The inverse Raven induction strength is exactly guarded Bayes inversion of
the forward `Raven -> Black` strength through the observed base rate. -/
theorem blackRavenStrength_toReal_eq_bayesInversion
    (R M : ℕ) (hR : 0 < R) (hTotal : 0 < R + M) :
    (toStrength (blackRavenEvidence R M)).toReal =
      plnInversionBayesStrength
        (toStrength (ravenBlackEvidence R)).toReal
        (ravenObservationBaseRate R M)
        1 := by
  rw [blackRavenStrength_toReal_eq_baseRate R M hTotal]
  rw [ravenBlackStrength_toReal_eq_one R hR]
  unfold ravenObservationBaseRate plnInversionBayesStrength bayesInversion
  ring

/-- Concrete value canary for the standard `5` black ravens and `95` other
black observations example. -/
theorem ravenInduction_bayesInversion_values_canary :
    (toStrength (ravenBlackEvidence 5)).toReal = (1 : ℝ) ∧
      (toStrength (blackRavenEvidence 5 95)).toReal = (1 / 20 : ℝ) ∧
      ravenObservationBaseRate 5 95 = (1 / 20 : ℝ) ∧
      plnInversionBayesStrength
          (toStrength (ravenBlackEvidence 5)).toReal
          (ravenObservationBaseRate 5 95)
          1 = (1 / 20 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ravenBlackStrength_toReal_eq_one 5 (by norm_num)
  · rw [blackRavenStrength_toReal_eq_baseRate 5 95 (by norm_num)]
    norm_num [ravenObservationBaseRate]
  · norm_num [ravenObservationBaseRate]
  · rw [ravenBlackStrength_toReal_eq_one 5 (by norm_num)]
    norm_num [ravenObservationBaseRate, plnInversionBayesStrength, bayesInversion]

/-- Negative canary: with other black observations present, the inverse
`Black -> Raven` strength is not the forward certainty `Raven -> Black`. -/
theorem ravenInduction_inverse_ne_forward_canary :
    (toStrength (blackRavenEvidence 5 95)).toReal ≠
      (toStrength (ravenBlackEvidence 5)).toReal := by
  rw [blackRavenStrength_toReal_eq_baseRate 5 95 (by norm_num)]
  rw [ravenBlackStrength_toReal_eq_one 5 (by norm_num)]
  norm_num [ravenObservationBaseRate]

/-- The concrete Bayes/Inversion instance is admissible and remains in the unit
interval. -/
theorem ravenInduction_bayesInversion_guard_canary :
    BayesInversionAdmissible
        (toStrength (ravenBlackEvidence 5)).toReal
        (ravenObservationBaseRate 5 95)
        1 ∧
      plnInversionBayesStrength
          (toStrength (ravenBlackEvidence 5)).toReal
          (ravenObservationBaseRate 5 95)
          1 ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨ravenInduction_bayesInversion_admissible 5 95 (by norm_num), ?_⟩
  exact plnInversionBayesStrength_mem_Icc
    (toStrength (ravenBlackEvidence 5)).toReal
    (ravenObservationBaseRate 5 95)
    1
    (ravenInduction_bayesInversion_admissible 5 95 (by norm_num))

end RavenInductionBridge

end Mettapedia.Logic.PLN
