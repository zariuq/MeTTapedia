import Mettapedia.Logic.PLNFirstOrder.ChoquetQuantifierSemantics
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierCanaryInf

/-!
# Choquet Quantifier Canary Suite

Concrete canaries for the Choquet-style infinitary fuzzy layer.
-/

namespace Mettapedia.Logic.PLNFirstOrder

open scoped unitInterval

/-- Infinite-support crisp canary: the Choquet score of the parity profile is the
top level of the Nat three-level capacity. -/
theorem canary_choquet_nat_parity :
    choquetScoreInf natThreeLevelCapacity natParityProfile = 1 := by
  calc
    choquetScoreInf natThreeLevelCapacity natParityProfile
      = natThreeLevelCapacity natEvenRange := by
          simpa [choquetScoreInf, natParityProfile] using
            FuzzyCapacity.choquetIntegral_crispIndicator natThreeLevelCapacity natEvenRange
    _ = 1 := natThreeLevelCapacity_evenRange_eq_one

/-- Finite-support contrast canary: the singleton profile lands at the middle
level of the Nat three-level capacity. -/
theorem canary_choquet_nat_singleton :
    choquetScoreInf natThreeLevelCapacity natSingletonProfile = halfI := by
  calc
    choquetScoreInf natThreeLevelCapacity natSingletonProfile
      = natThreeLevelCapacity ({0} : Set Nat) := by
          simpa [choquetScoreInf, natSingletonProfile] using
            FuzzyCapacity.choquetIntegral_crispIndicator natThreeLevelCapacity ({0} : Set Nat)
    _ = halfI := natThreeLevelCapacity_singleton_eq_half

/-- Constant-profile canary for normalized Choquet semantics. -/
theorem canary_choquet_nat_constant_one :
    choquetScoreInf natThreeLevelCapacity (FuzzyProfile.const (U := Nat) (1 : I)) = 1 :=
  choquetScoreInf_constantOne_eq_one
    natThreeLevelCapacity natThreeLevelCapacity_isNormalized

/-- Monotonicity canary for the Choquet score. -/
theorem canary_choquet_nat_monotonicity :
    choquetScoreInf natThreeLevelCapacity natSingletonProfile ≤
      choquetScoreInf natThreeLevelCapacity (FuzzyProfile.const (U := Nat) (1 : I)) :=
  choquetScoreInf_mono natThreeLevelCapacity
    natSingletonProfile (FuzzyProfile.const (U := Nat) (1 : I))
    natSingleton_le_constOne

end Mettapedia.Logic.PLNFirstOrder
