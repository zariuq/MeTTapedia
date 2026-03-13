import Mettapedia.Logic.PLNFirstOrder.GradedQuantifierSpecialization
import Mettapedia.Logic.PLNFirstOrder.ChoquetQuantifierCanary

/-!
# Graded Quantifier Canary Suite

Direct canaries for the shared graded quantifier specialization layer.

These are intentionally stated against `GradedQuantifierSemantics` itself,
rather than only through the Sugeno/Choquet fuzzy-domain wrappers, so that the
generic graded spine is exercised as a first-class surface.
-/

namespace Mettapedia.Logic.PLNFirstOrder

open scoped unitInterval

noncomputable abbrev natSugenoGraded : GradedQuantifierSemantics Nat :=
  sugenoGradedQuantifierSemantics natProxyParams natThreeLevelCapacity

/-- Stricter threshold used for direct negative canaries. -/
noncomputable def natStrictProxyParams : FuzzyQuantifierParamsInf where
  ε := 0
  LPC := 3 / 4
  UPC := 1
  PCL := 3 / 4
  hε := by constructor <;> norm_num
  hLPC := by constructor <;> norm_num
  hUPC := by constructor <;> norm_num
  hPCL := by constructor <;> norm_num
  hLPC_le_UPC := by norm_num

noncomputable abbrev natStrictSugenoGraded : GradedQuantifierSemantics Nat :=
  sugenoGradedQuantifierSemantics natStrictProxyParams natThreeLevelCapacity

noncomputable abbrev natChoquetGraded : GradedQuantifierSemantics Nat :=
  choquetGradedQuantifierSemantics natThreeLevelCapacity

/-- On the parity domain, the parity profile and the constant-one profile agree
after restriction, so the generic graded score is unchanged. -/
theorem natParity_eqOnDomain_constOne_graded :
    eqOnDomain natParityProfile natParityProfile
      (FuzzyProfile.const (U := Nat) (1 : I)) := by
  rw [eqOnDomain, domainRestrict_idem, domainRestrict_constOne]

/-- Generic Sugeno graded semantics lives on the restricted domain. -/
theorem canary_graded_nat_sugeno_lives_on :
    natSugenoGraded.scoreOnDomain natParityProfile natParityProfile =
      natSugenoGraded.scoreOnDomain natParityProfile
        (FuzzyProfile.const (U := Nat) (1 : I)) := by
  simpa [natSugenoGraded] using
    (GradedQuantifierSemantics.scoreOnDomain_eq_of_eqOnDomain
      (S := natSugenoGraded) natParity_eqOnDomain_constOne_graded)

/-- Generic Choquet graded semantics also lives on the restricted domain. -/
theorem canary_graded_nat_choquet_lives_on :
    natChoquetGraded.scoreOnDomain natParityProfile natParityProfile =
      natChoquetGraded.scoreOnDomain natParityProfile
        (FuzzyProfile.const (U := Nat) (1 : I)) := by
  simpa [natChoquetGraded] using
    (GradedQuantifierSemantics.scoreOnDomain_eq_of_eqOnDomain
      (S := natChoquetGraded) natParity_eqOnDomain_constOne_graded)

/-- The generic Sugeno graded layer proves the positive parity-domain universal
canary directly. -/
theorem canary_graded_nat_sugeno_forall_on_domain :
    natSugenoGraded.forAllOnDomainHolds natProxyParams
      natParityProfile (FuzzyProfile.const (U := Nat) (1 : I)) := by
  simp [natSugenoGraded, GradedQuantifierSemantics.forAllOnDomainHolds,
    GradedQuantifierSemantics.forAllHolds, sugenoGradedQuantifierSemantics,
    domainRestrict_constOne]
  change natProxyParams.PCL ≤
    (nearOneMassInf natProxyParams natThreeLevelCapacity natParityProfile : ℝ)
  rw [canary_inf_fuzzy_nat_support_contrast.1]
  norm_num [natProxyParams]

/-- The generic Choquet graded layer proves the positive parity-domain
universal canary directly. -/
theorem canary_graded_nat_choquet_forall_on_domain :
    natChoquetGraded.forAllOnDomainHolds natProxyParams
      natParityProfile (FuzzyProfile.const (U := Nat) (1 : I)) := by
  simp [natChoquetGraded, GradedQuantifierSemantics.forAllOnDomainHolds,
    GradedQuantifierSemantics.forAllHolds, choquetGradedQuantifierSemantics,
    domainRestrict_constOne]
  rw [canary_choquet_nat_parity]
  norm_num [natProxyParams]

/-- The generic monotonicity theorem is directly usable on the Sugeno instance. -/
theorem canary_graded_nat_sugeno_mono :
    natSugenoGraded.forAllHolds natProxyParams natSingletonProfile →
      natSugenoGraded.forAllHolds natProxyParams
        (FuzzyProfile.const (U := Nat) (1 : I)) := by
  intro hSingleton
  exact GradedQuantifierSemantics.forAllHolds_mono_of_pointwise
    (S := natSugenoGraded) natProxyParams natSingleton_le_constOne hSingleton

/-- The generic monotonicity theorem is directly usable on the Choquet
instance. -/
theorem canary_graded_nat_choquet_mono :
    natChoquetGraded.forAllHolds natProxyParams natSingletonProfile →
      natChoquetGraded.forAllHolds natProxyParams
        (FuzzyProfile.const (U := Nat) (1 : I)) := by
  intro hSingleton
  exact GradedQuantifierSemantics.forAllHolds_mono_of_pointwise
    (S := natChoquetGraded) natProxyParams natSingleton_le_constOne hSingleton

/-- Under a stricter threshold, the singleton profile is no longer enough for
the generic Sugeno graded universal predicate. -/
theorem canary_graded_nat_sugeno_singleton_not_strict :
    ¬ natStrictSugenoGraded.forAllHolds natStrictProxyParams natSingletonProfile := by
  simp [natStrictSugenoGraded, GradedQuantifierSemantics.forAllHolds,
    sugenoGradedQuantifierSemantics, fuzzyExistsScoreInf]
  rw [show nearOneMassInf natStrictProxyParams natThreeLevelCapacity natSingletonProfile =
      natThreeLevelCapacity ({0} : Set Nat) by
        simpa [natSingletonProfile] using
          nearOneMassInf_crispIndicator_eq_cap_of_epsilon_zero
            natStrictProxyParams rfl natThreeLevelCapacity ({0} : Set Nat)]
  rw [natThreeLevelCapacity_singleton_eq_half]
  norm_num [natStrictProxyParams, halfI]

/-- Under the same stricter threshold, the singleton profile is also too weak
for the generic Choquet graded universal predicate. -/
theorem canary_graded_nat_choquet_singleton_not_strict :
    ¬ natChoquetGraded.forAllHolds natStrictProxyParams natSingletonProfile := by
  simp [natChoquetGraded, GradedQuantifierSemantics.forAllHolds,
    choquetGradedQuantifierSemantics]
  rw [canary_choquet_nat_singleton]
  norm_num [natStrictProxyParams, halfI]

/-- The generic graded relativization operator is exposed directly on the
Sugeno instance. -/
theorem canary_graded_nat_sugeno_relativized :
    natSugenoGraded.allOnDomainHolds natProxyParams
      natParityProfile (FuzzyProfile.const (U := Nat) (1 : I))
      (FuzzyProfile.const (U := Nat) (1 : I)) ↔
    natSugenoGraded.forAllOnDomainHolds natProxyParams
      (domainRestrict natParityProfile (FuzzyProfile.const (U := Nat) (1 : I)))
      (domainRestrict (FuzzyProfile.const (U := Nat) (1 : I))
        (FuzzyProfile.const (U := Nat) (1 : I))) := by
  simpa [natSugenoGraded] using
    (GradedQuantifierSemantics.allOnDomainHolds_relativized
      (S := natSugenoGraded) natProxyParams
      natParityProfile (FuzzyProfile.const (U := Nat) (1 : I))
      (FuzzyProfile.const (U := Nat) (1 : I)))

/-- The generic graded relativization operator is exposed directly on the
Choquet instance. -/
theorem canary_graded_nat_choquet_relativized :
    natChoquetGraded.allOnDomainHolds natProxyParams
      natParityProfile (FuzzyProfile.const (U := Nat) (1 : I))
      (FuzzyProfile.const (U := Nat) (1 : I)) ↔
    natChoquetGraded.forAllOnDomainHolds natProxyParams
      (domainRestrict natParityProfile (FuzzyProfile.const (U := Nat) (1 : I)))
      (domainRestrict (FuzzyProfile.const (U := Nat) (1 : I))
        (FuzzyProfile.const (U := Nat) (1 : I))) := by
  simpa [natChoquetGraded] using
    (GradedQuantifierSemantics.allOnDomainHolds_relativized
      (S := natChoquetGraded) natProxyParams
      natParityProfile (FuzzyProfile.const (U := Nat) (1 : I))
      (FuzzyProfile.const (U := Nat) (1 : I)))

end Mettapedia.Logic.PLNFirstOrder
