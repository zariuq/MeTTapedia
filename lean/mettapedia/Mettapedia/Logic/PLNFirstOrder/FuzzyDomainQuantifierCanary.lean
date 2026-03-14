import Mettapedia.Logic.PLNFirstOrder.FuzzyDomainQuantifiers
import Mettapedia.Logic.PLNFirstOrder.ChoquetQuantifierCanary

/-!
# Fuzzy Domain Quantifier Canary Suite

Concrete canaries for fuzzy-domain restriction and relativization.
-/

namespace Mettapedia.Logic.PLNFirstOrder

open scoped unitInterval

/-- On the parity domain, the parity profile and the constant-one profile agree
after domain restriction. -/
theorem natParity_eqOnDomain_constOne :
    eqOnDomain natParityProfile natParityProfile
      (FuzzyProfile.const (U := Nat) (1 : I)) := by
  rw [eqOnDomain, domainRestrict_idem, domainRestrict_constOne]

/-- Proxy-cut semantics really lives on the fuzzy domain: changing values off the
domain does not change the restricted score. -/
theorem canary_fuzzy_domain_nat_proxy_lives_on :
    fuzzyExistsOnDomainScoreInf natProxyParams natThreeLevelCapacity
        natParityProfile natParityProfile =
      fuzzyExistsOnDomainScoreInf natProxyParams natThreeLevelCapacity
        natParityProfile (FuzzyProfile.const (U := Nat) (1 : I)) :=
  fuzzyExistsOnDomainScoreInf_eq_of_eqOnDomain
    natProxyParams natThreeLevelCapacity natParity_eqOnDomain_constOne

/-- Choquet semantics also lives on the fuzzy domain. -/
theorem canary_fuzzy_domain_nat_choquet_lives_on :
    choquetOnDomainScoreInf natThreeLevelCapacity
        natParityProfile natParityProfile =
      choquetOnDomainScoreInf natThreeLevelCapacity
        natParityProfile (FuzzyProfile.const (U := Nat) (1 : I)) :=
  choquetOnDomainScoreInf_eq_of_eqOnDomain
    natThreeLevelCapacity natParity_eqOnDomain_constOne

/-- Proxy-cut universal truth on the parity domain succeeds for the constant-one
profile because the restricted profile is exactly the parity domain. -/
theorem canary_fuzzy_domain_nat_proxy_forall :
    fuzzyForAllOnDomainHoldsInf natProxyParams natThreeLevelCapacity
      natParityProfile (FuzzyProfile.const (U := Nat) (1 : I)) := by
  simp [fuzzyForAllOnDomainHoldsInf, GradedQuantifierSemantics.forAllOnDomainHolds,
    GradedQuantifierSemantics.forAllHolds, sugenoGradedQuantifierSemantics, domainRestrict_constOne]
  change natProxyParams.PCL ≤
    (nearOneMassInf natProxyParams natThreeLevelCapacity natParityProfile : ℝ)
  rw [canary_inf_fuzzy_nat_support_contrast.1]
  norm_num [natProxyParams]

/-- Choquet universal truth on the parity domain succeeds for the constant-one
profile because the restricted profile is exactly the parity domain. -/
theorem canary_fuzzy_domain_nat_choquet_forall :
    choquetForAllOnDomainHoldsInf natProxyParams natThreeLevelCapacity
      natParityProfile (FuzzyProfile.const (U := Nat) (1 : I)) := by
  simp [choquetForAllOnDomainHoldsInf, GradedQuantifierSemantics.forAllOnDomainHolds,
    GradedQuantifierSemantics.forAllHolds, choquetGradedQuantifierSemantics, domainRestrict_constOne]
  rw [canary_choquet_nat_parity]
  norm_num [natProxyParams]

/-- Binary relativization for proxy-cut semantics is exposed as a first-class
fuzzy-domain operator. -/
theorem canary_fuzzy_domain_nat_proxy_relativization :
    fuzzyAllOnDomainHoldsInf natProxyParams natThreeLevelCapacity
      natParityProfile (FuzzyProfile.const (U := Nat) (1 : I))
      (FuzzyProfile.const (U := Nat) (1 : I)) ↔
    fuzzyForAllOnDomainHoldsInf natProxyParams natThreeLevelCapacity
      (domainRestrict natParityProfile (FuzzyProfile.const (U := Nat) (1 : I)))
      (domainRestrict (FuzzyProfile.const (U := Nat) (1 : I))
        (FuzzyProfile.const (U := Nat) (1 : I))) :=
  fuzzyAllOnDomainHoldsInf_relativized
    natProxyParams natThreeLevelCapacity
    natParityProfile (FuzzyProfile.const (U := Nat) (1 : I))
    (FuzzyProfile.const (U := Nat) (1 : I))

/-- Binary relativization for Choquet semantics is likewise first-class. -/
theorem canary_fuzzy_domain_nat_choquet_relativization :
    choquetAllOnDomainHoldsInf natProxyParams natThreeLevelCapacity
      natParityProfile (FuzzyProfile.const (U := Nat) (1 : I))
      (FuzzyProfile.const (U := Nat) (1 : I)) ↔
    choquetForAllOnDomainHoldsInf natProxyParams natThreeLevelCapacity
      (domainRestrict natParityProfile (FuzzyProfile.const (U := Nat) (1 : I)))
      (domainRestrict (FuzzyProfile.const (U := Nat) (1 : I))
        (FuzzyProfile.const (U := Nat) (1 : I))) :=
  choquetAllOnDomainHoldsInf_relativized
    natProxyParams natThreeLevelCapacity
    natParityProfile (FuzzyProfile.const (U := Nat) (1 : I))
    (FuzzyProfile.const (U := Nat) (1 : I))

end Mettapedia.Logic.PLNFirstOrder
