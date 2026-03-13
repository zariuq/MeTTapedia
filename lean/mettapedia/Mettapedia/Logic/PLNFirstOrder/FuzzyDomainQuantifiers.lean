import Mettapedia.Logic.PLNFirstOrder.GradedQuantifierSpecialization

/-!
# Fuzzy Domain Quantifiers

Fuzzy-domain lift for the infinitary `[0,1]`-valued quantifier surface.

The basic idea follows the Dvorak-Holcapek fuzzy-universe/fuzzy-domain line:
the quantifier acts over a pair `(M, C)`, where `C` is a fuzzy domain profile on
the crisp carrier `M`, and arguments are evaluated only through their
restriction to `C`.

This file now packages the Sugeno/proxy-cut and Choquet branches as explicit
specializations of the shared graded quantifier layer from
`GradedQuantifierSpecialization.lean`.
-/

namespace Mettapedia.Logic.PLNFirstOrder

open scoped unitInterval

variable {U : Type*} [MeasurableSpace U]

/-- Proxy-cut existential score restricted to a fuzzy domain. -/
abbrev fuzzyExistsOnDomainScoreInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C B : FuzzyProfile U) : I :=
  (sugenoGradedQuantifierSemantics p ν).scoreOnDomain C B

/-- Proxy-cut interval truth restricted to a fuzzy domain. -/
abbrev fuzzyIntervalOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C B : FuzzyProfile U) : Prop :=
  (sugenoGradedQuantifierSemantics p ν).intervalOnDomainHolds p C B

/-- Proxy-cut universal truth restricted to a fuzzy domain. -/
abbrev fuzzyForAllOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C B : FuzzyProfile U) : Prop :=
  (sugenoGradedQuantifierSemantics p ν).forAllOnDomainHolds p C B

/-- Proxy-cut existential truth restricted to a fuzzy domain. -/
abbrev fuzzyThereExistsOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C B : FuzzyProfile U) : Prop :=
  (sugenoGradedQuantifierSemantics p ν).thereExistsOnDomainHolds p C B

/-- Binary "all" obtained by relativizing the unary proxy-cut universal semantics
through the fuzzy domain profile. -/
abbrev fuzzyAllOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U) : Prop :=
  (sugenoGradedQuantifierSemantics p ν).allOnDomainHolds p C A B

/-- Binary "some" obtained by relativizing the unary proxy-cut existential semantics
through the fuzzy domain profile. -/
abbrev fuzzySomeOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U) : Prop :=
  (sugenoGradedQuantifierSemantics p ν).someOnDomainHolds p C A B

theorem fuzzyExistsOnDomainScoreInf_eq_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    fuzzyExistsOnDomainScoreInf p ν C A = fuzzyExistsOnDomainScoreInf p ν C B :=
  (sugenoGradedQuantifierSemantics p ν).scoreOnDomain_eq_of_eqOnDomain hAB

theorem fuzzyIntervalOnDomainHoldsInf_iff_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    fuzzyIntervalOnDomainHoldsInf p ν C A ↔ fuzzyIntervalOnDomainHoldsInf p ν C B :=
  (sugenoGradedQuantifierSemantics p ν).intervalOnDomainHolds_iff_of_eqOnDomain p hAB

theorem fuzzyForAllOnDomainHoldsInf_iff_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    fuzzyForAllOnDomainHoldsInf p ν C A ↔ fuzzyForAllOnDomainHoldsInf p ν C B :=
  (sugenoGradedQuantifierSemantics p ν).forAllOnDomainHolds_iff_of_eqOnDomain p hAB

theorem fuzzyThereExistsOnDomainHoldsInf_iff_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    fuzzyThereExistsOnDomainHoldsInf p ν C A ↔
      fuzzyThereExistsOnDomainHoldsInf p ν C B := by
  simpa [fuzzyThereExistsOnDomainHoldsInf] using
    (sugenoGradedQuantifierSemantics p ν).thereExistsOnDomainHolds_iff_of_eqOnDomain p hAB

theorem fuzzyExistsOnDomainScoreInf_mono_of_pointwise
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U)
    (hAB : ∀ u, A u ≤ B u) :
    fuzzyExistsOnDomainScoreInf p ν C A ≤ fuzzyExistsOnDomainScoreInf p ν C B :=
  (sugenoGradedQuantifierSemantics p ν).scoreOnDomain_mono_of_pointwise C A B hAB

theorem fuzzyForAllOnDomainHoldsInf_mono_of_pointwise
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U)
    (hAB : ∀ u, A u ≤ B u)
    (hA : fuzzyForAllOnDomainHoldsInf p ν C A) :
    fuzzyForAllOnDomainHoldsInf p ν C B :=
  (sugenoGradedQuantifierSemantics p ν).forAllOnDomainHolds_mono_of_pointwise p C A B hAB hA

theorem fuzzyAllOnDomainHoldsInf_relativized
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U) :
    fuzzyAllOnDomainHoldsInf p ν C A B ↔
      fuzzyForAllOnDomainHoldsInf p ν (domainRestrict C A) (domainRestrict A B) :=
  (sugenoGradedQuantifierSemantics p ν).allOnDomainHolds_relativized p C A B

theorem fuzzySomeOnDomainHoldsInf_relativized
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U) :
    fuzzySomeOnDomainHoldsInf p ν C A B ↔
      fuzzyThereExistsOnDomainHoldsInf p ν (domainRestrict C A) (domainRestrict A B) :=
  (sugenoGradedQuantifierSemantics p ν).someOnDomainHolds_relativized p C A B

/-- Choquet score restricted to a fuzzy domain. -/
noncomputable abbrev choquetOnDomainScoreInf
    (ν : FuzzyCapacity U) (C B : FuzzyProfile U) : I :=
  (choquetGradedQuantifierSemantics ν).scoreOnDomain C B

/-- Choquet interval truth restricted to a fuzzy domain. -/
abbrev choquetIntervalOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C B : FuzzyProfile U) : Prop :=
  (choquetGradedQuantifierSemantics ν).intervalOnDomainHolds p C B

/-- Choquet universal truth restricted to a fuzzy domain. -/
abbrev choquetForAllOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C B : FuzzyProfile U) : Prop :=
  (choquetGradedQuantifierSemantics ν).forAllOnDomainHolds p C B

/-- Choquet existential truth restricted to a fuzzy domain. -/
abbrev choquetThereExistsOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C B : FuzzyProfile U) : Prop :=
  (choquetGradedQuantifierSemantics ν).thereExistsOnDomainHolds p C B

/-- Binary Choquet "all" by relativization through a fuzzy domain profile. -/
abbrev choquetAllOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U) : Prop :=
  (choquetGradedQuantifierSemantics ν).allOnDomainHolds p C A B

/-- Binary Choquet "some" by relativization through a fuzzy domain profile. -/
abbrev choquetSomeOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U) : Prop :=
  (choquetGradedQuantifierSemantics ν).someOnDomainHolds p C A B

theorem choquetOnDomainScoreInf_eq_of_eqOnDomain
    (ν : FuzzyCapacity U)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    choquetOnDomainScoreInf ν C A = choquetOnDomainScoreInf ν C B :=
  (choquetGradedQuantifierSemantics ν).scoreOnDomain_eq_of_eqOnDomain hAB

theorem choquetIntervalOnDomainHoldsInf_iff_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    choquetIntervalOnDomainHoldsInf p ν C A ↔
      choquetIntervalOnDomainHoldsInf p ν C B :=
  (choquetGradedQuantifierSemantics ν).intervalOnDomainHolds_iff_of_eqOnDomain p hAB

theorem choquetForAllOnDomainHoldsInf_iff_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    choquetForAllOnDomainHoldsInf p ν C A ↔
      choquetForAllOnDomainHoldsInf p ν C B :=
  (choquetGradedQuantifierSemantics ν).forAllOnDomainHolds_iff_of_eqOnDomain p hAB

theorem choquetThereExistsOnDomainHoldsInf_iff_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    choquetThereExistsOnDomainHoldsInf p ν C A ↔
      choquetThereExistsOnDomainHoldsInf p ν C B :=
  (choquetGradedQuantifierSemantics ν).thereExistsOnDomainHolds_iff_of_eqOnDomain p hAB

theorem choquetOnDomainScoreInf_mono_of_pointwise
    (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U)
    (hAB : ∀ u, A u ≤ B u) :
    choquetOnDomainScoreInf ν C A ≤ choquetOnDomainScoreInf ν C B :=
  (choquetGradedQuantifierSemantics ν).scoreOnDomain_mono_of_pointwise C A B hAB

theorem choquetForAllOnDomainHoldsInf_mono_of_pointwise
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U)
    (hAB : ∀ u, A u ≤ B u)
    (hA : choquetForAllOnDomainHoldsInf p ν C A) :
    choquetForAllOnDomainHoldsInf p ν C B :=
  (choquetGradedQuantifierSemantics ν).forAllOnDomainHolds_mono_of_pointwise p C A B hAB hA

theorem choquetAllOnDomainHoldsInf_relativized
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U) :
    choquetAllOnDomainHoldsInf p ν C A B ↔
      choquetForAllOnDomainHoldsInf p ν (domainRestrict C A) (domainRestrict A B) :=
  (choquetGradedQuantifierSemantics ν).allOnDomainHolds_relativized p C A B

theorem choquetSomeOnDomainHoldsInf_relativized
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U) :
    choquetSomeOnDomainHoldsInf p ν C A B ↔
      choquetThereExistsOnDomainHoldsInf p ν (domainRestrict C A) (domainRestrict A B) :=
  (choquetGradedQuantifierSemantics ν).someOnDomainHolds_relativized p C A B

end Mettapedia.Logic.PLNFirstOrder
