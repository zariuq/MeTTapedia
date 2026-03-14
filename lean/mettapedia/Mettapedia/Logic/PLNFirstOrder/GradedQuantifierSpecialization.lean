import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSemanticsInf
import Mettapedia.Logic.PLNFirstOrder.ChoquetQuantifierSemantics

/-!
# Graded Quantifier Specialization

Shared specialization layer for the arbitrary-domain graded quantifier families.

This file factors out the common structure shared by the current Sugeno/proxy-cut
and Choquet quantifier surfaces:

- score-based interval and `ForAll` predicates
- complement-dual `ThereExists` predicates
- fuzzy-domain restriction / relativization
- monotonicity and equality transport on the restricted domain

The purpose is not to erase the semantic differences between the existing
graded branches. It is to expose the honest common spine as a reusable Lean
interface, while keeping the specialized branches explicit instances.
-/

namespace Mettapedia.Logic.PLNFirstOrder

open scoped unitInterval

variable {U : Type*} [MeasurableSpace U]

/-- Pointwise restriction of a fuzzy profile to a fuzzy domain profile. -/
def domainRestrict (C A : FuzzyProfile U) : FuzzyProfile U :=
  ⟨fun u => min (C u) (A u)⟩

/-- Equality of profiles with respect to a fuzzy domain: only the restricted
part matters. -/
def eqOnDomain (C A B : FuzzyProfile U) : Prop :=
  domainRestrict C A = domainRestrict C B

section DomainRestrictionLemmas

variable {U : Type*}

theorem domainRestrict_apply (C A : FuzzyProfile U) (u : U) :
    domainRestrict C A u = min (C u) (A u) := rfl

theorem domainRestrict_assoc
    (C A B : FuzzyProfile U) :
    domainRestrict C (domainRestrict A B) =
      domainRestrict (domainRestrict C A) B := by
  cases C
  cases A
  cases B
  simp [domainRestrict, min_assoc]

theorem domainRestrict_idem
    (C : FuzzyProfile U) :
    domainRestrict C C = C := by
  cases C
  simp [domainRestrict]

theorem domainRestrict_constOne
    (C : FuzzyProfile U) :
    domainRestrict C (FuzzyProfile.const (U := U) (1 : I)) = C := by
  cases C
  refine congrArg FuzzyProfile.mk ?_
  funext u
  exact min_eq_left (unitInterval.le_one _)

theorem domainRestrict_le_right
    (C A : FuzzyProfile U) (u : U) :
    domainRestrict C A u ≤ A u := by
  simp [domainRestrict]

theorem domainRestrict_mono_right
    (C A B : FuzzyProfile U)
    (hAB : ∀ u, A u ≤ B u) :
    ∀ u, domainRestrict C A u ≤ domainRestrict C B u := by
  intro u
  simp [domainRestrict, hAB u]

theorem eqOnDomain_refl
    (C A : FuzzyProfile U) :
    eqOnDomain C A A := rfl

theorem eqOnDomain_symm
    {C A B : FuzzyProfile U} :
    eqOnDomain C A B → eqOnDomain C B A := by
  intro h
  simpa [eqOnDomain] using h.symm

theorem eqOnDomain_trans
    {C A B D : FuzzyProfile U} :
    eqOnDomain C A B → eqOnDomain C B D → eqOnDomain C A D := by
  intro hAB hBD
  simpa [eqOnDomain] using hAB.trans hBD

end DomainRestrictionLemmas

/-- Generic graded quantifier semantics determined by a score on fuzzy profiles.

The common shape is:
- interval truth depends on the score directly
- universal truth depends on the score directly
- existential truth is dualized through the score of the complement profile

Specialized branches remain free to choose different score constructions. -/
structure GradedQuantifierSemantics (U : Type*) [MeasurableSpace U] where
  score : FuzzyProfile U → I
  score_mono_of_pointwise :
    ∀ {f g : FuzzyProfile U}, (∀ u, f u ≤ g u) → score f ≤ score g

namespace GradedQuantifierSemantics

variable (S : GradedQuantifierSemantics U)

/-- Generic interval truth determined by the score. -/
def intervalHolds (p : FuzzyQuantifierParamsInf) (f : FuzzyProfile U) : Prop :=
  p.LPC ≤ (S.score f : ℝ) ∧ (S.score f : ℝ) ≤ p.UPC

/-- Generic universal truth determined by the score. -/
def forAllHolds (p : FuzzyQuantifierParamsInf) (f : FuzzyProfile U) : Prop :=
  p.PCL ≤ (S.score f : ℝ)

/-- Generic existential truth dualized through the complement score. -/
def thereExistsHolds (p : FuzzyQuantifierParamsInf) (f : FuzzyProfile U) : Prop :=
  p.PCL ≤ 1 - (S.score (FuzzyProfile.compl f) : ℝ)

/-- Domain-restricted score for the graded semantics. -/
def scoreOnDomain (C B : FuzzyProfile U) : I :=
  S.score (domainRestrict C B)

/-- Domain-restricted interval truth. -/
def intervalOnDomainHolds
    (p : FuzzyQuantifierParamsInf) (C B : FuzzyProfile U) : Prop :=
  S.intervalHolds p (domainRestrict C B)

/-- Domain-restricted universal truth. -/
def forAllOnDomainHolds
    (p : FuzzyQuantifierParamsInf) (C B : FuzzyProfile U) : Prop :=
  S.forAllHolds p (domainRestrict C B)

/-- Domain-restricted existential truth. -/
def thereExistsOnDomainHolds
    (p : FuzzyQuantifierParamsInf) (C B : FuzzyProfile U) : Prop :=
  S.thereExistsHolds p (domainRestrict C B)

/-- Binary "all" via relativization to the fuzzy domain. -/
def allOnDomainHolds
    (p : FuzzyQuantifierParamsInf) (C A B : FuzzyProfile U) : Prop :=
  S.forAllOnDomainHolds p (domainRestrict C A) (domainRestrict A B)

/-- Binary "some" via relativization to the fuzzy domain. -/
def someOnDomainHolds
    (p : FuzzyQuantifierParamsInf) (C A B : FuzzyProfile U) : Prop :=
  S.thereExistsOnDomainHolds p (domainRestrict C A) (domainRestrict A B)

  theorem score_eq_of_pointwiseEq
    {f g : FuzzyProfile U}
    (hfg : ∀ u, f u = g u) :
    S.score f = S.score g := by
  apply le_antisymm
  · exact S.score_mono_of_pointwise (fun u => by simp [hfg u])
  · exact S.score_mono_of_pointwise (fun u => by simp [hfg u])

theorem intervalHolds_iff_of_scoreEq
    (p : FuzzyQuantifierParamsInf) {f g : FuzzyProfile U}
    (hfg : S.score f = S.score g) :
    S.intervalHolds p f ↔ S.intervalHolds p g := by
  unfold intervalHolds
  simp [hfg]

theorem forAllHolds_iff_of_scoreEq
    (p : FuzzyQuantifierParamsInf) {f g : FuzzyProfile U}
    (hfg : S.score f = S.score g) :
    S.forAllHolds p f ↔ S.forAllHolds p g := by
  unfold forAllHolds
  simp [hfg]

theorem thereExistsHolds_iff_of_complScoreEq
    (p : FuzzyQuantifierParamsInf) {f g : FuzzyProfile U}
    (hfg : S.score (FuzzyProfile.compl f) = S.score (FuzzyProfile.compl g)) :
    S.thereExistsHolds p f ↔ S.thereExistsHolds p g := by
  unfold thereExistsHolds
  simp [hfg]

theorem forAllHolds_mono_of_pointwise
    (p : FuzzyQuantifierParamsInf)
    {f g : FuzzyProfile U}
    (hfg : ∀ u, f u ≤ g u)
    (hf : S.forAllHolds p f) :
    S.forAllHolds p g := by
  unfold forAllHolds at *
  exact le_trans hf (S.score_mono_of_pointwise hfg)

theorem thereExistsHolds_iff_compl
    (p : FuzzyQuantifierParamsInf) (f : FuzzyProfile U) :
    S.thereExistsHolds p f ↔
      p.PCL ≤ 1 - (S.score (FuzzyProfile.compl f) : ℝ) :=
  Iff.rfl

theorem scoreOnDomain_eq_of_eqOnDomain
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    S.scoreOnDomain C A = S.scoreOnDomain C B := by
  simpa [scoreOnDomain] using congrArg S.score hAB

theorem intervalOnDomainHolds_iff_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    S.intervalOnDomainHolds p C A ↔ S.intervalOnDomainHolds p C B := by
  exact S.intervalHolds_iff_of_scoreEq p (S.scoreOnDomain_eq_of_eqOnDomain hAB)

theorem forAllOnDomainHolds_iff_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    S.forAllOnDomainHolds p C A ↔ S.forAllOnDomainHolds p C B := by
  exact S.forAllHolds_iff_of_scoreEq p (S.scoreOnDomain_eq_of_eqOnDomain hAB)

theorem thereExistsOnDomainHolds_iff_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    S.thereExistsOnDomainHolds p C A ↔ S.thereExistsOnDomainHolds p C B := by
  exact S.thereExistsHolds_iff_of_complScoreEq p (by
    simpa [scoreOnDomain] using congrArg (fun t => S.score (FuzzyProfile.compl t)) hAB)

theorem scoreOnDomain_mono_of_pointwise
    (C A B : FuzzyProfile U)
    (hAB : ∀ u, A u ≤ B u) :
    S.scoreOnDomain C A ≤ S.scoreOnDomain C B := by
  exact S.score_mono_of_pointwise (domainRestrict_mono_right C A B hAB)

theorem forAllOnDomainHolds_mono_of_pointwise
    (p : FuzzyQuantifierParamsInf)
    (C A B : FuzzyProfile U)
    (hAB : ∀ u, A u ≤ B u)
    (hA : S.forAllOnDomainHolds p C A) :
    S.forAllOnDomainHolds p C B := by
  exact S.forAllHolds_mono_of_pointwise p (domainRestrict_mono_right C A B hAB) hA

theorem allOnDomainHolds_relativized
    (p : FuzzyQuantifierParamsInf)
    (C A B : FuzzyProfile U) :
    S.allOnDomainHolds p C A B ↔
      S.forAllOnDomainHolds p (domainRestrict C A) (domainRestrict A B) :=
  Iff.rfl

theorem someOnDomainHolds_relativized
    (p : FuzzyQuantifierParamsInf)
    (C A B : FuzzyProfile U) :
    S.someOnDomainHolds p C A B ↔
      S.thereExistsOnDomainHolds p (domainRestrict C A) (domainRestrict A B) :=
  Iff.rfl

end GradedQuantifierSemantics

/-- Sugeno/proxy-cut graded quantifier semantics as an instance of the shared
graded quantifier spine. The threshold parameters are fixed in the score. -/
def sugenoGradedQuantifierSemantics
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) :
    GradedQuantifierSemantics U where
  score := fuzzyExistsScoreInf p ν
  score_mono_of_pointwise := by
    intro f g hfg
    exact fuzzyExistsScoreInf_mono_of_pointwise p ν f g hfg

/-- Choquet graded quantifier semantics as an instance of the shared graded
quantifier spine. -/
noncomputable def choquetGradedQuantifierSemantics
    (ν : FuzzyCapacity U) :
    GradedQuantifierSemantics U where
  score := choquetScoreInf ν
  score_mono_of_pointwise := by
    intro f g hfg
    exact choquetScoreInf_mono ν f g hfg

@[simp] theorem sugenoGraded_intervalHolds_iff
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    (sugenoGradedQuantifierSemantics p ν).intervalHolds p f ↔
      fuzzyIntervalHoldsInf p ν f := by
  rfl

@[simp] theorem sugenoGraded_forAllHolds_iff
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    (sugenoGradedQuantifierSemantics p ν).forAllHolds p f ↔
      fuzzyForAllHoldsInf p ν f := by
  rfl

theorem sugenoGraded_thereExistsHolds_iff
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    (sugenoGradedQuantifierSemantics p ν).thereExistsHolds p f ↔
      fuzzyThereExistsHoldsInf p ν f := by
  simpa [GradedQuantifierSemantics.thereExistsHolds, sugenoGradedQuantifierSemantics] using
    (fuzzyThereExistsHoldsInf_iff_nearOneComplement p ν f).symm

@[simp] theorem choquetGraded_intervalHolds_iff
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    (choquetGradedQuantifierSemantics ν).intervalHolds p f ↔
      choquetIntervalHoldsInf p ν f := by
  rfl

@[simp] theorem choquetGraded_forAllHolds_iff
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    (choquetGradedQuantifierSemantics ν).forAllHolds p f ↔
      choquetForAllHoldsInf p ν f := by
  rfl

@[simp] theorem choquetGraded_thereExistsHolds_iff
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    (choquetGradedQuantifierSemantics ν).thereExistsHolds p f ↔
      choquetThereExistsHoldsInf p ν f := by
  rfl

end Mettapedia.Logic.PLNFirstOrder
