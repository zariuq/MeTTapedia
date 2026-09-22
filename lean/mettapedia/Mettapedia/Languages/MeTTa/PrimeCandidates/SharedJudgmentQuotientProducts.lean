import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientComprehension
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientProductRepresentation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientProductTermRepresentation

/-!
# Actual product and sum meanings on the shared quotient

Native formation and conversion are interpreted through the same graph as
admission, declarations and universes. Independently qualified dependent
families are reduced to their actual native representatives by comprehension
uniqueness. The component predicates do not require a separate total
identity eliminator; no full constructor record is claimed here.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientProducts

open _root_.CategoryTheory
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation FormationSensitive SharedJudgmentFragment
open FormationSensitiveContextual SharedJudgmentQuotientInterpretation
open SharedJudgmentTypeInterpretation SharedJudgmentQuotientComprehension
open QuotientComprehensionSyntax
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

variable {assembly : Assembly}

theorem code_conversion_of_meaning {n : Nat}
    {source : SharedJudgmentInterpretation.Context assembly n}
    {term annotation : Tower.Tm n}
    {semanticType : (QuotientCwf.cwf assembly.rules).Ty ((data assembly).ctx source)}
    {value : (QuotientCwf.cwf assembly.rules).Tm ((data assembly).ctx source) semanticType}
    (meaning : (data assembly).term source term annotation semanticType value) :
    Conv assembly.rules.headEq (chosenTerm value).code term assembly.rules.computation := by
  obtain ⟨actualType, _, actual, sameCode, _, sameValue⟩ := meaning
  exact sameCode ▸ chosenTerm_represents value actual sameValue

/-- The result annotation is independently admitted and represented.
Conversion of the result code alone would not supply either fact. -/
theorem meaning_of_code_conversion {n : Nat}
    {source : SharedJudgmentInterpretation.Context assembly n}
    {term annotation : Tower.Tm n}
    {semanticType : (QuotientCwf.cwf assembly.rules).Ty ((data assembly).ctx source)}
    {value : (QuotientCwf.cwf assembly.rules).Tm ((data assembly).ctx source) semanticType}
    (admitted : Judgment assembly.rules source.raw term annotation)
    (typeMeaning : (data assembly).ty source annotation semanticType)
    (converted : Conv assembly.rules.headEq (chosenTerm value).code term assembly.rules.computation) :
    (data assembly).term source term annotation semanticType value := by
  obtain ⟨actualType, rfl, represented⟩ := typeMeaning
  let actual : Term (context source) actualType := ⟨term, admitted.typing⟩
  refine ⟨actualType, rfl, actual, rfl, represented, ?_⟩
  apply Eq.trans _ (chosenTerm_class value)
  apply (QTerm.mk_eq_iff actual (chosenTerm value)).mpr
  exact ⟨(QType.mk_eq_iff _ _).mp
    (represented.trans (QuotientCwf.typeRepresentative_class semanticType).symm), converted.symm⟩

theorem pi_formation_meaning :
    PiFormationMeaning (data assembly) (QuotientProducts.products assembly.declarations) := by
  intro n source domain codomain family _ meaning
  obtain ⟨actualDomain, actualCodomain, rfl, rfl, same⟩ := family_representation family meaning
  cases eq_of_heq same
  exact ⟨QuotientProducts.nativePi actualDomain actualCodomain, rfl,
    (QuotientProductRepresentation.pi_projects actualDomain actualCodomain).symm⟩

theorem sigma_formation_meaning :
    SigmaFormationMeaning (data assembly) (QuotientProducts.sums assembly.declarations) := by
  intro n source domain codomain family _ meaning
  obtain ⟨actualDomain, actualCodomain, rfl, rfl, same⟩ := family_representation family meaning
  cases eq_of_heq same
  exact ⟨QuotientProducts.nativeSigma actualDomain actualCodomain, rfl,
    (QuotientProductRepresentation.sigma_projects actualDomain actualCodomain).symm⟩

/-- Instantiating a dependent family uses the caller's actual admitted
argument, not an unrelated representative with the same result type. -/
theorem instantiated_type_meaning {n : Nat}
    (source : SharedJudgmentInterpretation.Context assembly n)
    (domain : TypeOver (context source))
    (codomain : TypeOver (extend (context source) domain)) (argument : Tower.Tm n)
    (semanticArgument : (QuotientCwf.cwf assembly.rules).Tm ((data assembly).ctx source) (QType.mk domain))
    (admitted : Judgment assembly.rules source.raw argument domain.code)
    (meaning : (data assembly).term source argument domain.code (QType.mk domain) semanticArgument) :
    (data assembly).ty source (inst0 argument codomain.code)
      (QuotientCwf.tySub
        (QuotientCwf.tySub (QType.mk codomain) (QuotientCwf.extPresentation (context source) domain).hom)
        (selfExtend (QuotientCwf.cwf assembly.rules) semanticArgument)) := by
  let actual : Term (context source) domain := ⟨argument, admitted.typing⟩
  have same : QTerm.mk actual = semanticArgument.val :=
    term_meaning_value_unique (QuotientInterpretation.term_meaning (context source) actual) meaning
  refine ⟨codomain.reindex (nativeSection actual), ?_,
    (QuotientProductTermRepresentation.type_at_argument domain codomain actual semanticArgument same).symm⟩
  change subst (nativeSection actual).substitution codomain.code = inst0 argument codomain.code
  rw [nativeSection_substitution]
  rfl

theorem pi_introduction_meaning :
    PiIntroductionMeaning (data assembly) (QuotientProducts.products assembly.declarations) := by
  intro n source domain codomain body family semanticBody admitted meaning bodyAdmitted bodyMeaning
  obtain ⟨actualDomain, actualCodomain, rfl, rfl, same⟩ := family_representation family meaning
  cases eq_of_heq same
  apply meaning_of_code_conversion
  · exact ⟨source.formed, .lamIntro (QuotientProducts.nativePi actualDomain actualCodomain).formed
      (QuotientProducts.nativePi actualDomain actualCodomain).universeWitness bodyAdmitted.typing⟩
  · exact pi_formation_meaning n source _ _ _ admitted meaning
  · exact .trans _ _ _ (QuotientProductTermRepresentation.lam_through_presentation actualDomain semanticBody)
      (Conv.congLam (code_conversion_of_meaning bodyMeaning))

theorem pi_elimination_meaning :
    PiEliminationMeaning (data assembly) (QuotientProducts.products assembly.declarations) := by
  intro n source domain function argument codomain family semanticFunction semanticArgument
    _ meaning functionAdmitted argumentAdmitted functionMeaning argumentMeaning
  obtain ⟨actualDomain, actualCodomain, rfl, rfl, same⟩ := family_representation family meaning
  cases eq_of_heq same
  have resultType := instantiated_type_meaning source actualDomain actualCodomain argument
    semanticArgument argumentAdmitted argumentMeaning
  refine ⟨resultType, meaning_of_code_conversion ?_ resultType ?_⟩
  · exact ⟨source.formed, .appElim functionAdmitted.typing argumentAdmitted.typing⟩
  · exact .trans _ _ _ (QuotientProducts.app_represents semanticFunction semanticArgument)
      (Conv.congApp (code_conversion_of_meaning functionMeaning) (code_conversion_of_meaning argumentMeaning))

theorem sigma_introduction_meaning :
    SigmaIntroductionMeaning (data assembly) (QuotientProducts.sums assembly.declarations) := by
  intro n source domain first second codomain family semanticFirst semanticSecond
    admitted meaning firstAdmitted secondAdmitted firstMeaning secondMeaning
  obtain ⟨actualDomain, actualCodomain, rfl, rfl, same⟩ := family_representation family meaning
  cases eq_of_heq same
  apply meaning_of_code_conversion
  · exact ⟨source.formed, .pairIntro (QuotientProducts.nativeSigma actualDomain actualCodomain).formed
      (QuotientProducts.nativeSigma actualDomain actualCodomain).universeWitness
      firstAdmitted.typing secondAdmitted.typing⟩
  · exact sigma_formation_meaning n source _ _ _ admitted meaning
  · exact .trans _ _ _ (QuotientProducts.pair_represents
      (codomain := (canonicalFamily source actualDomain actualCodomain).semanticCodomain)
      semanticFirst semanticSecond)
      (Conv.congPair (code_conversion_of_meaning firstMeaning) (code_conversion_of_meaning secondMeaning))

theorem sigma_elimination_meaning :
    SigmaEliminationMeaning (data assembly) (QuotientProducts.sums assembly.declarations) := by
  intro n source domain pair codomain family semanticPair _ meaning pairAdmitted pairMeaning
  obtain ⟨actualDomain, actualCodomain, rfl, rfl, same⟩ := family_representation family meaning
  cases eq_of_heq same
  have firstAdmitted : Judgment assembly.rules source.raw (.fst pair) actualDomain.code :=
    ⟨source.formed, .fstElim pairAdmitted.typing⟩
  have firstMeaning : (data assembly).term source (.fst pair) actualDomain.code (QType.mk actualDomain)
      (QuotientProducts.fst semanticPair) := by
    apply meaning_of_code_conversion firstAdmitted meaning.1
    exact .trans _ _ _ (QuotientProducts.fst_represents semanticPair)
      (Conv.mapCompatible Tm.fst (fun step => .congFst step) (code_conversion_of_meaning pairMeaning))
  have resultType := instantiated_type_meaning source actualDomain actualCodomain (.fst pair)
    (QuotientProducts.fst semanticPair) firstAdmitted firstMeaning
  refine ⟨firstMeaning, resultType, meaning_of_code_conversion ?_ resultType ?_⟩
  · exact ⟨source.formed, .sndElim pairAdmitted.typing⟩
  · exact .trans _ _ _ (QuotientProducts.snd_represents semanticPair)
      (Conv.mapCompatible Tm.snd (fun step => .congSnd step) (code_conversion_of_meaning pairMeaning))

theorem pi_beta :
    AdmittedPiBeta (data assembly) (QuotientProducts.products assembly.declarations) :=
  admittedPiBeta_of_full (data assembly) (QuotientProducts.products assembly.declarations)
    (QuotientProducts.pi_beta assembly.declarations)

theorem sigma_beta :
    AdmittedSigmaBeta (data assembly) (QuotientProducts.sums assembly.declarations) :=
  admittedSigmaBeta_of_full (data assembly) (QuotientProducts.sums assembly.declarations)
    (QuotientProducts.sigma_beta assembly.declarations)

#print axioms code_conversion_of_meaning
#print axioms meaning_of_code_conversion
#print axioms pi_formation_meaning
#print axioms sigma_formation_meaning
#print axioms instantiated_type_meaning
#print axioms pi_introduction_meaning
#print axioms pi_elimination_meaning
#print axioms sigma_introduction_meaning
#print axioms sigma_elimination_meaning
#print axioms pi_beta
#print axioms sigma_beta

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientProducts
