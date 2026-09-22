import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientInterpretation

/-!
# Uniqueness of the admitted comprehension comparison

The actual substitution graph fixes the base projection. The actual term
graph fixes the newest variable even when its dependent annotations are
presented differently. Together these determine the comprehension map;
the inverse equations then determine its inverse. Consequently every
qualified native family has the canonical quotient representation, without
identifying distinct raw context objects or discarding source expressions.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientComprehension

open _root_.CategoryTheory
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation FormationSensitive SharedJudgmentFragment
open FormationSensitiveContextual SharedJudgmentQuotientInterpretation
open SharedJudgmentTypeInterpretation

variable {assembly : Assembly}

private theorem inverse_unique {C : Type} [Category C] {source target : C}
    {first second : source ⟶ target} {firstInverse secondInverse : target ⟶ source}
    (same : first = second) (left : firstInverse ≫ first = 𝟙 target)
    (right : second ≫ secondInverse = 𝟙 source) : firstInverse = secondInverse := by
  calc
    firstInverse = firstInverse ≫ (second ≫ secondInverse) := by
      rw [right, Category.comp_id]
    _ = (firstInverse ≫ first) ≫ secondInverse := by rw [same, Category.assoc]
    _ = secondInverse := by rw [left, Category.id_comp]

private theorem type_inverse {Head : Type} {rules : Rules Head}
    {source target : QuotientCwf.QContext rules} (iso : source ≅ target)
    (family : QuotientCwf.Ty source) :
    QuotientCwf.tySub (QuotientCwf.tySub family iso.inv) iso.hom = family := by
  rw [← QuotientCwf.tySub_comp, iso.hom_inv_id, QuotientCwf.tySub_id]

theorem substitution_meaning_unique {n m : Nat}
    {source : SharedJudgmentInterpretation.Context assembly n}
    {target : SharedJudgmentInterpretation.Context assembly m}
    {sigma : Sub Tower.Head n m}
    {first second : (QuotientCwf.cwf assembly.rules).Sub
      ((data assembly).ctx target) ((data assembly).ctx source)}
    (firstMeaning : (data assembly).sub source target sigma first)
    (secondMeaning : (data assembly).sub source target sigma second) : first = second := by
  obtain ⟨firstTyped, rfl⟩ := firstMeaning
  obtain ⟨secondTyped, rfl⟩ := secondMeaning
  rfl

/-- The total term class is functional before identifying its dependent
semantic type indices. Both source annotation and source term are fixed. -/
theorem term_meaning_value_unique {n : Nat}
    {source : SharedJudgmentInterpretation.Context assembly n}
    {term annotation : Tower.Tm n}
    {firstType secondType : (QuotientCwf.cwf assembly.rules).Ty ((data assembly).ctx source)}
    {first : (QuotientCwf.cwf assembly.rules).Tm ((data assembly).ctx source) firstType}
    {second : (QuotientCwf.cwf assembly.rules).Tm ((data assembly).ctx source) secondType}
    (firstMeaning : (data assembly).term source term annotation firstType first)
    (secondMeaning : (data assembly).term source term annotation secondType second) :
    first.val = second.val := by
  obtain ⟨firstAnnotation, firstCode, firstTerm, firstTermCode, _, firstValue⟩ := firstMeaning
  obtain ⟨secondAnnotation, secondCode, secondTerm, secondTermCode, _, secondValue⟩ := secondMeaning
  rw [← firstValue, ← secondValue]
  apply (QTerm.mk_eq_iff firstTerm secondTerm).mpr
  constructor
  · rw [firstCode, secondCode]
    exact .refl _
  · rw [firstTermCode, secondTermCode]
    exact .refl _

theorem comparison_forward_unique {n : Nat}
    {source : SharedJudgmentInterpretation.Context assembly n} {type : Tower.Tm n}
    {extendedFormed : ContextFormation assembly.rules (.snoc source.raw type)}
    {semanticType : (QuotientCwf.cwf assembly.rules).Ty ((data assembly).ctx source)}
    {first second : ContextComparison (QuotientCwf.cwf assembly.rules)
      ((data assembly).ctx ⟨.snoc source.raw type, extendedFormed⟩)
      ((QuotientCwf.cwf assembly.rules).ext ((data assembly).ctx source) semanticType)}
    (firstMeaning : ComprehensionMeaning (data assembly) source type extendedFormed semanticType first)
    (secondMeaning : ComprehensionMeaning (data assembly) source type extendedFormed semanticType second) :
    first.forward = second.forward := by
  apply QuotientCwf.pair_unique semanticType
  · exact substitution_meaning_unique firstMeaning.2.1 secondMeaning.2.1
  · exact term_meaning_value_unique firstMeaning.2.2.2 secondMeaning.2.2.2

/-- This uniqueness uses both the projection and newest-variable laws;
the inverse equations alone would permit arbitrary context automorphisms. -/
theorem comparison_unique {n : Nat}
    {source : SharedJudgmentInterpretation.Context assembly n} {type : Tower.Tm n}
    {extendedFormed : ContextFormation assembly.rules (.snoc source.raw type)}
    {semanticType : (QuotientCwf.cwf assembly.rules).Ty ((data assembly).ctx source)}
    {first second : ContextComparison (QuotientCwf.cwf assembly.rules)
      ((data assembly).ctx ⟨.snoc source.raw type, extendedFormed⟩)
      ((QuotientCwf.cwf assembly.rules).ext ((data assembly).ctx source) semanticType)}
    (firstMeaning : ComprehensionMeaning (data assembly) source type extendedFormed semanticType first)
    (secondMeaning : ComprehensionMeaning (data assembly) source type extendedFormed semanticType second) :
    first = second := by
  have forwardSame := comparison_forward_unique firstMeaning secondMeaning
  have backwardSame : first.backward = second.backward := by
    exact inverse_unique forwardSame firstMeaning.1.1 secondMeaning.1.2
  cases first
  cases second
  cases forwardSame
  cases backwardSame
  rfl

noncomputable def canonicalFamily {n : Nat}
    (source : SharedJudgmentInterpretation.Context assembly n)
    (domain : TypeOver (context source))
    (codomain : TypeOver (extend (context source) domain)) :
    Family (data assembly) source domain.code codomain.code where
  contextFormation := .snoc source.formed domain.formed domain.universeWitness
  semanticDomain := QType.mk domain
  semanticCodomain := QuotientCwf.tySub (QType.mk codomain)
    (QuotientCwf.extPresentation (context source) domain).hom
  comparison := comparison source domain

theorem canonical_family_meaning {n : Nat}
    (source : SharedJudgmentInterpretation.Context assembly n)
    (domain : TypeOver (context source))
    (codomain : TypeOver (extend (context source) domain)) :
    FamilyMeaning (data assembly) (canonicalFamily source domain codomain) :=
  ⟨QuotientInterpretation.type_meaning (context source) domain,
    comprehension_meaning source domain,
    QuotientInterpretation.family_comparison (context source) domain codomain⟩

/-- Every independently qualified family is represented by actual native
types through the canonical comparison. The witnesses may have different
formation levels; only their admitted codes and quotient classes matter. -/
theorem family_representation {n : Nat}
    {source : SharedJudgmentInterpretation.Context assembly n}
    {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    (family : Family (data assembly) source domain codomain)
    (meaning : FamilyMeaning (data assembly) family) :
    ∃ actualDomain : TypeOver (context source),
      ∃ actualCodomain : TypeOver (extend (context source) actualDomain),
        actualDomain.code = domain ∧ actualCodomain.code = codomain ∧
          HEq family (canonicalFamily source actualDomain actualCodomain) := by
  rcases family with ⟨formed, semanticDomain, semanticCodomain, familyComparison⟩
  rcases meaning with ⟨⟨actualDomain, rfl, rfl⟩, comparisonMeaning, codomainMeaning⟩
  have sameComparison := comparison_unique comparisonMeaning (comprehension_meaning source actualDomain)
  cases sameComparison
  change QuotientInterpretation.TypeMeaning (extend (context source) actualDomain) codomain
    (QuotientCwf.tySub semanticCodomain
      (QuotientCwf.extPresentation (context source) actualDomain).inv) at codomainMeaning
  rcases codomainMeaning with ⟨actualCodomain, rfl, represented⟩
  have sameCodomain : semanticCodomain = QuotientCwf.tySub (QType.mk actualCodomain)
      (QuotientCwf.extPresentation (context source) actualDomain).hom := by
    exact (type_inverse (QuotientCwf.extPresentation (context source) actualDomain)
      semanticCodomain).symm.trans
      (congrArg (fun value => QuotientCwf.tySub value
        (QuotientCwf.extPresentation (context source) actualDomain).hom) represented.symm)
  cases sameCodomain
  exact ⟨actualDomain, actualCodomain, rfl, rfl, HEq.rfl⟩

#print axioms substitution_meaning_unique
#print axioms term_meaning_value_unique
#print axioms comparison_forward_unique
#print axioms comparison_unique
#print axioms family_representation

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientComprehension
