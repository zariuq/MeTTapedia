import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentTypeInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeQuotientInterpretationControls

/-!
# The formed native quotient in the shared interpretation interface

The context map and all three meaning relations below are the graphs of the
actual formed presentation and its conversion quotient. The independent
shared admission, substitution and conversion predicates are proved of that
same data. No semantic value is assigned to an unformed raw telescope.

This is a structural syntactic interpretation, not an external set model,
an operational-presheaf comparison, or a selection of an identity policy.
Raw terms and proof records remain in the source; their chosen conversion
classes are one explicitly named semantic observation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientInterpretation

open _root_.CategoryTheory
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation FormationSensitive SharedJudgmentFragment

open FormationSensitiveContextual

variable {assembly : Assembly}

abbrev context {n : Nat} (source : SharedJudgmentInterpretation.Context assembly n) : FormationSensitiveContextual.Context assembly.rules :=
  ⟨n, source.raw, source.formed⟩

/-- Each field uses the actual native quotient projection. This is not a
constant interpretation of contexts, types, terms, or substitutions. -/
noncomputable def data (assembly : Assembly) :
    SharedJudgmentInterpretation.Data assembly (QuotientCwf.cwf assembly.rules) where
  ctx source := (FormationSensitiveContextual.quotientProjection assembly.rules).obj (context source)
  ty source := QuotientInterpretation.TypeMeaning (context source)
  term source := QuotientInterpretation.TermMeaning (context source)
  sub source target := QuotientInterpretation.SubstitutionMeaning (context source) (context target)

theorem admitted_total : SharedJudgmentInterpretation.AdmittedTotal (data assembly) := by
  intro n source term type admitted
  exact (QuotientInterpretation.admitted_iff_interpreted (context source)
    OpaqueRelatorExtension.universes term type).mp admitted

/-- Coverage reflects admission too; arbitrary semantic graph witnesses
cannot admit an untyped native term. -/
theorem admitted_iff_meaning {n : Nat} (source : SharedJudgmentInterpretation.Context assembly n)
    (term type : Tower.Tm n) :
    Judgment assembly.rules source.raw term type ↔
      ∃ semanticType, (data assembly).ty source type semanticType ∧
        ∃ value, (data assembly).term source term type semanticType value :=
  QuotientInterpretation.admitted_iff_interpreted (context source) OpaqueRelatorExtension.universes term type

theorem substitutions_total : SharedJudgmentInterpretation.AdmittedSubstitutionsTotal (data assembly) := by
  intro n m source target sigma _ typed
  exact QuotientInterpretation.substitutions_total (context source) (context target) sigma typed

theorem substitution_constructors : SharedJudgmentInterpretation.SubstitutionConstructors (data assembly) := by
  constructor
  · intro n source _
    exact QuotientInterpretation.substitution_identity (context source)
  · intro n m k first middle last sigma tau semanticSigma semanticTau earlier later
    exact QuotientInterpretation.substitution_composition earlier later

theorem substitution_stable : SharedJudgmentInterpretation.SubstitutionStable (data assembly) := by
  constructor
  · intro n m source target sigma semantic type semanticType _ _ arrow meaning
    exact QuotientInterpretation.type_substitution arrow meaning
  · intro n m source target sigma semantic term type semanticType value _ _ _ arrow _ meaning
    exact QuotientInterpretation.term_substitution arrow meaning

/-- Independent target formation supplies the target class representative;
the conversion receipt alone does not supply a formation derivation. -/
theorem type_conversion_invariant : SharedJudgmentInterpretation.TypeConversionInvariant (data assembly) := by
  intro n source sortHead left right semanticType universeWitness converted
  let leftType : FormationSensitiveContextual.TypeOver (context source) :=
    ⟨left.val, sortHead, universeWitness, left.property.typing⟩
  let rightType : FormationSensitiveContextual.TypeOver (context source) :=
    ⟨right.val, sortHead, universeWitness, right.property.typing⟩
  exact ⟨fun meaning => QuotientInterpretation.type_conversion meaning rightType converted,
    fun meaning => QuotientInterpretation.type_conversion meaning leftType converted.symm⟩

private theorem transport_meaning {n : Nat} {source : SharedJudgmentInterpretation.Context assembly n}
    {term annotation next nextAnnotation : Tower.Tm n}
    {semanticType : (QuotientCwf.cwf assembly.rules).Ty ((data assembly).ctx source)}
    {value : (QuotientCwf.cwf assembly.rules).Tm ((data assembly).ctx source) semanticType}
    (meaning : (data assembly).term source term annotation semanticType value)
    (target : Judgment assembly.rules source.raw next nextAnnotation)
    (typeConversion : Conv assembly.rules.headEq annotation nextAnnotation assembly.rules.computation)
    (termConversion : Conv assembly.rules.headEq term next assembly.rules.computation) :
    (data assembly).term source next nextAnnotation semanticType value := by
  obtain ⟨sortHead, universeWitness, formed⟩ := target.regularity OpaqueRelatorExtension.universes
  let targetType : FormationSensitiveContextual.TypeOver (context source) :=
    ⟨nextAnnotation, sortHead, universeWitness, formed.typing⟩
  let targetTerm : FormationSensitiveContextual.Term (context source) targetType := ⟨next, target.typing⟩
  exact QuotientInterpretation.term_and_annotation_conversion meaning targetTerm typeConversion termConversion

theorem term_conversion_invariant : SharedJudgmentInterpretation.TermConversionInvariant (data assembly) := by
  intro n source type left right semanticType value converted
  exact ⟨fun meaning => transport_meaning meaning right.property (.refl _) converted,
    fun meaning => transport_meaning meaning left.property (.refl _) converted.symm⟩

theorem conversion_invariant : SharedJudgmentInterpretation.ConversionInvariant (data assembly) :=
  ⟨type_conversion_invariant, term_conversion_invariant⟩

theorem annotation_transport : SharedJudgmentInterpretation.AnnotationTransport (data assembly) := by
  intro n source term first last semanticType value sourceAdmitted targetAdmitted _ _ converted
  exact ⟨fun meaning => transport_meaning meaning targetAdmitted converted (.refl _),
    fun meaning => transport_meaning meaning sourceAdmitted converted.symm (.refl _)⟩

theorem development_invariant (opacity : OpaqueRelatorExtension.Opacity assembly.declarations) :
    SharedJudgmentInterpretation.DevelopmentInvariant (data assembly) :=
  (SharedJudgmentInterpretation.conversion_invariant_iff_development_invariant opacity _).mp conversion_invariant

theorem conversion_rule_sound (opacity : OpaqueRelatorExtension.Opacity assembly.declarations) :
    SharedJudgmentInterpretation.ConversionRuleSound (data assembly) :=
  (SharedJudgmentInterpretation.conversion_rule_sound_iff_annotation_transport opacity _
    (development_invariant opacity).1).mpr annotation_transport

/-- One native annotation determines its actual semantic type class, not
an arbitrary carrier merely isomorphic to it. -/
theorem type_meaning_unique {n : Nat} {source : SharedJudgmentInterpretation.Context assembly n}
    {code : Tower.Tm n} {first second : (QuotientCwf.cwf assembly.rules).Ty ((data assembly).ctx source)}
    (firstMeaning : (data assembly).ty source code first)
    (secondMeaning : (data assembly).ty source code second) : first = second := by
  obtain ⟨firstType, firstCode, rfl⟩ := firstMeaning
  obtain ⟨secondType, secondCode, rfl⟩ := secondMeaning
  apply (FormationSensitiveContextual.QType.mk_eq_iff firstType secondType).mpr
  rw [firstCode, secondCode]
  exact .refl _

/-- Functionality is scoped to one retained native term and annotation.
It does not equate distinct proof objects in the source language. -/
theorem term_meaning_unique {n : Nat} {source : SharedJudgmentInterpretation.Context assembly n}
    {term annotation : Tower.Tm n}
    {semanticType : (QuotientCwf.cwf assembly.rules).Ty ((data assembly).ctx source)}
    {first second : (QuotientCwf.cwf assembly.rules).Tm ((data assembly).ctx source) semanticType}
    (firstMeaning : (data assembly).term source term annotation semanticType first)
    (secondMeaning : (data assembly).term source term annotation semanticType second) :
    first = second := by
  obtain ⟨firstType, firstAnnotation, firstTerm, firstCode, _, firstValue⟩ := firstMeaning
  obtain ⟨secondType, secondAnnotation, secondTerm, secondCode, _, secondValue⟩ := secondMeaning
  apply Subtype.ext
  rw [← firstValue, ← secondValue]
  apply (FormationSensitiveContextual.QTerm.mk_eq_iff firstTerm secondTerm).mpr
  constructor
  · rw [firstAnnotation, secondAnnotation]
    exact .refl _
  · rw [firstCode, secondCode]
    exact .refl _

/-! ## Actual dependent comprehension, without strict context equality -/

noncomputable def comparison {n : Nat} (source : SharedJudgmentInterpretation.Context assembly n)
    (type : FormationSensitiveContextual.TypeOver (context source)) :
    SharedJudgmentTypeInterpretation.ContextComparison (QuotientCwf.cwf assembly.rules)
      ((data assembly).ctx ⟨.snoc source.raw type.code,
        .snoc source.formed type.formed type.universeWitness⟩)
      ((QuotientCwf.cwf assembly.rules).ext ((data assembly).ctx source) (QType.mk type)) where
  forward := (QuotientCwf.extPresentation (context source) type).inv
  backward := (QuotientCwf.extPresentation (context source) type).hom

theorem comprehension_meaning {n : Nat} (source : SharedJudgmentInterpretation.Context assembly n)
    (type : FormationSensitiveContextual.TypeOver (context source)) :
    SharedJudgmentTypeInterpretation.ComprehensionMeaning (data assembly) source type.code
      (.snoc source.formed type.formed type.universeWitness) (QType.mk type)
      (comparison source type) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (QuotientCwf.extPresentation (context source) type).hom_inv_id
  · exact (QuotientCwf.extPresentation (context source) type).inv_hom_id
  · exact QuotientInterpretation.comprehension_projection (context source) type
  · exact QuotientInterpretation.comprehension_type (context source) type
  · exact QuotientInterpretation.comprehension_variable (context source) type

theorem comprehension_coverage : SharedJudgmentTypeInterpretation.ComprehensionCoverage (data assembly) := by
  intro n source type sortHead semanticType admitted universeWitness meaning
  obtain ⟨actual, rfl, rfl⟩ := meaning
  exact ⟨comparison source actual, comprehension_meaning source actual⟩

/-- Every independently formed dependent native family is carried through
the actual comprehension comparison, including variable-dependent ones. -/
theorem family_coverage : SharedJudgmentTypeInterpretation.FamilyCoverage (data assembly) := by
  intro n source domain codomain admitted
  obtain ⟨lower, upper, result, domainAdmitted, domainUniverse, codomainAdmitted,
    codomainUniverse, _⟩ := admitted
  let actualDomain : FormationSensitiveContextual.TypeOver (context source) :=
    ⟨domain, lower, domainUniverse, domainAdmitted.typing⟩
  let actualCodomain : FormationSensitiveContextual.TypeOver (extend (context source) actualDomain) :=
    ⟨codomain, upper, codomainUniverse, codomainAdmitted.typing⟩
  let family : SharedJudgmentTypeInterpretation.Family (data assembly) source domain codomain := {
    contextFormation := .snoc source.formed domainAdmitted.typing domainUniverse
    semanticDomain := QType.mk actualDomain
    semanticCodomain := QuotientCwf.tySub (QType.mk actualCodomain)
      (QuotientCwf.extPresentation (context source) actualDomain).hom
    comparison := comparison source actualDomain }
  refine ⟨family, ?_, ?_, ?_⟩
  · exact QuotientInterpretation.type_meaning (context source) actualDomain
  · exact comprehension_meaning source actualDomain
  · exact QuotientInterpretation.family_comparison (context source) actualDomain actualCodomain

namespace Controls

/-- The existing mixed HOL-list/wire computation has an actual value in
the shared interpretation. No arbitrary native-to-semantic relation remains. -/
theorem mixed_projection_meaning (wire : NativeWireData.Wire) :
    (data common).term .nil (.snd (HOLNativeRelatorCompatibility.mixedPayload wire))
      NativeWireData.dataType QuotientCwf.Controls.wireType (QuotientCwf.Controls.result wire) :=
  QuotientInterpretation.Controls.mixed_projection_meaning wire

theorem mixed_projection_changed_meaning :
    ¬ (data common).term .nil
      (.snd (HOLNativeRelatorCompatibility.mixedPayload (.natural 7)))
      NativeWireData.dataType QuotientCwf.Controls.wireType
      (QuotientCwf.Controls.result (.natural 8)) := by
  intro changed
  exact QuotientCwf.Controls.seven_is_not_eight
    (term_meaning_unique (mixed_projection_meaning (.natural 7)) changed)

/-- Conversion transports the real computed value across a different
formed annotation while its source spelling remains distinct. -/
theorem mixed_projection_across_annotation (wire : NativeWireData.Wire) :
    (data common).term .nil (.snd (HOLNativeRelatorCompatibility.mixedPayload wire))
      SharedJudgmentInterpretation.Controls.betaDataType QuotientCwf.Controls.wireType
      (QuotientCwf.Controls.result wire) ∧
    (SharedJudgmentInterpretation.Controls.betaDataType : Tower.Tm 0) ≠
      NativeWireData.dataType := by
  refine ⟨?_, SharedJudgmentInterpretation.Controls.beta_data_type_ne⟩
  exact transport_meaning (mixed_projection_meaning wire)
    (SharedJudgmentInterpretation.Controls.mixed_projection_beta_admitted wire)
    SharedJudgmentInterpretation.Controls.beta_data_type_converts.symm (.refl _)

end Controls

#print axioms admitted_total
#print axioms admitted_iff_meaning
#print axioms substitutions_total
#print axioms substitution_constructors
#print axioms substitution_stable
#print axioms conversion_invariant
#print axioms annotation_transport
#print axioms conversion_rule_sound
#print axioms type_meaning_unique
#print axioms term_meaning_unique
#print axioms comprehension_coverage
#print axioms family_coverage
#print axioms Controls.mixed_projection_meaning
#print axioms Controls.mixed_projection_changed_meaning
#print axioms Controls.mixed_projection_across_annotation

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientInterpretation
