import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientCwf

/-! # Interpretation in the formed conversion quotient

The construction is parameterized by the declared rules and uses the existing
formation, substitution and conversion judgments. Concrete language controls
are separate consumers, not premises of these laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientInterpretation

open _root_.CategoryTheory FormationSensitive

variable {Head : Type} {rules : Rules Head}

/-- A native annotation is represented by its actual formed conversion
class. The selected formation level is not recovered from that class. -/
def TypeMeaning (context : Context rules) (code : Tm Head context.arity)
    (type : QType context) : Prop :=
  ∃ actual : TypeOver context, actual.code = code ∧ QType.mk actual = type

/-- Both the native annotation and term are retained in the graph before
their actual conversion classes are compared with the semantic fibre. -/
def TermMeaning (context : Context rules) (code annotation : Tm Head context.arity)
    (type : QType context) (value : TermFibre type) : Prop :=
  ∃ actualType : TypeOver context, actualType.code = annotation ∧
    ∃ actual : Term context actualType, actual.code = code ∧
      QType.mk actualType = type ∧ QTerm.mk actual = value.val

/-- The semantic arrow comes from this very admitted native substitution.
Both endpoints already carry their independent context formation. -/
def SubstitutionMeaning (source target : Context rules)
    (substitution : Sub Head source.arity target.arity)
    (semantic : (quotientProjection rules).obj target ⟶ (quotientProjection rules).obj source) : Prop :=
  ∃ typed : FormationSensitive.CtxMor rules source.raw target.raw substitution,
    QuotientCwf.project (⟨substitution, typed⟩ : target ⟶ source) = semantic

theorem type_meaning (context : Context rules) (type : TypeOver context) :
    TypeMeaning context type.code (QType.mk type) := ⟨type, rfl, rfl⟩

theorem term_meaning (context : Context rules) {type : TypeOver context} (term : Term context type) :
    TermMeaning context term.code type.code (QType.mk type) (TermFibre.mk term) :=
  ⟨type, rfl, term, rfl, rfl, rfl⟩

/-- Coverage includes every actual native judgment, not a finite selected
subtype. Regularity provides its independently formed result annotation. -/
theorem admitted_iff_interpreted (context : Context rules) (regular : UniverseRegularity rules)
    (term type : Tm Head context.arity) :
    Judgment rules context.raw term type ↔
      ∃ semanticType : QType context, TypeMeaning context type semanticType ∧
        ∃ value : TermFibre semanticType, TermMeaning context term type semanticType value := by
  constructor
  · intro admitted
    obtain ⟨actualType, sameType, actual, sameTerm⟩ :=
      (judgment_iff_term context regular term type).mp admitted
    exact ⟨QType.mk actualType, ⟨actualType, sameType, rfl⟩,
      TermFibre.mk actual, actualType, sameType, actual, sameTerm, rfl, rfl⟩
  · rintro ⟨_, _, _, actualType, sameType, actual, sameTerm, _, _⟩
    simpa only [sameType, sameTerm] using actual.judgment

theorem substitutions_total (source target : Context rules)
    (substitution : Sub Head source.arity target.arity)
    (typed : FormationSensitive.CtxMor rules source.raw target.raw substitution) :
    ∃ semantic, SubstitutionMeaning source target substitution semantic :=
  ⟨QuotientCwf.project (⟨substitution, typed⟩ : target ⟶ source), typed, rfl⟩

theorem substitution_identity (context : Context rules) :
    SubstitutionMeaning context context ids (𝟙 (quotientProjection rules).obj context) := by
  refine ⟨identityTyped context.raw, ?_⟩
  exact (quotientProjection rules).map_id context

theorem substitution_composition {first middle last : Context rules}
    {earlier : Sub Head first.arity middle.arity} {later : Sub Head middle.arity last.arity}
    {semanticEarlier : (quotientProjection rules).obj middle ⟶ (quotientProjection rules).obj first}
    {semanticLater : (quotientProjection rules).obj last ⟶ (quotientProjection rules).obj middle}
    (firstMeaning : SubstitutionMeaning first middle earlier semanticEarlier)
    (secondMeaning : SubstitutionMeaning middle last later semanticLater) :
    SubstitutionMeaning first last (subComp later earlier) (semanticLater ≫ semanticEarlier) := by
  obtain ⟨firstTyped, rfl⟩ := firstMeaning
  obtain ⟨secondTyped, rfl⟩ := secondMeaning
  refine ⟨compositionTyped secondTyped firstTyped, ?_⟩
  exact (quotientProjection rules).map_comp
    (⟨later, secondTyped⟩ : last ⟶ middle) (⟨earlier, firstTyped⟩ : middle ⟶ first)

theorem type_substitution {source target : Context rules}
    {substitution : Sub Head source.arity target.arity}
    {semantic : (quotientProjection rules).obj target ⟶ (quotientProjection rules).obj source}
    {code : Tm Head source.arity} {type : QType source}
    (arrow : SubstitutionMeaning source target substitution semantic)
    (meaning : TypeMeaning source code type) :
    TypeMeaning target (subst substitution code) (QuotientCwf.tySub type semantic) := by
  obtain ⟨typed, rfl⟩ := arrow
  obtain ⟨actual, rfl, rfl⟩ := meaning
  exact ⟨actual.reindex ⟨substitution, typed⟩, rfl, rfl⟩

theorem term_substitution {source target : Context rules}
    {substitution : Sub Head source.arity target.arity}
    {semantic : (quotientProjection rules).obj target ⟶ (quotientProjection rules).obj source}
    {code annotation : Tm Head source.arity} {type : QType source} {value : TermFibre type}
    (arrow : SubstitutionMeaning source target substitution semantic)
    (meaning : TermMeaning source code annotation type value) :
    TermMeaning target (subst substitution code) (subst substitution annotation)
      (QuotientCwf.tySub type semantic) (QuotientCwf.tmSub value semantic) := by
  obtain ⟨typed, rfl⟩ := arrow
  obtain ⟨actualType, rfl, actual, rfl, sameType, sameValue⟩ := meaning
  let morphism : target ⟶ source := ⟨substitution, typed⟩
  refine ⟨actualType.reindex morphism, rfl, actual.reindex morphism, rfl, ?_, ?_⟩
  · exact congrArg (fun type => type.reindex morphism) sameType
  · exact congrArg (fun value => value.reindex morphism) sameValue

/-- Independently formed convertible annotations have the same class even
if their original formation-level witnesses differ. -/
theorem type_conversion {context : Context rules} {code : Tm Head context.arity}
    {semanticType : QType context} (meaning : TypeMeaning context code semanticType)
    (target : TypeOver context)
    (converted : Conv rules.headEq code target.code rules.computation) :
    TypeMeaning context target.code semanticType := by
  obtain ⟨source, rfl, same⟩ := meaning
  exact ⟨target, rfl, ((QType.mk_eq_iff target source).mpr converted.symm).trans same⟩

/-- The source and target terms and annotations are genuinely admitted;
their joint conversion transports the very same semantic term value. -/
theorem term_and_annotation_conversion {context : Context rules}
    {code annotation : Tm Head context.arity} {semanticType : QType context}
    {value : TermFibre semanticType} (meaning : TermMeaning context code annotation semanticType value)
    {targetType : TypeOver context} (target : Term context targetType)
    (typeConversion : Conv rules.headEq annotation targetType.code rules.computation)
    (termConversion : Conv rules.headEq code target.code rules.computation) :
    TermMeaning context target.code targetType.code semanticType value := by
  obtain ⟨sourceType, rfl, source, rfl, sameType, sameValue⟩ := meaning
  exact ⟨targetType, rfl, target, rfl,
    ((QType.mk_eq_iff targetType sourceType).mpr typeConversion.symm).trans sameType,
    ((QTerm.mk_eq_iff target source).mpr ⟨typeConversion.symm, termConversion.symm⟩).trans sameValue⟩

/-! ## Comprehension through the actual comparison isomorphism -/

theorem comprehension_projection_comparison (context : Context rules) (type : TypeOver context) :
    (QuotientCwf.extPresentation context type).inv ≫ QuotientCwf.wk (QType.mk type) =
      QuotientCwf.project (projectionHom context type) := by
  rw [← QuotientCwf.extPresentation_projection context type]
  exact (QuotientCwf.extPresentation context type).inv_hom_id_assoc _

/-- The actual native weakening is the model projection after comparison;
neither extension object is replaced by an equality of raw annotations. -/
theorem comprehension_projection (context : Context rules) (type : TypeOver context) :
    SubstitutionMeaning context (extend context type) projection
      ((QuotientCwf.extPresentation context type).inv ≫ QuotientCwf.wk (QType.mk type)) :=
  ⟨(projectionHom context type).typed, (comprehension_projection_comparison context type).symm⟩

theorem comprehension_type_class (context : Context rules) (type : TypeOver context) :
    QType.mk (type.reindex (projectionHom context type)) =
      QuotientCwf.tySub (QuotientCwf.tySub (QType.mk type) (QuotientCwf.wk (QType.mk type)))
        (QuotientCwf.extPresentation context type).inv := by
  exact (congrArg (fun arrow => QuotientCwf.tySub (QType.mk type) arrow)
    (comprehension_projection_comparison context type)).symm.trans
      (QuotientCwf.tySub_comp (QType.mk type)
        (QuotientCwf.extPresentation context type).inv (QuotientCwf.wk (QType.mk type)))

theorem comprehension_type (context : Context rules) (type : TypeOver context) :
    TypeMeaning (extend context type) (rename wk type.code)
      (QuotientCwf.tySub (QuotientCwf.tySub (QType.mk type) (QuotientCwf.wk (QType.mk type)))
        (QuotientCwf.extPresentation context type).inv) :=
  ⟨type.reindex (projectionHom context type), subst_projection _,
    comprehension_type_class context type⟩

/-- The newest native variable has exactly the compared semantic variable,
including its dependent annotation; raw term code remains `var 0`. -/
theorem comprehension_variable (context : Context rules) (type : TypeOver context) :
    TermMeaning (extend context type) (.var 0) (rename wk type.code)
      (QuotientCwf.tySub (QuotientCwf.tySub (QType.mk type) (QuotientCwf.wk (QType.mk type)))
        (QuotientCwf.extPresentation context type).inv)
      (QuotientCwf.tmSub (QuotientCwf.vz (QType.mk type))
        (QuotientCwf.extPresentation context type).inv) := by
  refine ⟨type.reindex (projectionHom context type), subst_projection _,
    newest context type, rfl, comprehension_type_class context type, ?_⟩
  let selected := QuotientCwf.typeRepresentative (QType.mk type)
  let converted := (QType.mk_eq_iff selected type).mp
    (QuotientCwf.typeRepresentative_class (QType.mk type))
  change QTerm.mk (newest context type) =
    QTerm.mk ((newest context selected).reindex (extensionComparison selected type converted).inv)
  apply (QTerm.mk_eq_iff _ _).mpr
  constructor
  · change Conv rules.headEq (subst projection type.code)
      (subst ids (subst projection selected.code)) rules.computation
    rw [subst_ids]
    exact Conv.substitute projection converted.symm
  · change Conv rules.headEq (.var 0) (subst ids (.var 0)) rules.computation
    rw [subst_ids]
    exact .refl _

/-- Every independently formed native family over the actual extension
transports to the model extension and back. This is coverage of native
families, not an assumption about an ambient collection of semantic sets. -/
theorem family_comparison (context : Context rules) (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    TypeMeaning (extend context domain) codomain.code
      (QuotientCwf.tySub
        (QuotientCwf.tySub (QType.mk codomain) (QuotientCwf.extPresentation context domain).hom)
        (QuotientCwf.extPresentation context domain).inv) := by
  refine ⟨codomain, rfl, ?_⟩
  exact (QuotientCwf.tySub_id (QType.mk codomain)).symm.trans
    ((congrArg (fun arrow => QuotientCwf.tySub (QType.mk codomain) arrow)
      (QuotientCwf.extPresentation context domain).inv_hom_id).symm.trans
        (QuotientCwf.tySub_comp (QType.mk codomain)
          (QuotientCwf.extPresentation context domain).inv
          (QuotientCwf.extPresentation context domain).hom))

theorem family_coverage (context : Context rules) (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    ∃ semanticCodomain : QuotientCwf.Ty
        (QuotientCwf.ext ((quotientProjection rules).obj context) (QType.mk domain)),
      TypeMeaning (extend context domain) codomain.code
        (QuotientCwf.tySub semanticCodomain (QuotientCwf.extPresentation context domain).inv) :=
  ⟨QuotientCwf.tySub (QType.mk codomain) (QuotientCwf.extPresentation context domain).hom,
    family_comparison context domain codomain⟩

/-! ## A total raw-context section is not this attachment -/

def underlyingContext (context : QuotientCwf.QContext rules) : (n : Nat) × Ctx Head n :=
  ⟨context.as.arity, context.as.raw⟩

/-- Any purported exact total raw-context attachment would provide missing
native formation. This is not a claim that arbitrary context maps do not exist. -/
theorem no_total_context_section {n : Nat} {raw : Ctx Head n}
    (unformed : ¬ ContextFormation rules raw) :
    ¬ ∃ attach : ((n : Nat) × Ctx Head n) → QuotientCwf.QContext rules,
      ∀ source, underlyingContext (attach source) = source := by
  rintro ⟨attach, same⟩
  have formed : ContextFormation rules (underlyingContext (attach ⟨n, raw⟩)).2 :=
    (attach ⟨n, raw⟩).as.formed
  rw [same] at formed
  exact unformed formed


end FormationSensitiveContextual.QuotientInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
