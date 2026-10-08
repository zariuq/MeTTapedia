import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTypedAdmission
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualYoneda
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.TypedContextQuotientControls

/-!+# From supplied formation evidence to native sections

The actual context `(X : U), (f : Πx:X.X)` crosses the admission comparison.
Its eta substitution has the same typed quotient arrow and native section,
although the original subject codes are different. A second substitution
computes the type variable before admitting its dependent component. The
comparison is faithful on typed arrows and injective on typed fibres; these
facts do not provide an inverse recovering unquotiented syntax.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Examples.TypedAdmissionControls

open _root_.CategoryTheory
open TypedEquality TypedEquality.Normalization
open TypedQuotientControls (setting qualification functionValue displayedFunctionType)
open FormationSensitiveTypedAdmission TypedContextual NativePresheaf

abbrev source := TypedContextQuotientControls.context
abbrev target := admitContext qualification source

noncomputable def supplied : Term target (admitType qualification displayedFunctionType.erase) :=
  admitTerm qualification functionValue.erase

noncomputable def substituted :
    Term target (admitType qualification
      (displayedFunctionType.erase.reindex TypedContextQuotientControls.etaArrow)) :=
  admitTerm qualification (functionValue.erase.reindex TypedContextQuotientControls.etaArrow)

theorem admitted_eta_arrows_equal :
    (quotientProjection Tower.rules).map (admitArrow qualification (𝟙 source)) =
      (quotientProjection Tower.rules).map (admitArrow qualification TypedContextQuotientControls.etaArrow) :=
  (quotientProjection_map_eq_iff _ _).mpr
    (admitArrow_typed_equal qualification TypedContextQuotientControls.identity_eta_typed_equal)

/-- Faithfulness belongs to the typed comparison. The preceding raw-conversion
quotient still retains the eta distinction identified by the typed quotient. -/
theorem typed_admission_reflects_arrow_equality
    {first second : (FormationSensitiveTypedQuotient.typedProjection Tower.rules).obj source ⟶
      (FormationSensitiveTypedQuotient.typedProjection Tower.rules).obj source}
    (same : (typedBaseFunctor qualification).map first =
      (typedBaseFunctor qualification).map second) : first = second :=
  (typedBaseFunctor_faithful qualification).map_injective same

theorem dependent_annotation_preserved :
    (termClassMap qualification (FormationSensitiveTypedQuotient.QTerm.mk qualification functionValue.erase)).type =
      typeClassMap qualification (FormationSensitiveTypedQuotient.QType.mk qualification displayedFunctionType.erase) :=
  termClassMap_type qualification _

/-- Admission and actual eta substitution commute on the complete
type/subject pair, without selecting another source derivation. -/
theorem admitted_eta_terms_agree :
    QTerm.mk setting.levels supplied = QTerm.mk setting.levels substituted := by
  have same := TypedContextQuotientControls.reindexed_function_points_agree
  rw [FormationSensitiveTypedQuotient.QTerm.reindex_id] at same
  have mapped := congrArg (termClassMap qualification) same
  simpa only [FormationSensitiveTypedQuotient.QTerm.reindex_mk,
    termClassMap_mk, supplied, substituted] using mapped

theorem admitted_eta_types_agree :
    QType.mk setting.levels (admitType qualification displayedFunctionType.erase) =
      QType.mk setting.levels
        (admitType qualification (displayedFunctionType.erase.reindex TypedContextQuotientControls.etaArrow)) := by
  have same := TypedContextQuotientControls.reindexed_function_types_agree
  rw [FormationSensitiveTypedQuotient.QType.reindex_id] at same
  have mapped := congrArg (typeClassMap qualification) same
  simpa only [FormationSensitiveTypedQuotient.QType.reindex_mk,
    typeClassMap_mk] using mapped

/-- Independently annotated supplied subjects give the same actual natural
section in the native presheaf model. -/
theorem native_eta_sections_agree :
    nativeSection setting.levels supplied =
      nativeSectionAt setting.levels substituted admitted_eta_types_agree.symm := by
  apply (nativeSectionAt_eq_iff setting.levels supplied substituted
    rfl admitted_eta_types_agree.symm).mpr
  exact (QTerm.mk_eq_iff setting.levels supplied substituted).mp admitted_eta_terms_agree

/-- Native substitution has the actual admitted arrow as its argument and
recovers substitution into the supplied source subject. -/
theorem native_substitution_readout :
    nativeSection setting.levels (supplied.reindex (admitArrow qualification TypedContextQuotientControls.etaArrow)) =
      CwfYoneda.substituteSection (QuotientCwf.cwf setting.levels)
        (QuotientCwf.project (admitArrow qualification TypedContextQuotientControls.etaArrow))
        (nativeSection setting.levels supplied) :=
  section_reindex setting.levels supplied (admitArrow qualification TypedContextQuotientControls.etaArrow)

theorem equal_native_sections_have_different_subject_codes : supplied.code ≠ substituted.code :=
  TypedContextQuotientControls.reindexed_function_codes_differ

/-- Injective maps of typed fibres do not turn their quotient points into
injective encodings of unquotiented source syntax. -/
theorem original_raw_arrows_still_differ :
    (FormationSensitiveContextual.quotientProjection Tower.rules).map (𝟙 source) ≠
      (FormationSensitiveContextual.quotientProjection Tower.rules).map TypedContextQuotientControls.etaArrow :=
  TypedContextQuotientControls.raw_base_arrows_distinct

abbrev varying := TypedContextQuotientControls.dependent

theorem computed_component_is_admitted_at_changed_type :
    Typed Tower.rules (admitContext qualification varying).raw
      (.var (0 : Fin 2)) TypedContextQuotientControls.computedDomain.code :=
  admitArrow qualification TypedContextQuotientControls.computedArrow |>.typed (0 : Fin 2)

theorem computed_component_annotations_differ :
    subst (admitArrow qualification TypedContextQuotientControls.computedArrow).substitution
      (Ctx.lookup varying.raw (0 : Fin 2)) ≠ Ctx.lookup varying.raw (0 : Fin 2) :=
  TypedContextQuotientControls.computed_annotations_differ

theorem computed_arrows_agree_after_admission :
    (quotientProjection Tower.rules).map (admitArrow qualification (𝟙 varying)) =
      (quotientProjection Tower.rules).map (admitArrow qualification TypedContextQuotientControls.computedArrow) :=
  (quotientProjection_map_eq_iff _ _).mpr
    (admitArrow_typed_equal qualification TypedContextQuotientControls.identity_computed_equal)

end Examples.TypedAdmissionControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
