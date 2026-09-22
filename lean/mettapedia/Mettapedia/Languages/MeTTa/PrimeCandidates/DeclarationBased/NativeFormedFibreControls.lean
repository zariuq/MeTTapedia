import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConversionFibres
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualComparison
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeFormedContextComparisonControls
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveCompletedConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualQuotient
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeFormedQuotientControls

/-! # Concrete controls for conversion classes of formed dependent fibres -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual
open _root_.CategoryTheory FormationSensitive
/-- For every opaque native extension, the term component of quotient
equality has an entirely formed completed-conversion path after the actual
annotation conversion. This neither lifts an arbitrary raw receipt path
nor claims confluence of authored execution. -/
theorem QTerm.mk_eq_iff_completed {signature : Declaration.Signature Tower.Head}
    (opacity : OpaqueRelatorExtension.Opacity signature)
    {context : Context (OpaqueRelatorExtension.rules signature)}
    {first second : TypeOver context} (left : Term context first) (right : Term context second) :
    QTerm.mk left = QTerm.mk right ↔
      ∃ converted : Conv (OpaqueRelatorExtension.rules signature).headEq
        first.code second.code (OpaqueRelatorExtension.rules signature).computation,
        FormationSensitiveCompletedConversion.Conversion
          (⟨left.code, (left.convertType second converted).judgment⟩ :
            FormationSensitiveCompletedConversion.Admitted signature context.raw second.code)
          ⟨right.code, right.judgment⟩ := by
  constructor
  · intro same
    obtain ⟨annotations, terms⟩ := (QTerm.mk_eq_iff left right).mp same
    exact ⟨annotations, FormationSensitiveCompletedConversion.conversion_complete opacity _ _ terms⟩
  · rintro ⟨annotations, terms⟩
    exact (QTerm.mk_eq_iff left right).mpr
      ⟨annotations, FormationSensitiveCompletedConversion.conversion_sound opacity terms⟩

/-! ## Actual mixed native and universe-witness controls -/

namespace FibreControls

def projectedIdentity (wire : NativeWireData.Wire) : TypeOver Common.context :=
  ComparisonControls.variableIdentity.reindex (Common.sectionHom (Common.projected wire))

def resultIdentity (wire : NativeWireData.Wire) : TypeOver Common.context :=
  ComparisonControls.variableIdentity.reindex (Common.sectionHom (Common.result wire))

def projectedReflexivity (wire : NativeWireData.Wire) : Term Common.context (projectedIdentity wire) :=
  ComparisonControls.variableReflexivity.reindex (Common.sectionHom (Common.projected wire))

def resultReflexivity (wire : NativeWireData.Wire) : Term Common.context (resultIdentity wire) :=
  ComparisonControls.variableReflexivity.reindex (Common.sectionHom (Common.result wire))

/-- These are the actual dependent identity family and its reflexivity
section, substituted by the mixed HOL-list/wire projection and its result. -/
theorem dependent_mixed_reindex (wire : NativeWireData.Wire) :
    Judgment HOLNativeRelatorCompatibility.rules Common.context.raw
      (projectedReflexivity wire).code (projectedIdentity wire).code ∧
    Judgment HOLNativeRelatorCompatibility.rules Common.context.raw
      (resultReflexivity wire).code (resultIdentity wire).code ∧
    QType.mk (projectedIdentity wire) = QType.mk (resultIdentity wire) ∧
    QTerm.mk (projectedReflexivity wire) = QTerm.mk (resultReflexivity wire) :=
  ⟨(projectedReflexivity wire).judgment, (resultReflexivity wire).judgment,
    QType.reindex_pointwise (QType.mk ComparisonControls.variableIdentity)
      (QuotientControls.mixed_projection_homConversion wire),
    QTerm.reindex_pointwise (QTerm.mk ComparisonControls.variableReflexivity)
      (QuotientControls.mixed_projection_homConversion wire)⟩

theorem dependent_codes_differ :
    (projectedIdentity (.natural 7)).code ≠ (resultIdentity (.natural 7)).code ∧
    (projectedReflexivity (.natural 7)).code ≠ (resultReflexivity (.natural 7)).code := by
  constructor
  · intro same
    have endpoint := (Tm.id.inj same).2.1
    have actual : (Common.projected (.natural 7)).code = (Common.result (.natural 7)).code := by
      simpa only [subst, Common.sectionHom, pair, consSub_zero, Term.cast_code] using endpoint
    exact Common.converted_sections_distinct (congrArg Common.sectionHom (Term.ext actual))
  · intro same
    have endpoint := Tm.refl.inj same
    have actual : (Common.projected (.natural 7)).code = (Common.result (.natural 7)).code := by
      simpa only [subst, Common.sectionHom, pair, consSub_zero, Term.cast_code] using endpoint
    exact Common.converted_sections_distinct (congrArg Common.sectionHom (Term.ext actual))

theorem expanded_annotation_same_class :
    ComparisonControls.expandedWireType.code ≠ Common.wireType.code ∧
      QType.mk ComparisonControls.expandedWireType = QType.mk Common.wireType :=
  ⟨ComparisonControls.expanded_annotation_distinct,
    (QType.mk_eq_iff _ _).mpr ComparisonControls.expanded_converts_wire⟩

theorem natural_term_classes_equal_iff (first second : Nat) :
    QTerm.mk (Common.result (.natural first)) = QTerm.mk (Common.result (.natural second)) ↔
      first = second := by
  constructor
  · intro same
    exact (QuotientControls.natural_conversion_iff (n := 0) first second).mp
      ((QTerm.mk_eq_iff _ _).mp same).2
  · rintro rfl
    rfl

/-- The quotient is nontrivial but not collapsed: actual values seven and
eight remain different, despite identifying the mixed projection with seven. -/
theorem seven_eight_distinct :
    QTerm.mk (Common.result (.natural 7)) ≠ QTerm.mk (Common.result (.natural 8)) := by
  intro same
  have impossible := (natural_term_classes_equal_iff 7 8).mp same
  cases impossible

theorem projected_term_same_class (wire : NativeWireData.Wire) :
    QTerm.mk (Common.projected wire) = QTerm.mk (Common.result wire) :=
  (QTerm.mk_eq_iff _ _).mpr ⟨.refl _, Common.projected_converts_result wire⟩

/-- Raw syntax inspection remains meaningful before this quotient, but
cannot be reconstructed uniformly from the chosen conversion class. -/
theorem no_total_code_recovery :
    ¬ ∃ recover : QTerm Common.context → Tower.Tm Common.context.arity,
      ∀ (type : TypeOver Common.context) (term : Term Common.context type),
        recover (QTerm.mk term) = term.code := by
  rintro ⟨recover, faithful⟩
  have first := faithful Common.wireType (Common.projected (.natural 7))
  have second := faithful Common.wireType (Common.result (.natural 7))
  rw [projected_term_same_class] at first
  have impossible := first.symm.trans second
  change .snd (HOLNativeRelatorCompatibility.mixedPayload (.natural 7)) =
    NativeWireData.encode (.natural 7) at impossible
  simp only [NativeWireData.encode] at impossible
  cases impossible

/-- The same actual Data code is independently formed one universe higher
by native cumulativity. Its formation witness is not a unique code property. -/
def raisedWireType : TypeOver Common.context where
  code := NativeWireData.dataType
  level := .sort (.succ Tower.zero)
  universeWitness := .sort _
  formed := .cumul Common.wireType.formed (fun _ => Nat.le_succ _)

theorem raised_same_class : QType.mk raisedWireType = QType.mk Common.wireType :=
  (QType.mk_eq_iff _ _).mpr (.refl _)

theorem wire_two_universe_memberships :
    (QType.mk Common.wireType).AtUniverse (.sort Tower.zero) ∧
      (QType.mk Common.wireType).AtUniverse (.sort (.succ Tower.zero)) :=
  ⟨QType.atUniverse_mk _, ⟨raisedWireType, raised_same_class, rfl⟩⟩

theorem no_selected_level_recovery :
    ¬ ∃ recover : QType Common.context → Tower.Head,
      ∀ type : TypeOver Common.context, recover (QType.mk type) = type.level := by
  rintro ⟨recover, faithful⟩
  have first := faithful raisedWireType
  have second := faithful Common.wireType
  rw [raised_same_class] at first
  have impossible := first.symm.trans second
  cases impossible

theorem conversion_fibre_crown :
    QType.mk (projectedIdentity (.natural 7)) = QType.mk (resultIdentity (.natural 7)) ∧
    QTerm.mk (projectedReflexivity (.natural 7)) = QTerm.mk (resultReflexivity (.natural 7)) ∧
    (projectedIdentity (.natural 7)).code ≠ (resultIdentity (.natural 7)).code ∧
    QTerm.mk (Common.result (.natural 7)) ≠ QTerm.mk (Common.result (.natural 8)) ∧
    (QType.mk Common.wireType).AtUniverse (.sort Tower.zero) ∧
    (QType.mk Common.wireType).AtUniverse (.sort (.succ Tower.zero)) :=
  ⟨(dependent_mixed_reindex _).2.2.1, (dependent_mixed_reindex _).2.2.2,
    dependent_codes_differ.1, seven_eight_distinct,
    wire_two_universe_memberships.1, wire_two_universe_memberships.2⟩

end FibreControls

end FormationSensitiveContextual
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
