import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualComprehensionSyntax
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.TypedContextualControls

/-!
# Typed annotation comparison and binder-action controls

The actual family annotations `H(f)` and `H(eta f)` compare by typed equality
while their raw conversion relation fails. Their extension comparison preserves
code, projection and the converted newest term. The transported annotation
remains a different code until retyping is applied. A nonidentity projection
under a fresh binder retains both the new variable and the older variable
shift, detecting omission of the lift.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Examples.TypedComprehensionControls

open _root_.CategoryTheory TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open TypedContextualControls

def comparison : extend familyContext firstAnnotation ≅ extend familyContext secondAnnotation :=
  extensionComparison firstAnnotation secondAnnotation annotations_equal

theorem comparison_uses_nonraw_equation :
    TypeEq Tower.rules familyContext.raw firstAnnotation.code secondAnnotation.code ∧
      ¬ Conv Tower.rules.headEq firstAnnotation.code secondAnnotation.code Tower.rules.computation :=
  ⟨annotations_equal, annotations_not_raw_converted⟩

theorem comparison_keeps_projection :
    comparison.hom ≫ projectionHom familyContext secondAnnotation = projectionHom familyContext firstAnnotation :=
  extensionComparison_projection _ _ _

theorem comparison_keeps_newest_after_retyping :
    ((newest familyContext secondAnnotation).reindex comparison.hom).convertType
      (firstAnnotation.reindex (projectionHom familyContext firstAnnotation))
      (extensionComparison_newest_typeEquality firstAnnotation secondAnnotation annotations_equal) = suppliedVariable :=
  extensionComparison_newest _ _ _

theorem comparison_roundtrip : comparison.hom ≫ comparison.inv = 𝟙 suppliedContext := comparison.hom_inv_id

/-- Preserving the variable's code does not identify the annotations
before the conversion step. -/
theorem omitted_retyping_does_not_preserve_literal_annotation :
    ((secondAnnotation.reindex (projectionHom familyContext secondAnnotation)).reindex comparison.hom).code ≠
      (firstAnnotation.reindex (projectionHom familyContext firstAnnotation)).code := by
  rw [comparison, extensionComparison_type_code]
  change subst projection secondAnnotation.code ≠ subst projection firstAnnotation.code
  rw [subst_projection, subst_projection]
  change Tm.app (.var (1 : Fin 3)) (.lam (.app (.var 3) (.var 0))) ≠ .app (.var 1) (.var 2)
  intro same
  cases same

noncomputable def selectedVariable : Term suppliedContext
    (QuotientCwf.typeRepresentative
      (QuotientCwf.tySub (QType.mk levels secondAnnotation)
        (QuotientCwf.project (projectionHom familyContext firstAnnotation)))) :=
  convertedVariable.convertType _ ((QType.mk_eq_iff levels _ _).mp
    (QuotientCwf.typeRepresentative_class
      (QuotientCwf.tySub (QType.mk levels secondAnnotation)
        (QuotientCwf.project (projectionHom familyContext firstAnnotation)))).symm)

theorem selected_variable_is_supplied_code : selectedVariable.code = .var 0 := rfl

theorem selected_variable_has_supplied_class : QTerm.mk levels selectedVariable = suppliedNativeVariable.val :=
  QTerm.mk_convertType convertedVariable _ _

theorem actual_section_matches_native_self_extension :
    QuotientCwf.project (nativeSection selectedVariable) =
      Mettapedia.TypeTheory.ContextualProductComparison.selfExtend (QuotientCwf.cwf levels) suppliedNativeVariable :=
  nativeSection_projects_of_class suppliedNativeVariable selectedVariable selected_variable_has_supplied_class

theorem actual_section_keeps_variable_and_prior :
    (nativeSection selectedVariable).substitution 0 = .var 0 ∧
      (nativeSection selectedVariable).substitution 1 = .var 0 := by
  rw [nativeSection_substitution]
  exact ⟨rfl, rfl⟩

/-- The source annotation is retyped, and the actual earlier projection
is lifted underneath its new binder. -/
def suppliedLift :
    extend suppliedContext (secondAnnotation.reindex (projectionHom familyContext firstAnnotation)) ⟶
      extend familyContext firstAnnotation :=
  convertedLift (projectionHom familyContext firstAnnotation) firstAnnotation
    (secondAnnotation.reindex (projectionHom familyContext firstAnnotation))
    (reindex_typeEquality annotations_equal (projectionHom familyContext firstAnnotation))

set_option backward.isDefEq.respectTransparency false in
theorem lifted_projection_computes :
    suppliedLift.substitution 0 = .var 0 ∧
      suppliedLift.substitution 1 = .var 2 ∧ suppliedLift.substitution 2 = .var 3 := by
  rw [suppliedLift, convertedLift_substitution]
  exact ⟨rfl, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem omitted_binder_shift_fails : suppliedLift.substitution 1 ≠ .var 1 := by
  rw [suppliedLift, convertedLift_substitution]
  intro same
  cases same

theorem generic_lift_receives_actual_typed_substitution :
    QuotientCwf.project
      (nativeLift (QuotientCwf.project (projectionHom familyContext firstAnnotation))
        (QType.mk levels firstAnnotation)) =
      Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf levels)
        (QuotientCwf.project (projectionHom familyContext firstAnnotation)) (QType.mk levels firstAnnotation) :=
  nativeLift_projects _ _

end Examples.TypedComprehensionControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
