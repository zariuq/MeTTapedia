import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelMapComposition
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.RefinementAbstractModelMapControls

/-!
# Composition readouts on a guarded varying native model

The nonidentity generated-source map is followed by the actual identity
logical map. Its intermediate and final values are compared independently
with the supplied conditional natural-number section. The varying finite
family and selected newer argument retain their complete readings. Replacing
that selected argument by the older projection changes the result, and
deleting the proper positivity guard still rejects introduction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.ModelMapCompositionControls

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateModelScopes ContextualPredicateScopeMorphism ContextualComprehensionMorphism
open ContextualTelescopeMorphism ContextualModelTelescopes ContextualStrictMorphismComposition
open Refinement.Abstract
open AbstractModelMapControls

noncomputable section

def sequentialMapping : ModelMap source target := mapping.comp (ModelMap.identity target)

theorem complete_map_unit : sequentialMapping = mapping := ModelMap.comp_identity mapping

/-- Independently successful middle and final evaluations recover the same
complete supplied native value, not just its guard or inhabitation. -/
theorem intermediate_and_final_certificate_retained :
    ValueImage mapping.morphism
      (⟨sourceConditionalType, sourceConditionalCertificate⟩ :
        Value sourceBase.toCwf sourceConditionalScope.1)
      (⟨ULift.up (PresheafNativeStableRefinement.chosen
          InterpretationControls.conditionalType InterpretationControls.conditionalPredicate),
        ULift.up InterpretationControls.conditionalRefined⟩ :
          Value targetBase.toCwf targetConditionalScope.1) ∧
    ValueImage (ModelMap.identity target).morphism
      (⟨ULift.up (PresheafNativeStableRefinement.chosen
          InterpretationControls.conditionalType InterpretationControls.conditionalPredicate),
        ULift.up InterpretationControls.conditionalRefined⟩ :
          Value targetBase.toCwf targetConditionalScope.1)
      (⟨ULift.up (PresheafNativeStableRefinement.chosen
          InterpretationControls.conditionalType InterpretationControls.conditionalPredicate),
        ULift.up InterpretationControls.conditionalRefined⟩ :
          Value targetBase.toCwf targetConditionalScope.1) ∧
    ValueImage sequentialMapping.morphism
      (⟨sourceConditionalType, sourceConditionalCertificate⟩ :
        Value sourceBase.toCwf sourceConditionalScope.1)
      (⟨ULift.up (PresheafNativeStableRefinement.chosen
          InterpretationControls.conditionalType InterpretationControls.conditionalPredicate),
        ULift.up InterpretationControls.conditionalRefined⟩ :
          Value targetBase.toCwf targetConditionalScope.1) := by
  rcases mapping.evaluateTerm_composition (ModelMap.identity target)
    (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0))
    sourceConditionalScope targetConditionalScope targetConditionalScope
    (scope_image Controls.conditionalContextFormed _ target_conditional_context_read)
    (ScopeImage.identity targetConditionalScope) _ source_conditional_certificate_read with
      ⟨middleValue, finalValue, middleRead, finalRead, firstValues, secondValues, totalValues⟩
  cases Option.some.inj (middleRead.symm.trans target_conditional_certificate_read)
  cases Option.some.inj (finalRead.symm.trans target_conditional_certificate_read)
  exact ⟨firstValues, secondValues, totalValues⟩

theorem complete_conditional_certificate_composed :
    HEq (sequentialMapping.morphism.toFamilyMorphism.mapTerm sourceConditionalCertificate)
      (ULift.up InterpretationControls.conditionalRefined) :=
  intermediate_and_final_certificate_retained.2.2.terms

/-- The actual mapped certificate is retyped using its earned type image;
this definition does not select the independently supplied native section. -/
def composedConditionalCertificate : targetBase.toCwf.Tm targetConditionalScope.1
    (ULift.up (PresheafNativeStableRefinement.chosen
      InterpretationControls.conditionalType InterpretationControls.conditionalPredicate)) :=
  imageAtType sequentialMapping.morphism
    (scope_image Controls.conditionalContextFormed _ target_conditional_context_read).contexts _
    intermediate_and_final_certificate_retained.2.2.types sourceConditionalCertificate

theorem composedConditionalCertificate_eq :
    composedConditionalCertificate = ULift.up InterpretationControls.conditionalRefined :=
  eq_of_heq ((imageAtType_heq sequentialMapping.morphism
    (scope_image Controls.conditionalContextFormed _ target_conditional_context_read).contexts _
    intermediate_and_final_certificate_retained.2.2.types sourceConditionalCertificate).symm.trans
      complete_conditional_certificate_composed)

theorem supplied_positive_number_survives_composition
    (world : Worldᵒᵖ) (number : Nat) (positive : 0 < number) :
    (PresheafNativeStableRefinement.forget
      InterpretationControls.conditionalType InterpretationControls.conditionalPredicate
      composedConditionalCertificate.down).val
        ⟨world, InterpretationControls.positiveBase world number positive⟩ = number := by
  rw [composedConditionalCertificate_eq]
  exact InterpretationControls.supplied_number_retained world number positive

theorem different_positive_inputs_remain_distinct_after_composition (world : Worldᵒᵖ) :
    (PresheafNativeStableRefinement.forget
      InterpretationControls.conditionalType InterpretationControls.conditionalPredicate
      composedConditionalCertificate.down).val
        ⟨world, InterpretationControls.positiveBase world 1 (by decide)⟩ ≠
    (PresheafNativeStableRefinement.forget
      InterpretationControls.conditionalType InterpretationControls.conditionalPredicate
      composedConditionalCertificate.down).val
        ⟨world, InterpretationControls.positiveBase world 2 (by decide)⟩ := by
  rw [supplied_positive_number_survives_composition, supplied_positive_number_survives_composition]
  exact (by decide : (1 : Nat) ≠ 2)

def sourcePositivity : sourceQualified.localModel.doctrine.Predicate (sourceScope Controls.scalarContext).1 :=
  Abstract.Derivation.predicateValue source sourceQualified.realization
    sourceQualified.products_substitution sourceQualified.products_beta sourceQualified.products_eta
    Controls.positiveVariable (sourceScope Controls.scalarContext) (sourceScope_read Controls.scalarContext)

theorem source_positivity_read : source.evaluatePredicate (sourceScope Controls.scalarContext)
    (Controls.positive 0) = some sourcePositivity :=
  Abstract.Derivation.predicateValue_readout source sourceQualified.realization
    sourceQualified.products_substitution sourceQualified.products_beta sourceQualified.products_eta
    Controls.positiveVariable (sourceScope Controls.scalarContext) (sourceScope_read Controls.scalarContext)

theorem target_positivity_read : target.evaluatePredicate targetScalarScope (Controls.positive 0) =
    some (ULift.up InterpretationControls.positivity) := by
  have original : AbstractInterpretationControls.model.evaluatePredicate
      AbstractInterpretationControls.scalarScope (Controls.positive 0) =
        some InterpretationControls.positivity :=
    (Refinement.ModelData.evaluatePredicate_compare InterpretationControls.model _ _).trans
      InterpretationControls.positive_scalar_read
  exact nativeQualified.data.evaluatePredicate_carrierLift _ _ _ original

theorem complete_positivity_composed :
    HEq (sequentialMapping.predicates.doctrine.hom (sourceScope Controls.scalarContext).1 sourcePositivity)
      (ULift.up InterpretationControls.positivity) :=
  sequentialMapping.evaluatePredicate_image_unique _ _ _
    (ScopeImage.comp mapping.morphism (ModelMap.identity target).morphism
      (scope_image Controls.scalarContext _ target_scalar_context_read) (ScopeImage.identity targetScalarScope))
      _ _ source_positivity_read target_positivity_read

def composedPositivity : targetQualified.localModel.doctrine.Predicate targetScalarScope.1 :=
  ContextualPredicateScopeMorphism.imagePredicate sequentialMapping.predicates.doctrine
    (scope_image Controls.scalarContext _ target_scalar_context_read).contexts sourcePositivity

theorem composedPositivity_eq : composedPositivity = ULift.up InterpretationControls.positivity :=
  eq_of_heq ((imagePredicate_heq sequentialMapping.predicates.doctrine
    (scope_image Controls.scalarContext _ target_scalar_context_read).contexts sourcePositivity).symm.trans
      complete_positivity_composed)

theorem composition_does_not_replace_positivity_by_truth : composedPositivity.down ≠
    (⊤ : _root_.CategoryTheory.Subfunctor InterpretationControls.scalarScope.1) := by
  rw [composedPositivity_eq]
  exact InterpretationControls.positivity_is_proper

theorem varying_fibre_survives_composition :
    ∃ annotation : sourceBase.toCwf.Ty (sourceScope Controls.scalarContext).1,
      source.evaluateType (sourceScope Controls.scalarContext) (Controls.fibre 0) = some annotation ∧
      HEq (sequentialMapping.morphism.toFamilyMorphism.mapType annotation)
        (ULift.up.{1,1} InterpretationControls.fibreType) := by
  rw [complete_map_unit]
  exact mapped_fibre_read

theorem fibre_still_varies (world : Worldᵒᵖ) (number : Nat) :
    InterpretationControls.fibreType.decoded.obj
      ⟨world, (⟨PUnit.unit, number⟩ : AbstractInterpretationControls.scalarScope.1.obj world)⟩ =
        Fin (Nat.succ number) := actual_fibre_depends_on_input world number

theorem newer_argument_survives_composition : imageArrow sequentialMapping.morphism
    (scope_image doubleContextTree targetDoubleScope target_double_context_read).contexts
    (scope_image Controls.scalarContext targetScalarScope target_scalar_context_read).contexts
    sourceNewestArgument = ULift.up InterpretationControls.newestScalar := by
  change imageArrow mapping.morphism
    (scope_image doubleContextTree targetDoubleScope target_double_context_read).contexts
    (scope_image Controls.scalarContext targetScalarScope target_scalar_context_read).contexts
    sourceNewestArgument = ULift.up InterpretationControls.newestScalar
  exact actual_newer_argument_image

theorem older_projection_does_not_replace_the_composite_image :
    imageArrow sequentialMapping.morphism
      (scope_image doubleContextTree targetDoubleScope target_double_context_read).contexts
      (scope_image Controls.scalarContext targetScalarScope target_scalar_context_read).contexts
      sourceNewestArgument ≠
        (ULift.up (native.toCwf.wk InterpretationControls.scalarVariableType) :
          targetBase.toCwf.Sub targetDoubleScope.1 targetScalarScope.1) := by
  rw [newer_argument_survives_composition]
  exact omitting_the_selected_argument_changes_the_reading

theorem composition_does_not_supply_a_missing_guard :
    ¬ Nonempty (Derivation Controls.signature (.term (.snoc .nil (Controls.scalar 0))
      (.refine (Controls.scalar 1) (Controls.positive 1) (.var 0))
      (.comprehension (Controls.scalar 1) (Controls.positive 1)))) :=
  removing_positivity_prevents_a_generated_refinement

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.ModelMapCompositionControls
