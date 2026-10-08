import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualCellUniqueness
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalContextualControls

/-!
# Converted variable-domain context presentation controls

The family depends on an actual function assumption. Equal function values
give generated-equal family annotations with different raw codes and different
raw extension objects. Selection preserves the function and dependent witness
positions while providing a finite chosen-comprehension presentation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.PresentationControls

open _root_.CategoryTheory Contextual
open ContextualControls
open Contextual.Presentation

noncomputable def presentedWitness : Context signature := selectedContext witnessContext

theorem presented_is_chosen : Chosen signature presentedWitness := selected_chosen witnessContext

theorem presented_retains_two_assumptions : presentedWitness.arity = 2 := rfl

theorem presented_context_conversion : Holds signature
    (.contextEq presentedWitness.raw witnessContext.raw) :=
  (select witnessContext.raw witnessContext.formed).equivalent

theorem presented_witness_position : (witness.reindex (comparison witnessContext).hom).code = .var (0 : Fin 2) :=
  comparison_term_code witnessContext witness

theorem presented_parameter_position :
    (firstAnnotation.reindex (comparison witnessContext).hom).code =
      .family .indexed (fun _ => .var (1 : Fin 2)) :=
  (comparison_type_code witnessContext firstAnnotation).trans projection_shifts_parameter

theorem presented_parameter_not_witness :
    (firstAnnotation.reindex (comparison witnessContext).hom).code ≠
      .family .indexed (fun _ => .var (0 : Fin 2)) := by
  rw [comparison_type_code]
  exact omitted_parameter_shift

theorem normalized_projection_code :
    ((normalizer signature).map olderProjection).substitution = (fun index => .var index.succ) :=
  normalizer_map_substitution olderProjection

theorem different_quotient_context_objects :
    (quotientProjection signature).obj (extend functionContext firstFamily) ≠
      (quotientProjection signature).obj (extend functionContext secondFamily) := by
  intro same
  have rawContexts : extend functionContext firstFamily = extend functionContext secondFamily :=
    congrArg (fun context => context.as) same
  have raw := congrArg (fun context : Context signature =>
    (⟨context.arity, context.raw⟩ : Σ n, ContextExpr symbols n)) rawContexts
  exact extension_changes_annotation (eq_of_heq (Sigma.mk.inj raw).2)

def actual_annotation_context_iso :
    (quotientProjection signature).obj (extend functionContext firstFamily) ≅
      (quotientProjection signature).obj (extend functionContext secondFamily) :=
  (quotientProjection signature).mapIso annotationExtensionIso

theorem comparison_roundtrip :
    (quotientComparison ((quotientProjection signature).obj witnessContext)).hom ≫
      (quotientComparison ((quotientProjection signature).obj witnessContext)).inv = 𝟙 _ :=
  (quotientComparison _).hom_inv_id

theorem complete_comparison_forces_every_component
    (other : quotientNormalizer signature ≅ 𝟭 (quotientContext signature))
    (onChosen : ∀ context, Chosen signature context.as →
      (other.app context).hom = ((quotientNormalizerIso signature).app context).hom) :
    other = quotientNormalizerIso signature :=
  natIso_ext_chosen other (quotientNormalizerIso signature) onChosen

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.PresentationControls
