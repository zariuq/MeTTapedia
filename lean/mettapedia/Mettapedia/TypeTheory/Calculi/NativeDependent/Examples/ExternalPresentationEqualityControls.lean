import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualPresentationEquality
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticModel
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalRegularityControls

/-!
# Selected context equality with distinct higher-order family annotations

Contexts storing a witness of the declared family at a function and at its eta
expansion remain different raw syntax. Their actual selected comprehension
contexts and finite native telescopes coincide. At least one normalization
must change its annotation, so an identity presentation cannot satisfy this
comparison. The context maps preserve every original variable position.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.PresentationEqualityControls

open Contextual ContextualControls RegularityControls
open Contextual.Presentation Contextual.PresentationEquality

abbrev firstContext := extend functionContext firstFamily
abbrev secondContext := extend functionContext secondFamily

theorem selected_contexts_agree : selectedContext firstContext = selectedContext secondContext :=
  selected_context annotation_contexts_equal firstContext.formed secondContext.formed

theorem actual_telescope_agreement :
    HEq (selectedTelescope firstContext) (selectedTelescope secondContext) :=
  selected_telescope annotation_contexts_equal firstContext.formed secondContext.formed

theorem actual_source_parameter_context_agreement :
    SyntacticModel.parameterContext firstContext = SyntacticModel.parameterContext secondContext :=
  selected_parameter_context annotation_contexts_equal firstContext.formed secondContext.formed

theorem raw_contexts_still_differ : firstContext.raw ≠ secondContext.raw := extension_changes_annotation

theorem normalization_cannot_keep_both_raw_annotations :
    ¬ ((selectedContext firstContext).raw = firstContext.raw ∧
      (selectedContext secondContext).raw = secondContext.raw) := by
  rintro ⟨first, second⟩
  have selected := congrArg (fun context : Context signature =>
    (⟨context.arity, context.raw⟩ : Σ n, ContextExpr symbols n)) selected_contexts_agree
  have raws : (selectedContext firstContext).raw = (selectedContext secondContext).raw :=
    eq_of_heq (Sigma.mk.inj selected).2
  exact raw_contexts_still_differ (first.symm.trans (raws.trans second))

theorem comparison_retains_witness_position :
    (comparison firstContext).hom.substitution (0 : Fin 2) = .var (0 : Fin 2) := rfl

theorem comparison_retains_function_position :
    (comparison firstContext).hom.substitution (1 : Fin 2) = .var (1 : Fin 2) := rfl

def extraFirstType : TypeOver firstContext :=
  ⟨functionType 2, function_formed firstContext.formed⟩

def extraSecondType : TypeOver secondContext :=
  ⟨functionType 2, function_formed secondContext.formed⟩

theorem longer_contexts_equal : Holds signature (.contextEq
    (extend firstContext extraFirstType).raw (extend secondContext extraSecondType).raw) :=
  conclude (.contextExtendEquality firstContext.raw secondContext.raw (functionType 2) (functionType 2))
    ⟨annotation_contexts_equal, typeEquality_refl extraFirstType, extraSecondType.formed, trivial⟩

theorem longer_selected_contexts_agree :
    selectedContext (extend firstContext extraFirstType) = selectedContext (extend secondContext extraSecondType) :=
  selected_context longer_contexts_equal
    (extend firstContext extraFirstType).formed (extend secondContext extraSecondType).formed

theorem longer_parameter_contexts_agree :
    SyntacticModel.parameterContext (extend firstContext extraFirstType) =
      SyntacticModel.parameterContext (extend secondContext extraSecondType) :=
  selected_parameter_context longer_contexts_equal
    (extend firstContext extraFirstType).formed (extend secondContext extraSecondType).formed

theorem older_function_position_retained_after_extension :
    (comparison (extend firstContext extraFirstType)).hom.substitution (2 : Fin 3) = .var (2 : Fin 3) := rfl

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.PresentationEqualityControls
