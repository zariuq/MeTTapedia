import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalChosenContextFixedPoint
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalPresentationEqualityControls

/-!
# Chosen fixed points and genuinely changed dependent annotations

The selected function-and-witness context is fixed by another selection.
The corresponding native telescope is fixed as well. Two raw contexts
whose family annotations differ by function eta cannot both already be
chosen, despite their generated context equation and common presentation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.ChosenFixedPointControls

open _root_.CategoryTheory
open Contextual ContextualControls PresentationEqualityControls
open Contextual.Presentation

theorem selected_dependent_context_is_fixed :
    selectedContext (selectedContext witnessContext) = selectedContext witnessContext :=
  selectedContext_fixed (selected_chosen witnessContext)

theorem actual_native_telescope_is_fixed :
    selectedContext ((quotientProjection signature).obj
      (selectedContext witnessContext)).as =
        ((quotientProjection signature).obj (selectedContext witnessContext)).as :=
  selectedContext_telescope_fixed (selectedTelescope witnessContext)

theorem selected_context_keeps_both_assumptions :
    (selectedContext witnessContext).arity = 2 := rfl

theorem distinct_eta_annotations_cannot_both_be_chosen :
    ¬ (Chosen signature firstContext ∧ Chosen signature secondContext) := by
  rintro ⟨first, second⟩
  have same : firstContext = secondContext :=
    (selectedContext_fixed first).symm.trans
      (selected_contexts_agree.trans (selectedContext_fixed second))
  have raw := congrArg (fun context : Context signature =>
    (⟨context.arity, context.raw⟩ : Σ n, ContextExpr symbols n)) same
  exact raw_contexts_still_differ (eq_of_heq (Sigma.mk.inj raw).2)

theorem fixed_selection_keeps_function_position :
    (comparison (selectedContext witnessContext)).hom.substitution (1 : Fin 2) =
      .var (1 : Fin 2) := rfl

theorem fixed_selection_keeps_witness_position :
    (comparison (selectedContext witnessContext)).hom.substitution (0 : Fin 2) =
      .var (0 : Fin 2) := rfl

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.ChosenFixedPointControls
