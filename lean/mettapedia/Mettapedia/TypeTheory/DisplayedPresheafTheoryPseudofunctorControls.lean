import Mettapedia.TypeTheory.DisplayedPresheafTheoryPseudofunctor
import Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfCompositionControls

/-!
# Evidence-sensitive controls for the assembled theory action

The actual pseudofunctor changes the map of a presheaf under an exchange
of parallel theory arrows. Its two-cell action increments or resets a
supplied witness. Whiskering changes an increment into a reset, while
the composition comparison retains both components of each receipt.
Agreement on a singleton program context does not determine the action
on its displayed evidence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafTheoryPseudofunctorControls

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory
open _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafTheoryCwfControls DisplayedPresheafTheoryCwfTransformationControls
open DisplayedPresheafTheoryCwfCompositionControls

namespace Action
open DisplayedPresheafTheoryPseudofunctor

theorem exchange_changes_the_route (number : Nat) :
    ((action.map (route exchange)).base.obj ⟨changingContext⟩).val.map
      backwardsRoute number = (1 : Nat) := rfl

theorem exchanged_action_is_not_identity :
    (action.map (route exchange)).base.obj ⟨changingContext⟩ ≠
      (⟨changingContext⟩ : (action.obj (theory Worlds)).toCwf.base.Context) :=
  actual_context_action_is_not_identity

theorem increment_reads_the_supplied_witness (number : Nat) :
    ((((action.map₂ (change increment)).family base ⟨witnesses⟩).substitution).app
      (Opposite.op (Discrete.mk ())) (sourceReceipt number)).2 = Nat.succ number := rfl

theorem reset_reads_the_constant_witness (number : Nat) :
    ((((action.map₂ (change reset)).family base ⟨witnesses⟩).substitution).app
      (Opposite.op (Discrete.mk ())) (sourceReceipt number)).2 = (1 : Nat) := rfl

theorem same_singleton_program_action :
    (action.map₂ (change increment)).base.app ⟨base⟩ =
      (action.map₂ (change reset)).base.app ⟨base⟩ :=
  constant_base_components_agree

theorem distinct_evidence_actions :
    action.map₂ (change increment) ≠ action.map₂ (change reset) :=
  corrected_transformations_differ

theorem a_coherent_two_cell_can_merge_witnesses :
    ¬ Function.Injective
      ((((action.map₂ (change reset)).family base ⟨witnesses⟩).substitution).app
        (Opposite.op (Discrete.mk ()))) :=
  corrected_reset_is_not_injective

theorem composition_comparison_reads_the_exact_witness (number : Nat) :
    (((((action.mapComp (route exchange) (route exchange)).hom.family base
      ⟨witnesses⟩).substitution).app
        (Opposite.op (WalkingParallelPair.zero : Worlds))) (exchangeReceipt number)).2 =
      number := rfl

theorem whiskering_changes_increment_to_reset (number : Nat) :
    ((((action.map₂ (route exchange ◁ change increment)).family base
      ⟨witnesses⟩).substitution).app (Opposite.op (Discrete.mk ()))
        (horizontalReceipt number)).2 = (1 : Nat) := rfl

theorem ignoring_whiskering_changes_the_answer :
    ((((action.map₂ (route exchange ◁ change increment)).family base
      ⟨witnesses⟩).substitution).app (Opposite.op (Discrete.mk ()))
        (horizontalReceipt 1)).2 ≠ Nat.succ 1 := by
  rw [whiskering_changes_increment_to_reset]
  exact (Nat.succ_ne_self 1).symm

end Action
end Mettapedia.TypeTheory.DisplayedPresheafTheoryPseudofunctorControls
