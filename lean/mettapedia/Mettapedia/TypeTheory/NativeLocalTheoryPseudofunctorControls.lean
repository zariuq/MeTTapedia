import Mettapedia.TypeTheory.NativeLocalTheoryPseudofunctor
import Mettapedia.TypeTheory.NativeLocalTheoryTransformationControls
import Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfCompositionControls

/-!
# Evidence-sensitive controls of the full local theory action

The nonidentity exchange changes an actual contextual transition. Its native
presentation retains the parameter context and name. The complete two-cell
action distinguishes a successor from a coherent, noninjective reset on the
same supplied receipt. Genuine composition and whiskering are exercised on
these independently constructed theory routes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NativeLocalTheoryPseudofunctorControls

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory
open _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafTheoryCwfControls DisplayedPresheafTheoryCwfTransformationControls
open DisplayedPresheafTheoryCwfCompositionControls
open NativeLocalTheoryTransformationControls (localWitness)
open DisplayedPresheafTheoryPseudofunctor (route change theory)
open NativeLocalTheoryPseudofunctor

theorem exchange_changes_the_route (number : Nat) :
    ((action.map (route exchange)).base.obj ⟨changingContext⟩).val.map
      backwardsRoute number = (1 : Nat) := rfl

theorem exchanged_context_is_not_identity :
    (action.map (route exchange)).base.obj ⟨changingContext⟩ ≠
      (⟨changingContext⟩ : (action.obj (theory Worlds)).toCwf.base.Context) :=
  actual_context_action_is_not_identity

theorem parameter_presentation_is_retained :
    ((action.map (route exchange)).mapType localWitness).parameters =
      exchange.op ⋙ base := rfl

theorem increment_reads_the_supplied_witness (number : Nat) :
    ((((action.map₂ (change increment)).family base ⟨localWitness⟩).substitution).app
      (Opposite.op (Discrete.mk ())) (sourceReceipt number)).2 = Nat.succ number := rfl

theorem reset_reads_the_constant_witness (number : Nat) :
    ((((action.map₂ (change reset)).family base ⟨localWitness⟩).substitution).app
      (Opposite.op (Discrete.mk ())) (sourceReceipt number)).2 = (1 : Nat) := rfl

theorem same_singleton_program_action :
    (action.map₂ (change increment)).base.app ⟨base⟩ =
      (action.map₂ (change reset)).base.app ⟨base⟩ :=
  NativeLocalTheoryTransformationControls.same_singleton_base_action

theorem distinct_evidence_actions :
    action.map₂ (change increment) ≠ action.map₂ (change reset) :=
  NativeLocalTheoryTransformationControls.corrected_cells_differ

theorem a_coherent_two_cell_can_merge_witnesses :
    ¬ Function.Injective
      ((((action.map₂ (change reset)).family base ⟨localWitness⟩).substitution).app
        (Opposite.op (Discrete.mk ()))) :=
  NativeLocalTheoryTransformationControls.coherent_reset_is_not_injective

theorem composition_comparison_reads_the_exact_witness (number : Nat) :
    (((((action.mapComp (route exchange) (route exchange)).hom.family base
      ⟨localWitness⟩).substitution).app
        (Opposite.op (WalkingParallelPair.zero : Worlds))) (exchangeReceipt number)).2 =
      number := rfl

theorem whiskering_changes_increment_to_reset (number : Nat) :
    ((((action.map₂ (route exchange ◁ change increment)).family base
      ⟨localWitness⟩).substitution).app (Opposite.op (Discrete.mk ()))
        (horizontalReceipt number)).2 = (1 : Nat) := rfl

theorem ignoring_whiskering_changes_the_answer :
    ((((action.map₂ (route exchange ◁ change increment)).family base
      ⟨localWitness⟩).substitution).app (Opposite.op (Discrete.mk ()))
        (horizontalReceipt 1)).2 ≠ Nat.succ 1 := by
  rw [whiskering_changes_increment_to_reset]
  exact (Nat.succ_ne_self 1).symm

end Mettapedia.TypeTheory.NativeLocalTheoryPseudofunctorControls
