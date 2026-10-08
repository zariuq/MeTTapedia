import Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfComposition
import Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfTransformationControls

/-!
# Nonidentity controls for native CwF composition coherence

Exchanging two authored routes changes their actual presheaf action.
Two exchange stages restore the original route, and the structured
composition comparison retains every supplied witness. Horizontal
whiskering changes an increment into a reset because the outer theory
functor exchanges the routes. Ignoring that action yields a different
answer, and the coherent horizontal reset still identifies witnesses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfCompositionControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafCwf DisplayedPresheafTheoryRestriction
open DisplayedPresheafTheoryCwf DisplayedPresheafTheoryCwfControls
open DisplayedPresheafTheoryCwfTransformation DisplayedPresheafTheoryCwfTransformationControls
open DisplayedPresheafTheoryCwfComposition

theorem double_exchange_context_computes (number : Nat) :
    (((pseudoMorphism exchange).comp (pseudoMorphism exchange)).base.obj
      ⟨changingContext⟩).val.map backwardsRoute number = Nat.succ number := rfl

theorem direct_double_exchange_context_computes (number : Nat) :
    ((pseudoMorphism (exchange ⋙ exchange)).base.obj
      ⟨changingContext⟩).val.map backwardsRoute number = Nat.succ number := rfl

def exchangeReceipt (number : Nat) :
    (totalSpace (restrictFamily (exchange ⋙ exchange) base witnesses)).obj
      (Opposite.op (WalkingParallelPair.zero : Worlds)) :=
  ⟨PUnit.unit, number⟩

theorem composition_comparison_retains_witness (number : Nat) :
    ((((compositionIso exchange exchange).hom.family base ⟨witnesses⟩).substitution).app
      (Opposite.op (WalkingParallelPair.zero : Worlds)) (exchangeReceipt number)).2 = number := by
  rfl

/-- Whiskering the supplied increment by the actual route-exchange
functor gives a reset, despite coherence of the whole composition. -/
def horizontalIncrement :
    CorrectedTransformationData
      ((pseudoMorphism exchange).comp (pseudoMorphism selectOne))
      ((pseudoMorphism exchange).comp (pseudoMorphism selectZero)) :=
  CorrectedTransformationData.horizontal (correctedTransformation (𝟙 exchange))
    (correctedTransformation increment)

def horizontalReceipt (number : Nat) :
    (totalSpace (restrictFamily selectOne (exchange.op ⋙ base)
      (restrictFamily exchange base witnesses))).obj (Opposite.op (Discrete.mk ())) :=
  ⟨PUnit.unit, number⟩

theorem horizontal_increment_becomes_reset (number : Nat) :
    (((horizontalIncrement.family base ⟨witnesses⟩).substitution).app
      (Opposite.op (Discrete.mk ())) (horizontalReceipt number)).2 = (1 : Nat) := by
  rfl

theorem direct_horizontal_increment_becomes_reset (number : Nat) :
    ((((correctedTransformation (increment ◫ 𝟙 exchange)).family base
      ⟨witnesses⟩).substitution).app (Opposite.op (Discrete.mk ()))
        (horizontalReceipt number)).2 = (1 : Nat) := rfl

/-- The actual structured horizontal composite has a different result
from applying the unwhiskered increment to the supplied witness. -/
theorem ignoring_the_outer_theory_changes_evidence :
    (((horizontalIncrement.family base ⟨witnesses⟩).substitution).app
      (Opposite.op (Discrete.mk ())) (horizontalReceipt 1)).2 ≠ Nat.succ 1 := by
  rw [horizontal_increment_becomes_reset]
  exact Nat.succ_ne_self 1 |>.symm

/-- Corrected horizontal composition preserves coherence, not injectivity
of a noninvertible witness transport. -/
theorem coherent_horizontal_reset_is_not_injective :
    ¬ Function.Injective
      (((horizontalIncrement.family base ⟨witnesses⟩).substitution).app
        (Opposite.op (Discrete.mk ()))) := by
  intro injective
  have same : horizontalReceipt 0 = horizontalReceipt 1 := injective (by rfl)
  have numbers := congrArg (fun receipt => receipt.2) same
  exact Nat.zero_ne_one numbers

end Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfCompositionControls
