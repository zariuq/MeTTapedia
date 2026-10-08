import Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfTransformation
import Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfControls

/-!
# Witness-sensitive corrected CwF transformation controls

Two actual theory transformations agree on the constant singleton base
context but increment or reset its supplied displayed witness. Their
corrected CwF transformations therefore differ. The reset component is
not injective, marking the boundary of claims about invertible transport.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfTransformationControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryTransformation
open DisplayedPresheafTheoryCwf DisplayedPresheafTheoryCwfControls
open DisplayedPresheafTheoryCwfTransformation

def increment : selectZero ⟶ selectOne :=
  (Functor.const Callers).map WalkingParallelPairHom.left

def reset : selectZero ⟶ selectOne :=
  (Functor.const Callers).map WalkingParallelPairHom.right

def sourceReceipt (number : Nat) :
    (totalSpace (restrictFamily selectOne base witnesses)).obj (Opposite.op (Discrete.mk ())) :=
  ⟨PUnit.unit, number⟩

theorem corrected_increment_computes (number : Nat) :
    (((correctedTransformation increment).family base ⟨witnesses⟩).substitution).app
      (Opposite.op (Discrete.mk ())) (sourceReceipt number) =
        (⟨PUnit.unit, Nat.succ number⟩ :
          (totalSpace (reindexDisplayed (baseMap increment base)
            (restrictFamily selectZero base witnesses))).obj (Opposite.op (Discrete.mk ()))) := rfl

theorem corrected_reset_computes (number : Nat) :
    (((correctedTransformation reset).family base ⟨witnesses⟩).substitution).app
      (Opposite.op (Discrete.mk ())) (sourceReceipt number) =
        (⟨PUnit.unit, (1 : Nat)⟩ :
          (totalSpace (reindexDisplayed (baseMap reset base)
            (restrictFamily selectZero base witnesses))).obj (Opposite.op (Discrete.mk ()))) := rfl

theorem constant_base_components_agree :
    (correctedTransformation increment).base.app ⟨base⟩ =
      (correctedTransformation reset).base.app ⟨base⟩ := by
  change baseMap increment base = baseMap reset base
  ext world value
  rfl

/-- Agreement on one base context does not determine a corrected CwF
transformation or its actual action on supplied witnesses. -/
theorem corrected_transformations_differ :
    correctedTransformation increment ≠ correctedTransformation reset := by
  intro same
  have supplied := congrArg (fun transformation :
      CorrectedTransformationData (pseudoMorphism selectOne) (pseudoMorphism selectZero) =>
    (transformation.base.app ⟨changingContext⟩).app
      (Opposite.op (Discrete.mk ())) (1 : Nat)) same
  change Nat.succ 1 = (1 : Nat) at supplied
  exact Nat.succ_ne_self 1 supplied

/-- A corrected 2-cell can satisfy all coherence squares while irreversibly
identifying different evidence values. -/
theorem corrected_reset_is_not_injective :
    ¬ Function.Injective
      ((((correctedTransformation reset).family base ⟨witnesses⟩).substitution).app
        (Opposite.op (Discrete.mk ()))) := by
  intro injective
  have equal : sourceReceipt 0 = sourceReceipt 1 := injective (by
    rw [corrected_reset_computes, corrected_reset_computes])
  have numbers := congrArg (fun receipt => receipt.2) equal
  change (0 : Nat) = 1 at numbers
  exact Nat.zero_ne_one numbers

end Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfTransformationControls
