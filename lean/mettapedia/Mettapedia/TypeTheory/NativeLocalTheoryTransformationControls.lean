import Mettapedia.TypeTheory.NativeLocalTheoryTransformation
import Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfTransformationControls
import Mettapedia.TypeTheory.ContextualLocalUniversesControls

/-!
# Local presentation and evidence controls for theory cells

The actual successor and reset theory transformations agree on a singleton
program context but act differently on supplied native evidence. Their local
presentations retain the parameter context, and their corrected cells retain
the complete transported witness. Reset is coherent and noninjective.

Two distinct external presentations of a varying finite family have equal
decodings. The fully faithful decoder constructs the actual display map
between them and preserves both the contextual point and supplied witness.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NativeLocalTheoryTransformationControls

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryTransformation ContextualLocalUniverses
open DisplayedPresheafTheoryCwfControls
open DisplayedPresheafTheoryCwfTransformationControls (increment reset sourceReceipt)
open NativeLocalTheoryTransformation

abbrev localWitness : LocalType (presheafCwf.{0, 0, 0} Worlds) base :=
  LocalType.present witnesses

theorem actual_parameter_is_retained :
    ((localMorphism selectOne).mapType localWitness).parameters = selectOne.op ⋙ base := rfl

theorem increment_reads_supplied_witness (number : Nat) :
    (((correctedTransformation increment).family base ⟨localWitness⟩).substitution).app
      (Opposite.op (Discrete.mk ())) (sourceReceipt number) =
        (⟨PUnit.unit, Nat.succ number⟩ :
          (totalSpace (reindexDisplayed (baseMap increment base)
            (restrictFamily selectZero base witnesses))).obj (Opposite.op (Discrete.mk ()))) := rfl

theorem reset_reads_constant_witness (number : Nat) :
    (((correctedTransformation reset).family base ⟨localWitness⟩).substitution).app
      (Opposite.op (Discrete.mk ())) (sourceReceipt number) =
        (⟨PUnit.unit, (1 : Nat)⟩ :
          (totalSpace (reindexDisplayed (baseMap reset base)
            (restrictFamily selectZero base witnesses))).obj (Opposite.op (Discrete.mk ()))) := rfl

theorem same_singleton_base_action :
    (correctedTransformation increment).base.app ⟨base⟩ =
      (correctedTransformation reset).base.app ⟨base⟩ := by
  change baseMap increment base = baseMap reset base
  ext world value
  rfl

theorem distinct_evidence_readouts :
    ((((correctedTransformation increment).family base ⟨localWitness⟩).substitution).app
      (Opposite.op (Discrete.mk ())) (sourceReceipt 1)).2 ≠
        ((((correctedTransformation reset).family base ⟨localWitness⟩).substitution).app
          (Opposite.op (Discrete.mk ())) (sourceReceipt 1)).2 := by
  rw [increment_reads_supplied_witness, reset_reads_constant_witness]
  exact Nat.succ_ne_self 1

theorem corrected_cells_differ :
    correctedTransformation increment ≠ correctedTransformation reset := by
  intro same
  have atPoint := congrArg (fun transformation :
      CorrectedTransformationData (localMorphism selectOne) (localMorphism selectZero) =>
    (transformation.base.app ⟨changingContext⟩).app
      (Opposite.op (Discrete.mk ())) (1 : Nat)) same
  change Nat.succ 1 = (1 : Nat) at atPoint
  exact Nat.succ_ne_self 1 atPoint

theorem coherent_reset_is_not_injective :
    ¬ Function.Injective
      ((((correctedTransformation reset).family base ⟨localWitness⟩).substitution).app
        (Opposite.op (Discrete.mk ()))) := by
  intro injective
  have equal : sourceReceipt 0 = sourceReceipt 1 := injective (by
    rw [reset_reads_constant_witness, reset_reads_constant_witness])
  have numbers := congrArg (fun receipt => receipt.2) equal
  exact Nat.zero_ne_one numbers

theorem corrected_identity :
    correctedTransformation (𝟙 selectOne) =
      CorrectedTransformationData.identity (localMorphism selectOne) :=
  correctedTransformation_identity selectOne

theorem genuine_vertical_composition :
    correctedTransformation (increment ≫ 𝟙 selectOne) =
      CorrectedTransformationData.vertical (correctedTransformation (𝟙 selectOne))
        (correctedTransformation increment) :=
  correctedTransformation_composition increment (𝟙 selectOne)

namespace Presentations

open ContextualLocalUniversesControls

local instance nativeCategory : Category.{0} (TypeOver core Bool) :=
  TypeOver.instCategory (C := core) (Γ := Bool)

local instance presentedCategory : Category.{0} (TypeOver (localCwf core) Bool) :=
  TypeOver.instCategory (C := localCwf core) (Γ := Bool)

abbrev firstObject : TypeOver (localCwf core) Bool := ⟨first⟩
abbrev secondObject : TypeOver (localCwf core) Bool := ⟨second⟩

theorem actual_presentations_differ : firstObject ≠ secondObject := fun same =>
  presentations_differ (congrArg TypeOver.val same)

theorem decoded_objects_agree :
    (displayDecoder core Bool).obj firstObject =
      (displayDecoder core Bool).obj secondObject := rfl

def completeDisplay : firstObject ⟶ secondObject :=
  (displayHomEquiv core firstObject secondObject).symm (𝟙 _)

theorem display_decodes_to_identity :
    (displayDecoder core Bool).map completeDisplay = 𝟙 _ :=
  (displayHomEquiv core firstObject secondObject).apply_symm_apply (𝟙 _)

theorem full_point_and_witness (point : Bool) (witness : Fin (sizes point)) :
    completeDisplay.substitution ⟨point, witness⟩ = ⟨point, witness⟩ := rfl

theorem supplied_varying_section_is_retained :
    (completeDisplay.substitution ⟨false, suppliedSection false⟩).2.val = 0 ∧
      (completeDisplay.substitution ⟨true, suppliedSection true⟩).2.val = 1 := ⟨rfl, rfl⟩

theorem decoded_arrow_faithfulness (candidate : firstObject ⟶ secondObject)
    (same : (displayDecoder core Bool).map candidate = 𝟙 _) : candidate = completeDisplay :=
  (displayHomEquiv core firstObject secondObject).injective (same.trans display_decodes_to_identity.symm)

end Presentations
end Mettapedia.TypeTheory.NativeLocalTheoryTransformationControls
