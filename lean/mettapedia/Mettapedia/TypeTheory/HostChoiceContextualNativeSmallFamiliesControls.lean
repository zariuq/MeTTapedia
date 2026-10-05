import Mettapedia.TypeTheory.HostChoiceContextualNativeSmallFamilies
import Mettapedia.TypeTheory.ContextualSmallFamilyNativeControls

/-!+# Growing material parameters in the optional native comparison

The site is an actual presheaf site whose opposite consists of successive
natural-number stages. Bare material parameters stay in the wider universe;
argument positions grow and results depend on their positions. The chosen
native product retains two complete functions that agree at every current
argument and differ at later arguments.

The optional native interfaces and their external host assumptions remain
separate from the constructive small-family controls.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HostChoiceContextualNativeSmallFamiliesControls

open CategoryTheory ContextualWitnessCover ContextualSmallFamilyTypeFormers
open HostChoiceContextualNativeSmallFamilies
open MaterialSets.Hypersets

abbrev Site := Natᵒᵖ

def stage (number : Nat) : Siteᵒᵖ := Opposite.op (Opposite.op number)

def stageReading : Siteᵒᵖ ⥤ Nat where
  obj point := point.unop.unop
  map arrow := arrow.unop.unop
  map_id _ := rfl
  map_comp _ _ := rfl

def parameters : Siteᵒᵖ ⥤ Type 1 where
  obj point := ContextualSmallFamilyUniverseControls.parameters.obj (stageReading.obj point)
  map arrow := ContextualSmallFamilyUniverseControls.parameters.map (stageReading.map arrow)
  map_id point := ContextualSmallFamilyUniverseControls.parameters.map_id (stageReading.obj point)
  map_comp first second := ContextualSmallFamilyUniverseControls.parameters.map_comp
    (stageReading.map first) (stageReading.map second)

def elementReading : parameters.Elements ⥤ ContextualSmallFamilyUniverseControls.parameters.Elements where
  obj point := ⟨stageReading.obj point.1, point.2⟩
  map arrow := ⟨stageReading.map arrow.1, arrow.2⟩
  map_id _ := by
    apply Subtype.ext
    rfl
  map_comp _ _ := by
    apply Subtype.ext
    rfl

def arguments := elementReading ⋙ ContextualSmallFamilyUniverseControls.cyclicSmall

def argumentReading : arguments.Elements ⥤ ContextualSmallFamilyUniverseControls.cyclicSmall.Elements where
  obj point := ⟨elementReading.obj point.1, point.2⟩
  map arrow := ⟨elementReading.map arrow.1, arrow.2⟩
  map_id _ := by
    apply Subtype.ext
    rfl
  map_comp _ _ := by
    apply Subtype.ext
    rfl

def results := argumentReading ⋙ ContextualSmallFamilyTypeFormerControls.positionResults

def unitFamily : parameters.Elements ⥤ Type := ContextualSmallFamilyTypeFormerControls.smallUnit

def greatestResult : NatTrans (overArguments arguments unitFamily) results where
  app argument := TypeCat.ofHom fun _ => ⟨argument.2.1.val, Nat.le_refl _⟩
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro _
    exact Subtype.ext (congrArg (fun member : arguments.obj second.1 => member.1.val) arrow.2).symm

def zeroResult : NatTrans (overArguments arguments unitFamily) results where
  app _ := TypeCat.ofHom fun _ => ⟨0, Nat.zero_le _⟩
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro _
    exact Subtype.ext rfl

def parameter (number : Nat) (material : HSet.{0}) : parameters.Elements := ⟨stage number, material⟩

def greatest (point : parameters.Elements) : ProductAt arguments results point :=
  piCurryValue arguments results greatestResult point PUnit.unit

def zero (point : parameters.Elements) : ProductAt arguments results point :=
  piCurryValue arguments results zeroResult point PUnit.unit

theorem greatest_evaluation (point : parameters.Elements) (argument : arguments.obj point) :
    (evaluateValue arguments results point (greatest point) argument).val = argument.1.val :=
  congrArg Subtype.val (congrArg
    (fun operation : NatTrans (overArguments arguments unitFamily) results =>
      operation.app ⟨point, argument⟩ PUnit.unit)
    (pi_uncurry_curry arguments results greatestResult))

theorem zero_evaluation (point : parameters.Elements) (argument : arguments.obj point) :
    (evaluateValue arguments results point (zero point) argument).val = 0 :=
  congrArg Subtype.val (congrArg
    (fun operation : NatTrans (overArguments arguments unitFamily) results =>
      operation.app ⟨point, argument⟩ PUnit.unit)
    (pi_uncurry_curry arguments results zeroResult))

theorem same_present_all_arguments (material : HSet.{0})
    (argument : arguments.obj (parameter 0 material)) :
    evaluateValue arguments results (parameter 0 material) (greatest (parameter 0 material)) argument =
      evaluateValue arguments results (parameter 0 material) (zero (parameter 0 material)) argument := by
  apply Subtype.ext
  rw [greatest_evaluation, zero_evaluation]
  exact congrArg Fin.val (Fin.eq_zero argument.1)

def laterArgument (number : Nat) : (futureDomain arguments (parameter 0 HSet.quineAtom)).Elements :=
  ⟨⟨stage (number + 1), (homOfLE (Nat.zero_le (number + 1))).op.op⟩,
    ContextualSmallFamilyUniverseControls.newCyclicMember number⟩

theorem greatest_future_value (number : Nat) :
    ((greatest (parameter 0 HSet.quineAtom)).val (laterArgument number)).val = number + 1 := rfl

theorem zero_future_value (number : Nat) :
    ((zero (parameter 0 HSet.quineAtom)).val (laterArgument number)).val = 0 := rfl

theorem different_complete_futures : greatest (parameter 0 HSet.quineAtom) ≠ zero (parameter 0 HSet.quineAtom) := by
  intro same
  have values := congrArg (fun function : ProductAt arguments results (parameter 0 HSet.quineAtom) =>
    (function.val (laterArgument 0)).val) same
  exact Nat.one_ne_zero values

noncomputable def nativeGreatest (point : parameters.Elements) :=
  (nativeFibreDecoder arguments results point).symm (greatest point)

noncomputable def nativeZero (point : parameters.Elements) :=
  (nativeFibreDecoder arguments results point).symm (zero point)

theorem native_same_present (material : HSet.{0}) (argument : arguments.obj (parameter 0 material)) :
    evaluateValue arguments results (parameter 0 material)
        (nativeFibreDecoder arguments results (parameter 0 material) (nativeGreatest (parameter 0 material))) argument =
      evaluateValue arguments results (parameter 0 material)
        (nativeFibreDecoder arguments results (parameter 0 material) (nativeZero (parameter 0 material))) argument := by
  have first := congrArg
    (fun function : ProductAt arguments results (parameter 0 material) =>
      evaluateValue arguments results (parameter 0 material) function argument)
    (nativeFibreDecoder_right arguments results (parameter 0 material) (greatest (parameter 0 material)))
  have second := congrArg
    (fun function : ProductAt arguments results (parameter 0 material) =>
      evaluateValue arguments results (parameter 0 material) function argument)
    (nativeFibreDecoder_right arguments results (parameter 0 material) (zero (parameter 0 material)))
  exact first.trans ((same_present_all_arguments material argument).trans second.symm)

theorem native_different_complete_futures :
    (nativeGreatest (parameter 0 HSet.quineAtom)).val ≠ (nativeZero (parameter 0 HSet.quineAtom)).val := by
  intro same
  apply different_complete_futures
  have decoded := congrArg (nativeFibreDecoder arguments results (parameter 0 HSet.quineAtom)) (Subtype.ext same)
  exact (nativeFibreDecoder_right arguments results (parameter 0 HSet.quineAtom)
    (greatest (parameter 0 HSet.quineAtom))).symm.trans
      (decoded.trans (nativeFibreDecoder_right arguments results (parameter 0 HSet.quineAtom)
        (zero (parameter 0 HSet.quineAtom))))

theorem native_infinitely_many_future_results : Function.Injective (fun number =>
    ((nativeFibreDecoder arguments results (parameter 0 HSet.quineAtom)
      (nativeGreatest (parameter 0 HSet.quineAtom))).val (laterArgument number)).val) := by
  intro first second same
  have firstValue := congrArg
    (fun function : ProductAt arguments results (parameter 0 HSet.quineAtom) =>
      (function.val (laterArgument first)).val)
    (nativeFibreDecoder_right arguments results (parameter 0 HSet.quineAtom)
      (greatest (parameter 0 HSet.quineAtom)))
  have secondValue := congrArg
    (fun function : ProductAt arguments results (parameter 0 HSet.quineAtom) =>
      (function.val (laterArgument second)).val)
    (nativeFibreDecoder_right arguments results (parameter 0 HSet.quineAtom)
      (greatest (parameter 0 HSet.quineAtom)))
  exact Nat.succ.inj (firstValue.symm.trans (same.trans secondValue))

theorem parameter_still_not_original_small {I : Type} (reading : I → parameters.obj (stage 0)) :
    ¬ Function.Surjective reading := ContextualSmallFamilyUniverseControls.parameter_object_has_no_small_cover reading

end Mettapedia.TypeTheory.HostChoiceContextualNativeSmallFamiliesControls
