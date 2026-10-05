import Mettapedia.TypeTheory.ContextualSmallFamilyNativeSigma
import Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormerControls

/-!
# Wider native consumers and genuinely future-dependent functions

The base retains arbitrary bare material parameters. The consumer itself
has wider fibres containing another arbitrary material value and growing
positions. Native abstraction and the original-bound cone abstraction
retain those source values. Complete future functions can agree on every
present application and still differ at newly available arguments.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyNativeControls

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open ContextualSmallFamilyUniverseControls ContextualSmallFamilyTypeFormerControls
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyNativeAdjunction ContextualNaturalSlices
open MaterialSets.Hypersets

def wideConsumers : parameters.Elements ⥤ Type 1 where
  obj point := HSet.{0} × Fin (point.1 + 1)
  map step := TypeCat.ofHom fun value =>
    ⟨value.1, Fin.castLE (Nat.succ_le_succ (leOfHom step.1)) value.2⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Prod.ext rfl (Fin.ext rfl)
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Prod.ext rfl (Fin.ext rfl)

def wideMethod : WiderPresheafDependentFunctions.Hom
    (WiderPresheafDependentFunctions.over cyclicSmall wideConsumers) positionResults where
  app argument consumer := ⟨min argument.2.1.val consumer.2.val, Nat.min_le_left _ _⟩
  naturality {first second} step consumer := by
    apply Subtype.ext
    exact congrArg (fun value => min value consumer.2.val)
      (congrArg (fun member : cyclicSmall.obj second.1 => member.1.val) step.2)

def nativeFunctions : WiderPresheafDependentFunctions.Hom wideConsumers
    (WiderPresheafDependentFunctions.dependentFunctions cyclicSmall positionResults) :=
  WiderPresheafDependentFunctions.curry wideMethod

def smallFunctions : WiderPresheafDependentFunctions.Hom wideConsumers (pi cyclicSmall positionResults) :=
  smallCurry cyclicSmall positionResults wideMethod

theorem full_native_small_abstraction_square :
    nativeFunctions.comp (nativeToSmall cyclicSmall positionResults) = smallFunctions :=
  smallCurry_native cyclicSmall positionResults wideMethod

theorem wider_consumer_beta (point : parameters.Elements) (consumer : wideConsumers.obj point)
    (argument : cyclicSmall.obj point) :
    (evaluateValue cyclicSmall positionResults point (smallFunctions.app point consumer) argument).val =
      min argument.1.val consumer.2.val :=
  congrArg Subtype.val (congrArg (fun operation => operation.app ⟨point, argument⟩ consumer)
    (small_uncurry_curry cyclicSmall positionResults wideMethod))

theorem wider_consumers_not_original_small {I : Type}
    (reading : I → wideConsumers.obj (parameter 0 HSet.quineAtom)) : ¬ Function.Surjective reading := by
  intro covers
  apply parameter_object_has_no_small_cover (fun code => (reading code).1)
  intro material
  obtain ⟨code, same⟩ := covers ⟨material, 0⟩
  exact ⟨code, congrArg Prod.fst same⟩

def nativeGreatest :
    (WiderPresheafDependentFunctions.dependentFunctions cyclicSmall positionResults).sections :=
  (smallToNative cyclicSmall positionResults).mapSection greatestSection

def nativeZero :
    (WiderPresheafDependentFunctions.dependentFunctions cyclicSmall positionResults).sections :=
  (smallToNative cyclicSmall positionResults).mapSection zeroSection

theorem native_same_present (material : HSet.{0}) (argument : cyclicSmall.obj (parameter 0 material)) :
    (nativeGreatest.val (parameter 0 material)).app (parameter 0 material) (𝟙 _) argument =
      (nativeZero.val (parameter 0 material)).app (parameter 0 material) (𝟙 _) argument := by
  have greatest := evaluation_compression cyclicSmall positionResults (parameter 0 material)
    (nativeGreatest.val (parameter 0 material)) argument
  have zero := evaluation_compression cyclicSmall positionResults (parameter 0 material)
    (nativeZero.val (parameter 0 material)) argument
  have greatestInverse := congrArg (fun operation => operation.app (parameter 0 material)
    (greatestSection.val (parameter 0 material))) (native_small_right cyclicSmall positionResults)
  have zeroInverse := congrArg (fun operation => operation.app (parameter 0 material)
    (zeroSection.val (parameter 0 material))) (native_small_right cyclicSmall positionResults)
  change (nativeToSmall cyclicSmall positionResults).app _ (nativeGreatest.val _) = greatestSection.val _ at greatestInverse
  change (nativeToSmall cyclicSmall positionResults).app _ (nativeZero.val _) = zeroSection.val _ at zeroInverse
  rw [greatestInverse] at greatest
  rw [zeroInverse] at zero
  exact greatest.symm.trans ((same_present_all_arguments material argument).trans zero)

theorem native_distinct_complete_futures :
    nativeGreatest.val (parameter 0 HSet.quineAtom) ≠ nativeZero.val (parameter 0 HSet.quineAtom) := by
  intro same
  apply different_whole_future_functions
  have functions := congrArg ((nativeToSmall cyclicSmall positionResults).app (parameter 0 HSet.quineAtom)) same
  have greatestInverse := congrArg (fun operation => operation.app (parameter 0 HSet.quineAtom)
    (greatestSection.val (parameter 0 HSet.quineAtom))) (native_small_right cyclicSmall positionResults)
  have zeroInverse := congrArg (fun operation => operation.app (parameter 0 HSet.quineAtom)
    (zeroSection.val (parameter 0 HSet.quineAtom))) (native_small_right cyclicSmall positionResults)
  exact greatestInverse.symm.trans (functions.trans zeroInverse)

def actualWideConsumer := ContextualSmallFamilyUniverse.projection wideConsumers

def actualConsumerBody : WiderPresheafDependentFunctions.Hom
    (WiderPresheafDependentFunctions.over cyclicSmall (fibres actualWideConsumer)) positionResults where
  app argument consumer := ⟨min argument.2.1.val consumer.val.2.2.val, Nat.min_le_left _ _⟩
  naturality {first second} step consumer := by
    apply Subtype.ext
    exact congrArg (fun value => min value consumer.val.2.2.val)
      (congrArg (fun member : cyclicSmall.obj second.1 => member.1.val) step.2)

def actualPullbackBody :=
  ContextualSmallFamilyNativeSlice.familyBodyToPullback cyclicSmall positionResults actualWideConsumer actualConsumerBody

def actualCodomainFunction :=
  ContextualSmallFamilyNativeSlice.transpose cyclicSmall positionResults actualWideConsumer actualPullbackBody

theorem actual_codomain_beta :
    (pullbackMap actualCodomainFunction (ContextualSmallFamilyUniverse.projection cyclicSmall)).comp
      (ContextualSmallFamilyNativeSlice.evaluation cyclicSmall positionResults) = actualPullbackBody :=
  ContextualSmallFamilyNativeSlice.codomain_beta cyclicSmall positionResults actualWideConsumer actualPullbackBody

theorem actual_codomain_retains_original_parent (stage : Nat)
    (value : (ContextualSmallFamilyUniverse.total wideConsumers).obj stage) :
    (actualCodomainFunction.mapping.app stage value).1 = value.1 :=
  actualCodomainFunction.square stage value

theorem actual_codomain_has_original_small_function_fibres (stage : Nat)
    (value : (ContextualSmallFamilyUniverse.total wideConsumers).obj stage) :
    ∃ function : ProductAt cyclicSmall positionResults (parameter stage value.1),
      actualCodomainFunction.mapping.app stage value = ⟨value.1, function⟩ := by
  let function := (fromTotal actualWideConsumer (pi cyclicSmall positionResults) actualCodomainFunction).app
    (parameter stage value.1) ⟨value, rfl⟩
  exact ⟨function, (congrArg (fun mapping => mapping.mapping.app stage value)
    (to_fromTotal actualWideConsumer (pi cyclicSmall positionResults) actualCodomainFunction)).symm⟩

end Mettapedia.TypeTheory.ContextualSmallFamilyNativeControls
