import Mettapedia.TypeTheory.ProjectionIndexedMonomorphismFibres
import Mettapedia.TypeTheory.CodomainClosedComprehension
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!

# Dependent operations on actual monomorphism slices

Composition along a monomorphism preserves admitted slice objects.
The actual dependent-product right adjoint preserves their monicity by
preserving the monic map to the actual terminal slice object. The restricted
adjunctions use the complete underlying slice hom equivalences.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.ProjectionIndexedMonomorphismComprehension

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory

universe u v
variable {C : Type (max u v)} [Category.{v} C] [HasFiniteLimits C]

def map {source target : C} (route : source ⟶ target) [Mono route] :
    MonicSlice source ⥤ MonicSlice target where
  obj object := ⟨(Over.map route).obj object.obj, by
    change Mono (object.obj.hom ≫ route)
    infer_instance⟩
  map arrow := ObjectProperty.homMk ((Over.map route).map arrow.hom)
  map_id _ := by apply ObjectProperty.hom_ext; exact (Over.map route).map_id _
  map_comp _ _ := by apply ObjectProperty.hom_ext; exact (Over.map route).map_comp _ _

def sumAdjunction {source target : C} (route : source ⟶ target) [Mono route] :
    map route ⊣ pullback route :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun first second => {
      toFun arrow := ObjectProperty.homMk
        ((Over.mapPullbackAdj route).homEquiv first.obj second.obj arrow.hom)
      invFun arrow := ObjectProperty.homMk
        (((Over.mapPullbackAdj route).homEquiv first.obj second.obj).symm arrow.hom)
      left_inv _ := Subsingleton.elim _ _
      right_inv _ := Subsingleton.elim _ _ }
    homEquiv_naturality_left_symm := by intros; apply Subsingleton.elim
    homEquiv_naturality_right := by intros; apply Subsingleton.elim }

theorem sumAdjunction_unit {source target : C} (route : source ⟶ target) [Mono route]
    (object : MonicSlice source) :
    ((sumAdjunction route).unit.app object).hom =
      (Over.mapPullbackAdj route).unit.app object.obj := by
  change (Over.mapPullbackAdj route).homEquiv object.obj _ (𝟙 _) = _
  exact (Over.mapPullbackAdj route).homEquiv_id _

theorem sumAdjunction_counit {source target : C} (route : source ⟶ target) [Mono route]
    (object : MonicSlice target) :
    ((sumAdjunction route).counit.app object).hom =
      (Over.mapPullbackAdj route).counit.app object.obj := by
  change ((Over.mapPullbackAdj route).homEquiv _ object.obj).symm (𝟙 _) = _
  exact (Over.mapPullbackAdj route).homEquiv_symm_id _

variable (model : CodomainClosedComprehension C)

theorem dependentProduct_mono {source target : C} (route : source ⟶ target)
    (object : MonicSlice source) :
    Mono ((model.dependentProduct route).obj object.obj).hom := by
  let : (model.dependentProduct route).IsRightAdjoint :=
    (model.dependentAdjunction route).isRightAdjoint
  let toTerminal : object.obj ⟶ Over.mk (𝟙 source) := Over.homMk object.obj.hom
  have : Mono toTerminal := by
    unfold toTerminal
    infer_instance
  let terminalComparison :=
    ((Over.mkIdTerminal (X := source)).isTerminalObj
      (model.dependentProduct route) _).uniqueUpToIso (Over.mkIdTerminal (X := target))
  let complete : (model.dependentProduct route).obj object.obj ⟶ Over.mk (𝟙 target) :=
    (model.dependentProduct route).map toTerminal ≫ terminalComparison.hom
  have : Mono complete := by
    unfold complete
    infer_instance
  have retained : complete.left = ((model.dependentProduct route).obj object.obj).hom := by
    have commutes := Over.w complete
    change complete.left ≫ 𝟙 target = _ at commutes
    exact (Category.comp_id _).symm.trans commutes
  rw [← retained]
  infer_instance

def product {source target : C} (route : source ⟶ target) :
    MonicSlice source ⥤ MonicSlice target where
  obj object := ⟨(model.dependentProduct route).obj object.obj,
    dependentProduct_mono model route object⟩
  map arrow := ObjectProperty.homMk ((model.dependentProduct route).map arrow.hom)
  map_id _ := by apply ObjectProperty.hom_ext; exact (model.dependentProduct route).map_id _
  map_comp _ _ := by apply ObjectProperty.hom_ext; exact (model.dependentProduct route).map_comp _ _

def productAdjunction {source target : C} (route : source ⟶ target) :
    pullback route ⊣ product model route :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun first second => {
      toFun arrow := ObjectProperty.homMk
        ((model.dependentAdjunction route).homEquiv first.obj second.obj arrow.hom)
      invFun arrow := ObjectProperty.homMk
        (((model.dependentAdjunction route).homEquiv first.obj second.obj).symm arrow.hom)
      left_inv _ := Subsingleton.elim _ _
      right_inv _ := Subsingleton.elim _ _ }
    homEquiv_naturality_left_symm := by intros; apply Subsingleton.elim
    homEquiv_naturality_right := by intros; apply Subsingleton.elim }

theorem productAdjunction_unit {source target : C} (route : source ⟶ target)
    (object : MonicSlice target) :
    ((productAdjunction model route).unit.app object).hom =
      (model.dependentAdjunction route).unit.app object.obj := by
  change (model.dependentAdjunction route).homEquiv object.obj _ (𝟙 _) = _
  exact (model.dependentAdjunction route).homEquiv_id _

theorem productAdjunction_counit {source target : C} (route : source ⟶ target)
    (object : MonicSlice source) :
    ((productAdjunction model route).counit.app object).hom =
      (model.dependentAdjunction route).counit.app object.obj := by
  change ((model.dependentAdjunction route).homEquiv _ object.obj).symm (𝟙 _) = _
  exact (model.dependentAdjunction route).homEquiv_symm_id _

end Mettapedia.TypeTheory.ProjectionIndexedMonomorphismComprehension
