import Mettapedia.TypeTheory.ProjectionIndexedMonomorphismComprehension

/-!

# Actual Beck--Chevalley mates on monomorphism fibres

The selected sum and product mates are compared with the complete
slice comparisons. Their reverse maps retain the independently constructed
slice witnesses; their inverse equations use the earned monicity of the
actual codomains. Thus the proof applies to the selected adjunction mates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.ProjectionIndexedMonomorphismComprehension

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Functor
open HasFibers
open Mettapedia.CategoryTheory Mettapedia.CategoryTheory.FibrationTwoCategory
open MonoArrowImageAdjunction ProjectionIndexedComprehension

universe u v
variable {C : Type (max u v)} [Category.{v} C] [HasFiniteLimits C]

local instance baseChangeLimits : HasFiniteLimits (predicates C).Base :=
  inferInstanceAs (HasFiniteLimits C)

local instance baseChangeFibres : HasFibers.{v,max u v} (predicates C).functor := fibres

local instance displayMono (object : Predicate C) :
    Mono (Comprehension.displayProjection fullComprehension object) := projection_mono object

variable (model : CodomainClosedComprehension C)
  {source target : Predicate C} (arrow : source ⟶ target)
  (cartesian : (projection C).IsCartesian arrow.hom.right arrow)

include cartesian

theorem displaySquare :
    IsPullback (fullComprehension.display.map arrow).left
      (Comprehension.displayProjection fullComprehension source)
      (Comprehension.displayProjection fullComprehension target)
      ((predicates C).functor.map arrow) := by
  rw [projection_eq, projection_eq]
  exact (cartesian_iff_pullback arrow).mp cartesian

set_option backward.isDefEq.respectTransparency.types false in
def sumComparisonComponent (object : MonicSlice target.obj.left) :
    (pullback (fullComprehension.display.map arrow).left ⋙
      map (Comprehension.displayProjection fullComprehension source)).obj object ≅
    (map (Comprehension.displayProjection fullComprehension target) ⋙
      pullback ((predicates C).functor.map arrow)).obj object where
  hom := ObjectProperty.homMk
    ((SliceBeckChevalley.sigmaBaseChange (displaySquare arrow cartesian)).hom.app object.obj)
  inv := ObjectProperty.homMk
    ((SliceBeckChevalley.sigmaBaseChange (displaySquare arrow cartesian)).inv.app object.obj)
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency.types false in
def productComparisonComponent (object : MonicSlice target.obj.left) :
    (product model (Comprehension.displayProjection fullComprehension target) ⋙
      pullback ((predicates C).functor.map arrow)).obj object ≅
    (pullback (fullComprehension.display.map arrow).left ⋙
      product model (Comprehension.displayProjection fullComprehension source)).obj object where
  hom := ObjectProperty.homMk
    ((model.productBaseChange (displaySquare arrow cartesian)).hom.app object.obj)
  inv := ObjectProperty.homMk
    ((model.productBaseChange (displaySquare arrow cartesian)).inv.app object.obj)
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency.types false in
theorem sumBaseChange_underlying (object : MonicSlice target.obj.left) :
    (((data model).sumBaseChange arrow).app object).hom =
      (SliceBeckChevalley.sigmaBaseChange (displaySquare arrow cartesian)).hom.app object.obj := by
  let first :=
    (pullback (fullComprehension.display.map arrow).left ⋙
      map (Comprehension.displayProjection fullComprehension source)).obj object
  let second :=
    (map (Comprehension.displayProjection fullComprehension target) ⋙
      pullback ((predicates C).functor.map arrow)).obj object
  exact congrArg (fun map : first ⟶ second => map.hom)
    (@Subsingleton.elim (first ⟶ second) (monicSlice_hom_subsingleton first second)
    (((data model).sumBaseChange arrow).app object)
    (sumComparisonComponent arrow cartesian object).hom)

set_option backward.isDefEq.respectTransparency.types false in
theorem productBaseChange_underlying (object : MonicSlice target.obj.left) :
    (((data model).productBaseChange arrow).app object).hom =
      (model.productBaseChange (displaySquare arrow cartesian)).hom.app object.obj := by
  let first :=
    (product model (Comprehension.displayProjection fullComprehension target) ⋙
      pullback ((predicates C).functor.map arrow)).obj object
  let second :=
    (pullback (fullComprehension.display.map arrow).left ⋙
      product model (Comprehension.displayProjection fullComprehension source)).obj object
  exact congrArg (fun map : first ⟶ second => map.hom)
    (@Subsingleton.elim (first ⟶ second) (monicSlice_hom_subsingleton first second)
    (((data model).productBaseChange arrow).app object)
    (productComparisonComponent model arrow cartesian object).hom)

set_option backward.isDefEq.respectTransparency.types false in
theorem sumBaseChange_isIso : IsIso ((data model).sumBaseChange arrow) := by
  have components : ∀ object, IsIso (((data model).sumBaseChange arrow).app object) := by
    intro object
    let first :=
      (pullback (fullComprehension.display.map arrow).left ⋙
        map (Comprehension.displayProjection fullComprehension source)).obj object
    let second :=
      (map (Comprehension.displayProjection fullComprehension target) ⋙
        pullback ((predicates C).functor.map arrow)).obj object
    let forward : first ⟶ second := ((data model).sumBaseChange arrow).app object
    let reverse := (sumComparisonComponent arrow cartesian object).inv
    change IsIso forward
    exact ⟨⟨reverse,
      @Subsingleton.elim (first ⟶ first) (monicSlice_hom_subsingleton first first) _ _,
      @Subsingleton.elim (second ⟶ second) (monicSlice_hom_subsingleton second second) _ _⟩⟩
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ components

set_option backward.isDefEq.respectTransparency.types false in
theorem productBaseChange_isIso : IsIso ((data model).productBaseChange arrow) := by
  have components : ∀ object, IsIso (((data model).productBaseChange arrow).app object) := by
    intro object
    let first :=
      (product model (Comprehension.displayProjection fullComprehension target) ⋙
        pullback ((predicates C).functor.map arrow)).obj object
    let second :=
      (pullback (fullComprehension.display.map arrow).left ⋙
        product model (Comprehension.displayProjection fullComprehension source)).obj object
    let forward : first ⟶ second := ((data model).productBaseChange arrow).app object
    let reverse := (productComparisonComponent model arrow cartesian object).inv
    change IsIso forward
    exact ⟨⟨reverse,
      @Subsingleton.elim (first ⟶ first) (monicSlice_hom_subsingleton first first) _ _,
      @Subsingleton.elim (second ⟶ second) (monicSlice_hom_subsingleton second second) _ _⟩⟩
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ components

omit cartesian in
def closed : ProjectionIndexedComprehension.Closed.{max u v,v,max u v,v} (predicates C) where
  toData := data model
  sumBeckChevalley arrow cartesian := sumBaseChange_isIso model arrow cartesian
  productBeckChevalley arrow cartesian := productBaseChange_isIso model arrow cartesian

end Mettapedia.TypeTheory.ProjectionIndexedMonomorphismComprehension
