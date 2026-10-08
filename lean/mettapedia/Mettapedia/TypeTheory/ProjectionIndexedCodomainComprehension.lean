import Mettapedia.TypeTheory.ProjectionIndexedComprehension
import Mettapedia.TypeTheory.CodomainFibrationComprehensionProfile

/-!
# The projection-indexed closed codomain comprehension

The operations use the actual slices and the independently constructed
dependent-product adjunctions. Cartesian display squares supply the
parameter comparisons. Their adjunction mates are identified with the
canonical slice base-change maps, rather than with unrelated isomorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.ProjectionIndexedCodomainComprehension

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Functor
open HasFibers
open Mettapedia.CategoryTheory
open Mettapedia.CategoryTheory.FibrationTwoCategory
open ProjectionIndexedComprehension

universe u v
variable {C : Type (max u v)} [Category.{v} C] [HasFiniteLimits C]

local instance codomainFibres : HasFibers.{v,max u v} (codomain C).functor :=
  CodomainComprehension.sliceFibres

local instance codomainTerminal : HasTerminal (codomain C).Base :=
  inferInstanceAs (HasTerminal C)

local instance codomainPullbacks : HasPullbacks (codomain C).Base :=
  inferInstanceAs (HasPullbacks C)

def data (model : CodomainClosedComprehension C) :
    Data.{max u v,v,max u v,v} (codomain C) :=
  Data.ofStrong (CodomainFibrationComprehensionProfile.closed model)

theorem projection_eq (object : Arrow C) :
    ProjectionIndexedComprehension.Comprehension.displayProjection
        CodomainFibrationComprehensionProfile.comprehension object = object.hom := by
  change object.hom ≫ 𝟙 object.right = object.hom
  exact Category.comp_id _

theorem displaySquare {source target : Arrow C} (arrow : source ⟶ target)
    (cartesian : Arrow.rightFunc.IsCartesian arrow.right arrow) :
    IsPullback arrow.left
      (ProjectionIndexedComprehension.Comprehension.displayProjection
        CodomainFibrationComprehensionProfile.comprehension source)
      (ProjectionIndexedComprehension.Comprehension.displayProjection
        CodomainFibrationComprehensionProfile.comprehension target) arrow.right := by
  rw [projection_eq, projection_eq]
  exact (CodomainComprehension.cartesian_iff_pullback arrow).mp cartesian

variable (model : CodomainClosedComprehension C)
  {source target : Arrow C} (arrow : source ⟶ target)

theorem parameterSquare_lift (object : Over target.right) :
    (CodomainComprehension.fibreInclusion source.left).map
        (((data model).parameterSquare arrow).hom.app object) ≫
      ProjectionIndexedComprehension.Substitution.composedLift
        CodomainFibrationComprehensionProfile.substitution
        (ProjectionIndexedComprehension.Comprehension.displayProjection
          CodomainFibrationComprehensionProfile.comprehension source) arrow.right object =
    ProjectionIndexedComprehension.Substitution.composedLift
      CodomainFibrationComprehensionProfile.substitution arrow.left
      (ProjectionIndexedComprehension.Comprehension.displayProjection
        CodomainFibrationComprehensionProfile.comprehension target) object :=
  ProjectionIndexedComprehension.Substitution.square_lift
    CodomainFibrationComprehensionProfile.substitution
    (ProjectionIndexedComprehension.Comprehension.displayProjection_naturality
      CodomainFibrationComprehensionProfile.comprehension arrow) object

section BaseChange

variable {first second third fourth : C}
  {top : first ⟶ second} {left : first ⟶ third}
  {right : second ⟶ fourth} {bottom : third ⟶ fourth}

theorem pullback_map_fst {domain codomain : C} (route : domain ⟶ codomain)
    {firstObject secondObject : Over codomain} (map : firstObject ⟶ secondObject) :
    ((Over.pullback route).map map).left ≫ pullback.fst secondObject.hom route =
      pullback.fst firstObject.hom route ≫ map.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

def sumRightMate (square : IsPullback top left right bottom) :
    Over.pullback right ⋙ Over.pullback top ⟶ Over.pullback bottom ⋙ Over.pullback left :=
  (mateEquiv (Over.mapPullbackAdj right) (Over.mapPullbackAdj left)
    (TwoSquare.mk _ _ _ _ (SliceBeckChevalley.sigmaBaseChange square).hom)).natTrans

set_option backward.isDefEq.respectTransparency.types false in
theorem sumRightMate_lift (square : IsPullback top left right bottom)
    (object : Over fourth) :
    (CodomainComprehension.fibreInclusion first).map
        ((sumRightMate square).app object) ≫
      Substitution.composedLift CodomainFibrationComprehensionProfile.substitution
        left bottom object =
    Substitution.composedLift CodomainFibrationComprehensionProfile.substitution
      top right object := by
  apply Arrow.hom_ext
  · have counit : (Over.map left).map ((sumRightMate square).app object) ≫
        (Over.mapPullbackAdj left).counit.app ((Over.pullback bottom).obj object) =
      (SliceBeckChevalley.sigmaBaseChange square).hom.app ((Over.pullback right).obj object) ≫
        (Over.pullback bottom).map ((Over.mapPullbackAdj right).counit.app object) :=
      mateEquiv_counit (Over.mapPullbackAdj right) (Over.mapPullbackAdj left)
        (TwoSquare.mk _ _ _ _ (SliceBeckChevalley.sigmaBaseChange square).hom) object
    have retained := congrArg Over.Hom.left counit
    simp only [Over.comp_left, Over.map_map_left, Over.mapPullbackAdj_counit_app,
      Over.homMk_left, Over.pullback_obj_hom]
      at retained
    change ((sumRightMate square).app object).left ≫
        pullback.fst (pullback.snd object.hom bottom) left = _ at retained
    change ((sumRightMate square).app object).left ≫
        (pullback.fst (pullback.snd object.hom bottom) left ≫ pullback.fst object.hom bottom) =
      pullback.fst (pullback.snd object.hom right) top ≫ pullback.fst object.hom right
    have projected := pullback_map_fst bottom ((Over.mapPullbackAdj right).counit.app object)
    simp only [Over.mapPullbackAdj_counit_app, Over.homMk_left,
      Functor.id_obj, Functor.comp_obj, Over.map_obj_hom] at projected
    rw [← Category.assoc, retained, Category.assoc, projected]
    change ((SliceBeckChevalley.sigmaBaseChange square).hom.app
        ((Over.pullback right).obj object)).left ≫
        (pullback.fst (((Over.pullback right).obj object).hom ≫ right) bottom ≫
          pullback.fst object.hom right) = _
    rw [← Category.assoc]
    exact congrArg (fun map => map ≫ pullback.fst object.hom right)
      (SliceBeckChevalley.sigmaBaseChangeComponent_fst square
        ((Over.pullback right).obj object))
  · change 𝟙 first ≫ (left ≫ bottom) = top ≫ right
    exact (Category.id_comp _).trans square.w.symm

theorem sumRightMate_eq_square (square : IsPullback top left right bottom) :
    sumRightMate square =
      (Substitution.square CodomainFibrationComprehensionProfile.substitution square.w).hom := by
  apply NatTrans.ext
  funext object
  apply Fib.hom_ext (p := (codomain C).functor)
  let chosen := CodomainFibrationComprehensionProfile.substitution (C := C)
  let := Substitution.composedLift_cartesian chosen left bottom object
  apply IsCartesian.ext (codomain C).functor (left ≫ bottom)
    (Substitution.composedLift chosen left bottom object)
  exact (sumRightMate_lift square object).trans
    (Substitution.square_lift chosen square.w object).symm

def sumLeftMate (square : IsPullback top left right bottom) :
    Over.pullback top ⋙ Over.map left ⟶ Over.map right ⋙ Over.pullback bottom :=
  ((mateEquiv (Over.mapPullbackAdj right) (Over.mapPullbackAdj left)).symm
    (TwoSquare.mk _ _ _ _
      (Substitution.square CodomainFibrationComprehensionProfile.substitution square.w).hom)).natTrans

theorem sumLeftMate_eq_baseChange (square : IsPullback top left right bottom) :
    sumLeftMate square = (SliceBeckChevalley.sigmaBaseChange square).hom := by
  let exchange := mateEquiv (G := Over.pullback top) (H := Over.pullback bottom)
    (Over.mapPullbackAdj right) (Over.mapPullbackAdj left)
  have whole : exchange (TwoSquare.mk _ _ _ _
      (SliceBeckChevalley.sigmaBaseChange square).hom) =
      TwoSquare.mk _ _ _ _
        (Substitution.square CodomainFibrationComprehensionProfile.substitution square.w).hom := by
    exact sumRightMate_eq_square square
  have restored := congrArg (fun comparison => (exchange.symm comparison).natTrans) whole
  simp only [Equiv.symm_apply_apply] at restored
  exact restored.symm

def productRightMate (square : IsPullback top left right bottom) :
    model.dependentProduct right ⋙ Over.pullback bottom ⟶
      Over.pullback top ⋙ model.dependentProduct left :=
  (mateEquiv (model.dependentAdjunction right) (model.dependentAdjunction left)
    (TwoSquare.mk _ _ _ _
      (Substitution.square CodomainFibrationComprehensionProfile.substitution square.w).inv)).natTrans

theorem productRightMate_evaluation (square : IsPullback top left right bottom)
    (object : Over second) :
    (Over.pullback left).map ((productRightMate model square).app object) ≫
        model.evaluation left ((Over.pullback top).obj object) =
      (Substitution.square CodomainFibrationComprehensionProfile.substitution square.w).inv.app
          ((model.dependentProduct right).obj object) ≫
        (Over.pullback top).map (model.evaluation right object) :=
  mateEquiv_counit (model.dependentAdjunction right) (model.dependentAdjunction left)
    (TwoSquare.mk _ _ _ _
      (Substitution.square CodomainFibrationComprehensionProfile.substitution square.w).inv) object

set_option backward.isDefEq.respectTransparency.types false in
theorem productRightMate_compound_evaluation (square : IsPullback top left right bottom)
    (object : Over second) :
    (Over.pullback left ⋙ Over.map top).map ((productRightMate model square).app object) ≫
        ((model.dependentAdjunction left).comp (Over.mapPullbackAdj top)).counit.app object =
      (SliceBeckChevalley.sigmaBaseChange square.flip).hom.app
          ((model.dependentProduct right ⋙ Over.pullback bottom).obj object) ≫
        ((Over.mapPullbackAdj bottom).comp (model.dependentAdjunction right)).counit.app object := by
  have outer : (Over.map top).map
      ((sumRightMate square.flip).app ((model.dependentProduct right).obj object)) ≫
      (Over.mapPullbackAdj top).counit.app
        ((Over.pullback right).obj ((model.dependentProduct right).obj object)) =
    (SliceBeckChevalley.sigmaBaseChange square.flip).hom.app
        ((Over.pullback bottom).obj ((model.dependentProduct right).obj object)) ≫
      (Over.pullback right).map
        ((Over.mapPullbackAdj bottom).counit.app ((model.dependentProduct right).obj object)) :=
    mateEquiv_counit (Over.mapPullbackAdj bottom) (Over.mapPullbackAdj top)
      (TwoSquare.mk _ _ _ _ (SliceBeckChevalley.sigmaBaseChange square.flip).hom)
      ((model.dependentProduct right).obj object)
  rw [sumRightMate_eq_square,
    Substitution.square_flip CodomainFibrationComprehensionProfile.substitution square.w] at outer
  simp only [Iso.symm_hom] at outer
  have inner : (Over.pullback left).map ((productRightMate model square).app object) ≫
        (model.dependentAdjunction left).counit.app ((Over.pullback top).obj object) =
      (Substitution.square CodomainFibrationComprehensionProfile.substitution square.w).inv.app
          ((model.dependentProduct right).obj object) ≫
        (Over.pullback top).map ((model.dependentAdjunction right).counit.app object) :=
    productRightMate_evaluation model square object
  simp only [Adjunction.comp_counit_app, Functor.comp_map]
  rw [← Category.assoc, ← (Over.map top).map_comp, inner,
    (Over.map top).map_comp, Category.assoc]
  have natural := (Over.mapPullbackAdj top).counit.naturality
    ((model.dependentAdjunction right).counit.app object)
  change (Over.map top).map
      ((Over.pullback top).map ((model.dependentAdjunction right).counit.app object)) ≫
      (Over.mapPullbackAdj top).counit.app object =
    (Over.mapPullbackAdj top).counit.app
        ((Over.pullback right).obj ((model.dependentProduct right).obj object)) ≫
      (model.dependentAdjunction right).counit.app object at natural
  rw [natural, ← Category.assoc, outer]
  exact Category.assoc _ _ _

theorem productRightMate_eq_baseChange (square : IsPullback top left right bottom) :
    productRightMate model square = (model.productBaseChange square).hom := by
  apply NatTrans.ext
  funext object
  apply (((model.dependentAdjunction left).comp (Over.mapPullbackAdj top)).homEquiv
    ((model.dependentProduct right ⋙ Over.pullback bottom).obj object) object).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  exact (productRightMate_compound_evaluation model square object).trans
    (model.productBaseChange_evaluation square object).symm

end BaseChange

set_option backward.isDefEq.respectTransparency.types false in
theorem sumBaseChange_eq
    (cartesian : Arrow.rightFunc.IsCartesian arrow.right arrow) :
    (data model).sumBaseChange arrow =
      (SliceBeckChevalley.sigmaBaseChange (displaySquare arrow cartesian)).hom := by
  dsimp only [Data.sumBaseChange, Data.parameterSquare, data, Data.ofStrong]
  change ((mateEquiv
      (Over.mapPullbackAdj (Comprehension.displayProjection
        CodomainFibrationComprehensionProfile.comprehension target))
      (Over.mapPullbackAdj (Comprehension.displayProjection
        CodomainFibrationComprehensionProfile.comprehension source))).symm
    (TwoSquare.mk _ _ _ _ (Substitution.square
      CodomainFibrationComprehensionProfile.substitution
      (Comprehension.displayProjection_naturality
        CodomainFibrationComprehensionProfile.comprehension arrow)).hom)).natTrans = _
  exact sumLeftMate_eq_baseChange (displaySquare arrow cartesian)

set_option backward.isDefEq.respectTransparency.types false in
theorem productBaseChange_eq
    (cartesian : Arrow.rightFunc.IsCartesian arrow.right arrow) :
    (data model).productBaseChange arrow =
      (model.productBaseChange (displaySquare arrow cartesian)).hom := by
  dsimp only [Data.productBaseChange, Data.parameterSquare, data, Data.ofStrong]
  change (mateEquiv
      (model.dependentAdjunction (Comprehension.displayProjection
        CodomainFibrationComprehensionProfile.comprehension target))
      (model.dependentAdjunction (Comprehension.displayProjection
        CodomainFibrationComprehensionProfile.comprehension source))
    (TwoSquare.mk _ _ _ _ (Substitution.square
      CodomainFibrationComprehensionProfile.substitution
      (Comprehension.displayProjection_naturality
        CodomainFibrationComprehensionProfile.comprehension arrow)).inv)).natTrans = _
  exact productRightMate_eq_baseChange model (displaySquare arrow cartesian)

def closed : ProjectionIndexedComprehension.Closed.{max u v,v,max u v,v} (codomain C) where
  toData := data model
  sumBeckChevalley arrow cartesian := by
    change Arrow.rightFunc.IsCartesian arrow.right arrow at cartesian
    rw [sumBaseChange_eq model arrow cartesian]
    infer_instance
  productBeckChevalley arrow cartesian := by
    change Arrow.rightFunc.IsCartesian arrow.right arrow at cartesian
    rw [productBaseChange_eq model arrow cartesian]
    infer_instance

end Mettapedia.TypeTheory.ProjectionIndexedCodomainComprehension
