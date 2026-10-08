import Mettapedia.TypeTheory.ProjectionIndexedComprehensionBaseChange

/-!
# Closed comprehension along display projections

Dependent sums and products are required only along the comprehension
projections. Parameter substitution is tested on the actual canonical
adjunction mates of Cartesian squares. Strong sums retain the canonical
domain arrow formed by their unit and the chosen Cartesian lift.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.ProjectionIndexedComprehension

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Functor
open HasFibers
open Mettapedia.CategoryTheory.FibrationTwoCategory

universe u v f h

namespace Comprehension

variable {projection : Fibration.{u,v}}
  (chosen : FibrationComprehensionProfile.Comprehension projection)

theorem base_eq (object : projection.Total) :
    (chosen.display.obj object).right = projection.functor.obj object :=
  Functor.congr_obj chosen.over object

def displayProjection (object : projection.Total) :
    (chosen.display.obj object).left ⟶ projection.functor.obj object :=
  (chosen.display.obj object).hom ≫ eqToHom (base_eq chosen object)

theorem displayProjection_naturality {source target : projection.Total}
    (arrow : source ⟶ target) :
    (chosen.display.map arrow).left ≫ displayProjection chosen target =
      displayProjection chosen source ≫ projection.functor.map arrow := by
  unfold displayProjection
  rw [← Category.assoc, Arrow.w]
  have baseMap := Functor.congr_hom chosen.over arrow
  change (chosen.display.map arrow).right =
    eqToHom (base_eq chosen source) ≫ projection.functor.map arrow ≫
      eqToHom (base_eq chosen target).symm at baseMap
  rw [Category.assoc, baseMap]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

end Comprehension

set_option linter.checkUnivs false in
structure Data (projection : Fibration.{u,v})
    [HasFibers.{h,f} projection.functor] where
  comprehension : FibrationComprehensionProfile.Comprehension projection
  substitution : FibrationComprehensionProfile.Substitution projection
  terminal : HasTerminal projection.Base
  sum : (object : projection.Total) →
    Fib projection.functor (comprehension.display.obj object).left ⥤
      Fib projection.functor (projection.functor.obj object)
  product : (object : projection.Total) →
    Fib projection.functor (comprehension.display.obj object).left ⥤
      Fib projection.functor (projection.functor.obj object)
  sumAdjunction : ∀ object,
    sum object ⊣ substitution.reindex (Comprehension.displayProjection comprehension object)
  productAdjunction : ∀ object,
    substitution.reindex (Comprehension.displayProjection comprehension object) ⊣ product object
  strongSum : ∀ (object : projection.Total)
      (result : Fib projection.functor (comprehension.display.obj object).left),
    IsIso ((comprehension.display ⋙ Arrow.leftFunc).map
      ((ι (comprehension.display.obj object).left).map ((sumAdjunction object).unit.app result) ≫
        (substitution.lift (Comprehension.displayProjection comprehension object)).app
          ((sum object).obj result)))

namespace Data

variable {projection : Fibration.{u,v}} [HasFibers.{h,f} projection.functor]
  (model : Data.{u,v,f,h} projection)

/-- Restriction of the operations forgets the demand for quantification
along every base arrow. Beck--Chevalley is not inferred by this data map. -/
def ofStrong (strong : FibrationComprehensionProfile.Closed.{u,v,f,h} projection)
    [HasTerminal projection.Base] : Data.{u,v,f,h} projection where
  comprehension := strong.comprehension
  substitution := strong.substitution
  terminal := inferInstance
  sum object := strong.sum (Comprehension.displayProjection strong.comprehension object)
  product object := strong.product (Comprehension.displayProjection strong.comprehension object)
  sumAdjunction object :=
    strong.sumAdjunction (Comprehension.displayProjection strong.comprehension object)
  productAdjunction object :=
    strong.productAdjunction (Comprehension.displayProjection strong.comprehension object)
  strongSum object result :=
    strong.strongSum (Comprehension.displayProjection strong.comprehension object) result

def parameterSquare {source target : projection.Total} (arrow : source ⟶ target) :
    model.substitution.reindex (Comprehension.displayProjection model.comprehension target) ⋙
        model.substitution.reindex (model.comprehension.display.map arrow).left ≅
      model.substitution.reindex (projection.functor.map arrow) ⋙
        model.substitution.reindex (Comprehension.displayProjection model.comprehension source) :=
  Substitution.square model.substitution
    (Comprehension.displayProjection_naturality model.comprehension arrow)

def sumBaseChange {source target : projection.Total} (arrow : source ⟶ target) :
    model.substitution.reindex (model.comprehension.display.map arrow).left ⋙ model.sum source ⟶
      model.sum target ⋙ model.substitution.reindex (projection.functor.map arrow) :=
  ((mateEquiv (model.sumAdjunction target) (model.sumAdjunction source)).symm
    (TwoSquare.mk _ _ _ _ (parameterSquare model arrow).hom)).natTrans

def productBaseChange {source target : projection.Total} (arrow : source ⟶ target) :
    model.product target ⋙ model.substitution.reindex (projection.functor.map arrow) ⟶
      model.substitution.reindex (model.comprehension.display.map arrow).left ⋙ model.product source :=
  (mateEquiv (model.productAdjunction target) (model.productAdjunction source)
    (TwoSquare.mk _ _ _ _ (parameterSquare model arrow).inv)).natTrans

theorem sumBaseChange_unit {source target : projection.Total} (arrow : source ⟶ target)
    (object : Fib projection.functor (model.comprehension.display.obj target).left) :
    (model.substitution.reindex (model.comprehension.display.map arrow).left).map
        ((model.sumAdjunction target).unit.app object) ≫
      (parameterSquare model arrow).hom.app ((model.sum target).obj object) =
    (model.sumAdjunction source).unit.app
        ((model.substitution.reindex (model.comprehension.display.map arrow).left).obj object) ≫
      (model.substitution.reindex
        (Comprehension.displayProjection model.comprehension source)).map
        ((sumBaseChange model arrow).app object) :=
  unit_mateEquiv_symm (model.sumAdjunction target) (model.sumAdjunction source)
    (TwoSquare.mk _ _ _ _ (parameterSquare model arrow).hom) object

theorem productBaseChange_evaluation {source target : projection.Total}
    (arrow : source ⟶ target)
    (object : Fib projection.functor (model.comprehension.display.obj target).left) :
    (model.substitution.reindex
        (Comprehension.displayProjection model.comprehension source)).map
        ((productBaseChange model arrow).app object) ≫
      (model.productAdjunction source).counit.app
        ((model.substitution.reindex (model.comprehension.display.map arrow).left).obj object) =
    (parameterSquare model arrow).inv.app ((model.product target).obj object) ≫
      (model.substitution.reindex (model.comprehension.display.map arrow).left).map
        ((model.productAdjunction target).counit.app object) :=
  mateEquiv_counit (model.productAdjunction target) (model.productAdjunction source)
    (TwoSquare.mk _ _ _ _ (parameterSquare model arrow).inv) object

end Data

set_option linter.checkUnivs false in
structure Closed (projection : Fibration.{u,v}) [HasFibers.{h,f} projection.functor]
    extends Data.{u,v,f,h} projection where
  sumBeckChevalley : ∀ {source target : projection.Total} (arrow : source ⟶ target),
    projection.functor.IsCartesian (projection.functor.map arrow) arrow →
      IsIso (toData.sumBaseChange arrow)
  productBeckChevalley : ∀ {source target : projection.Total} (arrow : source ⟶ target),
    projection.functor.IsCartesian (projection.functor.map arrow) arrow →
      IsIso (toData.productBaseChange arrow)

end Mettapedia.TypeTheory.ProjectionIndexedComprehension
