import Mettapedia.CategoryTheory.FibrationTwoCategory
import Mathlib.CategoryTheory.FiberedCategory.HasFibers
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Full closed comprehension profiles on actual fibrations

A profile includes a full comprehension functor over the actual base, its
unit adjunctions, and actual Cartesian lifts in chosen equivalent fibres.
Dependent sums and products are genuine adjoints to those substitutions.
Strong sums concern the domain map of the canonical total arrow formed
from the sum unit followed by the Cartesian lift.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.FibrationComprehensionProfile

open _root_.CategoryTheory _root_.CategoryTheory.Functor
  _root_.CategoryTheory.Limits
open HasFibers
open Mettapedia.CategoryTheory.FibrationTwoCategory

universe u v f h

structure Comprehension (projection : Fibration.{u,v}) where
  display : projection.Total ⥤ Arrow projection.Base
  over : display ⋙ Arrow.rightFunc = projection.functor
  [full : display.Full]
  [faithful : display.Faithful]
  cartesian : ∀ {first second : projection.Total} (arrow : first ⟶ second),
    projection.functor.IsCartesian (projection.functor.map arrow) arrow →
      IsPullback (display.map arrow).left (display.obj first).hom
        (display.obj second).hom (display.map arrow).right
  unit : projection.Base ⥤ projection.Total
  [unitFull : unit.Full]
  [unitFaithful : unit.Faithful]
  unitOver : unit ⋙ projection.functor = 𝟭 projection.Base
  unitAdjunction : projection.functor ⊣ unit
  domainAdjunction : unit ⊣ display ⋙ Arrow.leftFunc

attribute [instance] Comprehension.full Comprehension.faithful
  Comprehension.unitFull Comprehension.unitFaithful

structure Substitution (projection : Fibration.{u,v})
    [fibres : HasFibers.{h,f} projection.functor] where
  reindex : {source target : projection.Base} → (source ⟶ target) →
    Fib projection.functor target ⥤ Fib projection.functor source
  lift : ∀ {source target : projection.Base} (route : source ⟶ target),
    reindex route ⋙ HasFibers.ι source ⟶ HasFibers.ι target
  cartesian : ∀ {source target : projection.Base} (route : source ⟶ target)
      (object : Fib projection.functor target),
    projection.functor.IsStronglyCartesian route ((lift route).app object)

set_option linter.checkUnivs false in
structure Closed (projection : Fibration.{u,v})
    [fibres : HasFibers.{h,f} projection.functor] where
  comprehension : Comprehension projection
  substitution : Substitution projection
  sum : {source target : projection.Base} → (source ⟶ target) →
    Fib projection.functor source ⥤ Fib projection.functor target
  product : {source target : projection.Base} → (source ⟶ target) →
    Fib projection.functor source ⥤ Fib projection.functor target
  sumAdjunction : ∀ {source target : projection.Base} (route : source ⟶ target),
    sum route ⊣ substitution.reindex route
  productAdjunction : ∀ {source target : projection.Base} (route : source ⟶ target),
    substitution.reindex route ⊣ product route
  strongSum : ∀ {source target : projection.Base} (route : source ⟶ target)
      (object : Fib projection.functor source),
    IsIso ((comprehension.display ⋙ Arrow.leftFunc).map
      ((HasFibers.ι source).map ((sumAdjunction route).unit.app object) ≫
        (substitution.lift route).app ((sum route).obj object)))

namespace Closed

variable {projection : Fibration.{u,v}} [HasFibers.{h,f} projection.functor]
  (model : Closed.{u,v,f,h} projection)

def sumArrow {source target : projection.Base} (route : source ⟶ target)
    (object : Fib projection.functor source) :
    (HasFibers.ι source).obj object ⟶
      (HasFibers.ι target).obj ((model.sum route).obj object) :=
  (HasFibers.ι source).map ((model.sumAdjunction route).unit.app object) ≫
    (model.substitution.lift route).app ((model.sum route).obj object)

theorem sumArrow_lifts {source target : projection.Base} (route : source ⟶ target)
    (object : Fib projection.functor source) :
    projection.functor.IsHomLift route (model.sumArrow route object) := by
  let := model.substitution.cartesian route ((model.sum route).obj object)
  simpa only [sumArrow, Functor.id_obj, Category.id_comp] using
    (IsHomLift.comp projection.functor (𝟙 source) route
      ((HasFibers.ι source).map ((model.sumAdjunction route).unit.app object))
      ((model.substitution.lift route).app ((model.sum route).obj object)))

def strongSumComparison {source target : projection.Base} (route : source ⟶ target)
    (object : Fib projection.functor source) :
    (model.comprehension.display.obj ((HasFibers.ι source).obj object)).left ≅
      (model.comprehension.display.obj
        ((HasFibers.ι target).obj ((model.sum route).obj object))).left := by
  letI : IsIso ((model.comprehension.display ⋙ Arrow.leftFunc).map
      (model.sumArrow route object)) := model.strongSum route object
  exact asIso ((model.comprehension.display ⋙ Arrow.leftFunc).map
    (model.sumArrow route object))

theorem strongSumComparison_hom {source target : projection.Base} (route : source ⟶ target)
    (object : Fib projection.functor source) :
    (model.strongSumComparison route object).hom =
      (model.comprehension.display.map (model.sumArrow route object)).left := rfl

/-- The canonical strong comparison commutes with the entire display
square, including its independently retained base map. -/
theorem strongSumComparison_display {source target : projection.Base} (route : source ⟶ target)
    (object : Fib projection.functor source) :
    (model.strongSumComparison route object).hom ≫
        (model.comprehension.display.obj
          ((HasFibers.ι target).obj ((model.sum route).obj object))).hom =
      (model.comprehension.display.obj ((HasFibers.ι source).obj object)).hom ≫
        (model.comprehension.display.map (model.sumArrow route object)).right :=
  Arrow.w (model.comprehension.display.map (model.sumArrow route object))

def abstraction {source target : projection.Base} (route : source ⟶ target)
    {argument : Fib projection.functor target} {result : Fib projection.functor source}
    (body : (model.substitution.reindex route).obj argument ⟶ result) :
    argument ⟶ (model.product route).obj result :=
  (model.productAdjunction route).homEquiv argument result body

def evaluation {source target : projection.Base} (route : source ⟶ target)
    (result : Fib projection.functor source) :
    (model.substitution.reindex route).obj ((model.product route).obj result) ⟶ result :=
  (model.productAdjunction route).counit.app result

theorem beta {source target : projection.Base} (route : source ⟶ target)
    {argument : Fib projection.functor target} {result : Fib projection.functor source}
    (body : (model.substitution.reindex route).obj argument ⟶ result) :
    (model.substitution.reindex route).map (model.abstraction route body) ≫
      model.evaluation route result = body :=
  ((model.productAdjunction route).homEquiv argument result).symm_apply_apply body

theorem eta {source target : projection.Base} (route : source ⟶ target)
    {argument : Fib projection.functor target} {result : Fib projection.functor source}
    (function : argument ⟶ (model.product route).obj result) :
    model.abstraction route
      ((model.substitution.reindex route).map function ≫ model.evaluation route result) = function :=
  ((model.productAdjunction route).homEquiv argument result).apply_symm_apply function

end Closed
end Mettapedia.TypeTheory.FibrationComprehensionProfile
