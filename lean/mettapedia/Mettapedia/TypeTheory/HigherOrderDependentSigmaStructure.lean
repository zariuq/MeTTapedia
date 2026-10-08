import Mettapedia.CategoryTheory.FibrationAdjunctionTwoCategory
import Mettapedia.CategoryTheory.FibrationGenericObject
import Mettapedia.TypeTheory.ProjectionIndexedComprehension

/-!
# General higher-order dependent structures with strong sums

Kinds have full closed comprehension. The fibred reflection sends kinds
to types, and its fully faithful right adjoint includes types into kinds.
The resulting type comprehension is also closed, with operations along its
actual display projections and their Beck--Chevalley comparisons. A kind
over a terminal base displays the base of an actual generic type object.

Genericity requires a unique base classifier and an existing Cartesian
total arrow. Neither the types nor the kinds must be preorders, and no
monicity or predicate-doctrine presentation is imposed on general models.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.HigherOrderDependentSigmaStructure

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory Mettapedia.CategoryTheory.FibrationTwoCategory

universe u v p f h

set_option linter.checkUnivs false in
structure Profile (object : FibrationAdjunctionTwoCategory.{u,v}) where
  sameBase : object.target.Base = object.source.Base
  leftBase : object.left.square.right = eqToHom sameBase.symm
  rightBase : object.right.square.right = eqToHom sameBase
  unitBase : HEq object.adjunction.unit.hom.right (𝟙 (𝟙 object.source.Base))
  counitBase : HEq object.adjunction.counit.hom.right (𝟙 (𝟙 object.target.Base))
  rightFull : object.right.square.left.toFunctor.Full
  rightFaithful : object.right.square.left.toFunctor.Faithful
  kindFibres : HasFibers.{h,f} object.source.functor
  kinds : @ProjectionIndexedComprehension.Closed.{u,v,f,h} object.source kindFibres
  typeFibres : HasFibers.{h,p} object.target.functor
  types : @ProjectionIndexedComprehension.Closed.{u,v,p,h} object.target typeFibres
  typeDisplay : types.comprehension.display =
    object.right.square.left.toFunctor ⋙ kinds.comprehension.display ⋙
      object.left.square.right.toFunctor.mapArrow
  kind : object.source.Total
  kindTerminal : IsTerminal (object.source.functor.obj kind)
  generic : FibrationGenericObject.Generic object.target
  genericBase :
    object.left.square.right.toFunctor.obj (kinds.comprehension.display.obj kind).left ≅
      object.target.functor.obj generic.object

namespace Profile

variable {object : FibrationAdjunctionTwoCategory.{u,v}}
  (profile : Profile.{u,v,p,f,h} object)

def kindComprehension : FibrationComprehensionProfile.Comprehension object.source :=
  @ProjectionIndexedComprehension.Data.comprehension _ profile.kindFibres
    (@ProjectionIndexedComprehension.Closed.toData _ profile.kindFibres profile.kinds)

def typeComprehension : FibrationComprehensionProfile.Comprehension object.target :=
  @ProjectionIndexedComprehension.Data.comprehension _ profile.typeFibres
    (@ProjectionIndexedComprehension.Closed.toData _ profile.typeFibres profile.types)

theorem typeDisplay_cartesian {source target : object.target.Total}
    (arrow : source ⟶ target)
    (cartesian : object.target.functor.IsCartesian
      (object.target.functor.map arrow) arrow) :
    IsPullback (profile.typeComprehension.display.map arrow).left
      (profile.typeComprehension.display.obj source).hom
      (profile.typeComprehension.display.obj target).hom
      (profile.typeComprehension.display.map arrow).right :=
  profile.typeComprehension.cartesian arrow cartesian

theorem generic_base_substitution {source target : object.target.Total}
    (arrow : source ⟶ target)
    (cartesian : object.target.functor.IsCartesian
      (object.target.functor.map arrow) arrow) :
    profile.generic.characteristic source =
      object.target.functor.map arrow ≫ profile.generic.characteristic target :=
  profile.generic.characteristic_substitution arrow cartesian

end Profile

end Mettapedia.TypeTheory.HigherOrderDependentSigmaStructure
