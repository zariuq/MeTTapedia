import Mettapedia.CategoryTheory.ElementaryToposGlobalImageAction
import Mettapedia.TypeTheory.ElementaryToposHigherOrderDependentSigmaStructure
import Mettapedia.TypeTheory.HigherOrderDependentSigma

/-!
# The higher-order dependent language of an elementary topos

The object is the actual image-comprehension adjunction in fibrations.
It instantiates the general target with both projection-indexed closed
comprehension structures, their actual Cartesian and sum/product mates,
and generic truth over the classifier displayed by a terminal kind.
Monic predicate displays are retained as a property of this instance.

Only objects are raised to the common universe bound. The actual size
equivalence retains the original arrows, displays and transformations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.ElementaryToposHigherOrderDependentSigma

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Bicategory
open Mettapedia.CategoryTheory
open Mettapedia.CategoryTheory.FibrationTwoCategory
open ElementaryToposImageComprehensionAction

universe u v

def profile (topos : ElementaryTopos.{u,v}) :
    HigherOrderDependentSigma.Profile.{max u v,v,max u v,max u v,v}
      (globalAmbientAction.obj topos) :=
  ElementaryToposHigherOrderDependentSigmaStructure.profile topos

def language (topos : ElementaryTopos.{u,v}) :
    HigherOrderDependentSigma.TwoCategory.{max u v,v,max u v,max u v,v} :=
  ⟨globalAmbientAction.obj topos, ⟨profile topos⟩⟩

theorem predicate_display_mono (topos : ElementaryTopos.{u,v})
    (predicate : (globalAmbientAction.obj topos).target.Total) :
    Mono (((profile topos).typeComprehension.display.obj predicate).hom) :=
  ElementaryToposHigherOrderDependentSigmaStructure.type_display_mono topos predicate

theorem predicate_display_cartesian (topos : ElementaryTopos.{u,v})
    {first second : (globalAmbientAction.obj topos).target.Total}
    (arrow : first ⟶ second)
    (cartesian : (globalAmbientAction.obj topos).target.functor.IsCartesian
      ((globalAmbientAction.obj topos).target.functor.map arrow) arrow) :
    IsPullback ((profile topos).typeComprehension.display.map arrow).left
      ((profile topos).typeComprehension.display.obj first).hom
      ((profile topos).typeComprehension.display.obj second).hom
      ((profile topos).typeComprehension.display.map arrow).right :=
  (profile topos).typeDisplay_cartesian arrow cartesian

end Mettapedia.TypeTheory.ElementaryToposHigherOrderDependentSigma
