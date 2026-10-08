import Mettapedia.CategoryTheory.FibrationGenericObject
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.Bool.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
# Genericity does not force a unique total classification arrow

The permutation group of two points gives a real non-preordered total
category over a terminal base. Its object is generic, since the base
classifier is unique and a Cartesian arrow exists. Identity and swapping
the points are distinct Cartesian total arrows to that same generic
object, so the stronger total-arrow uniqueness property fails.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.FibrationGenericObject.Controls

open _root_.CategoryTheory _root_.CategoryTheory.Functor
open FibrationTwoCategory

abbrev Total := SingleObj (Equiv.Perm Bool)
abbrev Base := SingleObj PUnit.{1}

instance base_hom_subsingleton (first second : Base) : Subsingleton (first ⟶ second) :=
  inferInstanceAs (Subsingleton PUnit.{1})

def projection : Total ⥤ Base :=
  (1 : Equiv.Perm Bool →* PUnit.{1}).toFunctor

instance projection_fibered : projection.IsFibered :=
  Functor.IsFibered.of_exists_isStronglyCartesian (fun object base route => by
    have sameBase : base = projection.obj object := Subsingleton.elim _ _
    subst base
    have sameRoute : route = projection.map (𝟙 object) := Subsingleton.elim _ _
    refine ⟨object, 𝟙 object, ?_⟩
    rw [sameRoute]
    infer_instance)

def fibration : Fibration.{0,0} where
  projection := ⟨Cat.of Total, Cat.of Base, projection.toCatHom⟩
  fibered := projection_fibered

abbrev point : Total := SingleObj.star (Equiv.Perm Bool)

def generic : Generic fibration where
  object := point
  classifies object := by
    change ∃! route : projection.obj object ⟶ projection.obj point,
      ∃ arrow : object ⟶ point, projection.IsCartesian route arrow
    refine ⟨projection.map (Equiv.refl Bool : object ⟶ point),
      ⟨Equiv.refl Bool, by infer_instance⟩, ?_⟩
    intro other _
    exact Subsingleton.elim _ _

def identityArrow : point ⟶ point := Equiv.refl Bool
def swapArrow : point ⟶ point := Equiv.swap false true

theorem identity_cartesian :
    projection.IsCartesian (projection.map identityArrow) identityArrow := by infer_instance

theorem swap_cartesian :
    projection.IsCartesian (projection.map swapArrow) swapArrow := by infer_instance

theorem the_total_arrows_are_distinct : identityArrow ≠ swapArrow := by
  intro same
  have reading := congrArg (fun permutation : Equiv.Perm Bool => permutation false) same
  simp [identityArrow, swapArrow] at reading

theorem both_total_arrows_have_the_generic_base_classifier :
    projection.map identityArrow = generic.characteristic point ∧
      projection.map swapArrow = generic.characteristic point :=
  ⟨generic.unique point _ identityArrow identity_cartesian,
    generic.unique point _ swapArrow swap_cartesian⟩

theorem total_cartesian_classification_is_not_unique :
    ¬ ∃! arrow : point ⟶ point, projection.IsCartesian (projection.map arrow) arrow := by
  rintro ⟨arrow, _, unique⟩
  exact the_total_arrows_are_distinct
    ((unique identityArrow identity_cartesian).trans (unique swapArrow swap_cartesian).symm)

theorem the_total_fibre_is_not_a_preorder : ¬ Subsingleton (point ⟶ point) :=
  fun erased => the_total_arrows_are_distinct (@Subsingleton.elim _ erased _ _)

end Mettapedia.CategoryTheory.FibrationGenericObject.Controls
