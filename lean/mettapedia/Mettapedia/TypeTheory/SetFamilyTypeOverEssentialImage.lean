import Mathlib.CategoryTheory.EssentialImage
import Mettapedia.TypeTheory.ResponseIndexedResultFamily

/-!
# Essential images of constant families

The image of a contextual embedding must be closed under isomorphism.  For
the set-families CwF, an isomorphism of displayed types induces an equivalence
of every fibre.  This upgrades literal object-image comparisons to the
categorical essential image.

The response-indexed protocol result family is outside the essential image of
constant-family inclusion: its unit-result and Boolean-result fibres cannot
both be equivalent to one simple type.  The conclusion is invariant under
changing the displayed-family representation by isomorphism.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.SetFamilyTypeOverEssentialImage

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol.VaryingCanary
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.ResponseIndexedResultFamily
open Mettapedia.TypeTheory.SetFamilyComprehensionMap

universe u

variable {Context : Type u}
variable {sourceFamily targetFamily : Context → Type u}

/-! ## Fibre equivalence induced by a displayed-type isomorphism -/

/-- The map in one fibre selected by a display map over the unchanged base. -/
def fibreMapOfDisplayHom
    (morphism :
      (⟨sourceFamily⟩ : TypeOver (familiesCwf.{u}) Context) ⟶
        (⟨targetFamily⟩ : TypeOver (familiesCwf.{u}) Context))
    (context : Context) : sourceFamily context → targetFamily context :=
  fun value =>
    let output := morphism.substitution ⟨context, value⟩
    let baseEquality : output.1 = context :=
      congrFun morphism.over ⟨context, value⟩
    cast (congrArg targetFamily baseEquality) output.2

/-- The underlying substitution of a display map is exactly the total map of
its selected fibre maps. -/
theorem displayHom_substitution_eq_totalMap
    (morphism :
      (⟨sourceFamily⟩ : TypeOver (familiesCwf.{u}) Context) ⟶
        (⟨targetFamily⟩ : TypeOver (familiesCwf.{u}) Context)) :
    morphism.substitution = totalMap (fibreMapOfDisplayHom morphism) := by
  funext point
  apply Sigma.ext
  · change (morphism.substitution point).1 = point.1
    have overAtPoint := congrFun morphism.over point
    change (morphism.substitution point).1 = point.1 at overAtPoint
    exact overAtPoint
  · exact (cast_heq _ _).symm

/-- An isomorphism of displayed types gives an equivalence of their total
comprehension spaces. -/
def totalEquivOfTypeOverIso
    (isomorphism :
      (⟨sourceFamily⟩ : TypeOver (familiesCwf.{u}) Context) ≅
        (⟨targetFamily⟩ : TypeOver (familiesCwf.{u}) Context)) :
    Sigma sourceFamily ≃ Sigma targetFamily where
  toFun := isomorphism.hom.substitution
  invFun := isomorphism.inv.substitution
  left_inv point := by
    have substitutionEquality :=
      congrArg TypeOver.Hom.substitution isomorphism.hom_inv_id
    exact congrFun substitutionEquality point
  right_inv point := by
    have substitutionEquality :=
      congrArg TypeOver.Hom.substitution isomorphism.inv_hom_id
    exact congrFun substitutionEquality point

/-- A displayed-type isomorphism induces an equivalence in every fibre. -/
noncomputable def fibreEquivOfTypeOverIso
    (isomorphism :
      (⟨sourceFamily⟩ : TypeOver (familiesCwf.{u}) Context) ≅
        (⟨targetFamily⟩ : TypeOver (familiesCwf.{u}) Context))
    (context : Context) :
    sourceFamily context ≃ targetFamily context := by
  let fibreMap := fibreMapOfDisplayHom isomorphism.hom
  have totalBijective : Function.Bijective (totalMap fibreMap) := by
    rw [← displayHom_substitution_eq_totalMap isomorphism.hom]
    exact (totalEquivOfTypeOverIso isomorphism).bijective
  exact Equiv.ofBijective (fibreMap context)
    ((totalMap_bijective_iff fibreMap).1 totalBijective context)

/-! ## Essential properness of the response-indexed family -/

/-- The response-indexed result family is not merely absent from the literal
object image; it is outside the categorical essential image of the
constant-family functor. -/
theorem resultDisplay_not_in_simple_essentialImage :
    ¬ (simpleToDependentTypeFunctor Phase).essImage resultDisplay := by
  rintro ⟨simpleType, ⟨isomorphism⟩⟩
  have atUnit : simpleType.val ≃ Result Phase.unitDone := by
    simpa [simpleToDependentTypeFunctor, simpleToDependentObject,
      resultDisplay, constantFamily] using
      (fibreEquivOfTypeOverIso isomorphism Phase.unitDone)
  have atBool : simpleType.val ≃ Result Phase.boolDone := by
    simpa [simpleToDependentTypeFunctor, simpleToDependentObject,
      resultDisplay, constantFamily] using
      (fibreEquivOfTypeOverIso isomorphism Phase.boolDone)
  have unitBool : PUnit ≃ Bool := by
    change Result Phase.unitDone ≃ Result Phase.boolDone
    exact atUnit.symm.trans atBool
  exact Canary.unit_not_equiv_bool ⟨unitBool⟩

/-- Positive control: every constant family belongs to the essential image. -/
theorem constant_family_mem_simple_essentialImage
    (simpleType : TypeOver (SimpleFamiliesCwf.{u}) Context) :
    (simpleToDependentTypeFunctor Context).essImage
      ((simpleToDependentTypeFunctor Context).obj simpleType) :=
  (simpleToDependentTypeFunctor Context).obj_mem_essImage simpleType

/-- Paired invariant boundary for the constant-family embedding. -/
theorem constant_fragment_essentialImage_boundary
    (simpleType : TypeOver (SimpleFamiliesCwf.{0}) Phase) :
    (simpleToDependentTypeFunctor Phase).essImage
        ((simpleToDependentTypeFunctor Phase).obj simpleType) /\
      ¬ (simpleToDependentTypeFunctor Phase).essImage resultDisplay :=
  ⟨constant_family_mem_simple_essentialImage simpleType,
    resultDisplay_not_in_simple_essentialImage⟩

#print axioms displayHom_substitution_eq_totalMap
#print axioms totalEquivOfTypeOverIso
#print axioms fibreEquivOfTypeOverIso
#print axioms resultDisplay_not_in_simple_essentialImage
#print axioms constant_fragment_essentialImage_boundary

end Mettapedia.TypeTheory.SetFamilyTypeOverEssentialImage
