import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSiteLiftMaterial

/-!
# Constructed discrete material identity across successor sites

The upper identity graph is formed independently by equality separation of
the singleton empty set. Its actual occurrence-class witnesses explicitly
decode and encode the raised endpoint equality. This preserves the material
carrier, decoded equality, reflexivity and contextual restriction.

Subsingleton witness comparisons here belong to this discrete model only.
They do not impose UIP or equality reflection on a native identity calculus.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualIdentitySiteLift

open CategoryTheory
open Mettapedia.TypeTheory
open ContextualGeneratedUniverse

universe u
variable {C : Type u} [Category.{u} C] {original : LabelledContext C}
variable (domain : MaterialFamily original) (left right : domain.family.sections)

def formed : MaterialFamily (ContextualSiteLiftMaterial.context original) :=
  (ContextualSiteLiftMaterial.family domain).identity
    (PresheafSiteLift.raiseTerm original.base domain.family left)
    (PresheafSiteLift.raiseTerm original.base domain.family right)

def lowerWitness (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (witness : (formed domain left right).family.obj point) :
    (domain.identity left right).family.obj ((PresheafSiteLift.elementsDown original.base).obj point) :=
  PresheafIdentityWitness.encode (congrArg ULift.down (PresheafIdentityWitness.decode witness))

def raiseWitness (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (witness : (domain.identity left right).family.obj ((PresheafSiteLift.elementsDown original.base).obj point)) :
    (formed domain left right).family.obj point :=
  PresheafIdentityWitness.encode (congrArg ULift.up (PresheafIdentityWitness.decode witness))

private abbrev upperDiscrete (point : (ContextualSiteLiftMaterial.context original).base.Elements) :
    Subsingleton ((formed domain left right).family.obj point) := by
  change Subsingleton (PresheafIdentityWitness.Witness _ _)
  infer_instance

private abbrev lowerDiscrete (point : original.base.Elements) :
    Subsingleton ((domain.identity left right).family.obj point) := by
  change Subsingleton (PresheafIdentityWitness.Witness _ _)
  infer_instance

def semanticEquiv (point : (ContextualSiteLiftMaterial.context original).base.Elements) :
    (formed domain left right).family.obj point ≃
      (domain.identity left right).family.obj ((PresheafSiteLift.elementsDown original.base).obj point) where
  toFun := lowerWitness domain left right point
  invFun := raiseWitness domain left right point
  left_inv _ := @Subsingleton.elim _ (upperDiscrete domain left right point) _ _
  right_inv _ := @Subsingleton.elim _ (lowerDiscrete domain left right _) _ _

theorem decoded_endpoint_equality (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (witness : (formed domain left right).family.obj point) :
    PresheafIdentityWitness.decode (lowerWitness domain left right point witness) =
      congrArg ULift.down (PresheafIdentityWitness.decode witness) := rfl

theorem formed_value (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (witness : (formed domain left right).family.obj point) :
    ((formed domain left right).model point).value witness =
      HSet.lift (((domain.identity left right).model ((PresheafSiteLift.elementsDown original.base).obj point)).value
        (semanticEquiv domain left right point witness)) := by
  have upper : ((formed domain left right).model point).value witness = ∅ :=
    (PowerClassContextualMaterialization.powerClassModel_value _ witness).trans
      (PresheafIdentityWitness.member_condition witness).1
  have lower : ((domain.identity left right).model ((PresheafSiteLift.elementsDown original.base).obj point)).value
      (semanticEquiv domain left right point witness) = ∅ :=
    (PowerClassContextualMaterialization.powerClassModel_value _ _).trans
      (PresheafIdentityWitness.member_condition (semanticEquiv domain left right point witness)).1
  exact upper.trans (HSet.lift_empty.symm.trans (congrArg HSet.lift lower).symm)

theorem formed_carrier (point : (ContextualSiteLiftMaterial.context original).base.Elements) :
    ((formed domain left right).model point).carrier =
      HSet.lift (((domain.identity left right).model ((PresheafSiteLift.elementsDown original.base).obj point)).carrier) :=
  PresentedTypeCumulativity.carrier_eq_lift_of_values _ _ (semanticEquiv domain left right point)
    (formed_value domain left right point)

def memberEquiv (point : (ContextualSiteLiftMaterial.context original).base.Elements) :
    {value : HSet.{u + 1} // value ∈ ((formed domain left right).model point).carrier} ≃
      {value : HSet.{u} // value ∈ ((domain.identity left right).model ((PresheafSiteLift.elementsDown original.base).obj point)).carrier} :=
  PresentedTypeCumulativity.memberEquiv _ _ (semanticEquiv domain left right point)

theorem decoder (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (member : {value : HSet.{u + 1} // value ∈ ((formed domain left right).model point).carrier}) :
    ((domain.identity left right).model ((PresheafSiteLift.elementsDown original.base).obj point)).decode
      (memberEquiv domain left right point member) =
      semanticEquiv domain left right point (((formed domain left right).model point).decode member) :=
  PresentedTypeCumulativity.decode_memberEquiv _ _ _ member

theorem reflexivity (point : (ContextualSiteLiftMaterial.context original).base.Elements) :
    semanticEquiv domain left left point (PresheafIdentityWitness.encode rfl) = PresheafIdentityWitness.encode rfl :=
  @Subsingleton.elim _ (lowerDiscrete domain left left _) _ _

theorem semantic_restriction {first second : (ContextualSiteLiftMaterial.context original).base.Elements}
    (arrow : first ⟶ second) (witness : (formed domain left right).family.obj first) :
    semanticEquiv domain left right second ((formed domain left right).family.map arrow witness) =
      (domain.identity left right).family.map ((PresheafSiteLift.elementsDown original.base).map arrow)
        (semanticEquiv domain left right first witness) :=
  @Subsingleton.elim _ (lowerDiscrete domain left right _) _ _

def comparison : NatTrans (formed domain left right).family
    (PresheafSiteLift.family original.base (domain.identity left right).family) where
  app point := TypeCat.ofHom fun witness => ULift.up (lowerWitness domain left right point witness)
  naturality {first second} arrow := by
    apply ConcreteCategory.hom_ext
    intro witness
    exact congrArg ULift.up (semantic_restriction domain left right arrow witness)

def inverse : NatTrans (PresheafSiteLift.family original.base (domain.identity left right).family)
    (formed domain left right).family where
  app point := TypeCat.ofHom fun witness => raiseWitness domain left right point witness.down
  naturality {first second} _arrow := by
    apply ConcreteCategory.hom_ext
    intro _witness
    exact @Subsingleton.elim _ (upperDiscrete domain left right second) _ _

theorem comparison_left : Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
    (comparison domain left right) (inverse domain left right) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity _ := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro _witness
  exact @Subsingleton.elim _ (upperDiscrete domain left right point) _ _

theorem comparison_right : Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
    (inverse domain left right) (comparison domain left right) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity _ := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro _witness
  exact congrArg ULift.up (@Subsingleton.elim _ (lowerDiscrete domain left right _) _ _)

set_option backward.isDefEq.respectTransparency false in
theorem member_restriction {first second : (ContextualSiteLiftMaterial.context original).base.Elements}
    (arrow : first ⟶ second)
    (member : {value : HSet.{u + 1} // value ∈ ((formed domain left right).model first).carrier}) :
    memberEquiv domain left right second ((formed domain left right).memberRestriction arrow member) =
      (domain.identity left right).memberRestriction ((PresheafSiteLift.elementsDown original.base).map arrow)
        (memberEquiv domain left right first member) := by
  apply ((domain.identity left right).model ((PresheafSiteLift.elementsDown original.base).obj second)).decode.injective
  rw [decoder, MaterialFamily.memberRestriction_decode, MaterialFamily.memberRestriction_decode, decoder]
  exact semantic_restriction domain left right arrow (((formed domain left right).model first).decode member)

namespace Growing

abbrev input := ContextualGeneratedUniverse.Growing.input
abbrev emptyTerm := ContextualGeneratedUniverse.Growing.emptySection
abbrev positiveTerm := ContextualGeneratedUniverse.Growing.positiveSection
abbrev upperPoint (point : ContextualGeneratedUniverse.Growing.context.base.Elements) :=
  (PresheafSiteLift.elementsUp ContextualGeneratedUniverse.Growing.context.base).obj point

theorem old_identity :
    ((formed input emptyTerm positiveTerm).model (upperPoint ContextualGeneratedUniverse.Growing.old)).carrier = {∅} := by
  exact (formed_carrier input emptyTerm positiveTerm _).trans
    ((congrArg HSet.lift ContextualGeneratedUniverse.Growing.identity_old_carrier).trans
      ((HSet.lift_singleton _).trans (congrArg (fun value : HSet.{1} => ({value} : HSet.{1})) HSet.lift_empty)))

theorem new_identity :
    ((formed input emptyTerm positiveTerm).model (upperPoint ContextualGeneratedUniverse.Growing.newPoint)).carrier = ∅ := by
  exact (formed_carrier input emptyTerm positiveTerm _).trans
    ((congrArg HSet.lift ContextualGeneratedUniverse.Growing.identity_new_carrier).trans HSet.lift_empty)

end Growing

end Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualIdentitySiteLift
