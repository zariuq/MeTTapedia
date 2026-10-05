import Mettapedia.TypeTheory.HostChoiceContextualPresheafProfile

/-!
# Monomorphism smallness in the optional successor ambient model

Every injective contextual map has subsingleton fibres. A nonempty fibre
is enumerated by a proposition-sized receipt type, and external host choice
reads its unique element. Empty fibres have no receipt. This proves the
additional monomorphism-smallness condition for every monic in the fixed
successor ambient category, rather than inferring it from diagonal smallness.

The chosen host receipt is explicit. This result strengthens the optional
profile and does not assert an internal witness-selection principle. A
two-valued projection is small but is not monic.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HostChoiceContextualSmallMapMonics

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open HostChoiceContextualSmallMapModel

universe u v w
variable {D : Type u} [Category.{u} D] {A : D ⥤ Type v} {B : D ⥤ Type w}

noncomputable def monicEnumeration (operation : NaturalHom A B)
    (injective : ∀ point, Function.Injective (operation.app point)) (point : D) (value : B.obj point) :
    Enumeration.{u, v} (Fibre operation point value) where
  Carrier := {_receipt : PUnit.{u+1} // Nonempty (Fibre operation point value)}
  value receipt := Classical.choice receipt.property
  covered receipt := by
    refine ⟨⟨PUnit.unit, ⟨receipt⟩⟩, ?_⟩
    apply Subtype.ext
    exact injective point ((Classical.choice (show Nonempty (Fibre operation point value) from
      ⟨receipt⟩)).property.trans receipt.property.symm)

theorem small_of_injective (operation : NaturalHom A B)
    (injective : ∀ point, Function.Injective (operation.app point)) : SmallFibres operation :=
  fun point value => ⟨monicEnumeration operation injective point value⟩

theorem ordinary_monic_small {A B : D ⥤ Type (u+1)} (operation : A ⟶ B) [Mono operation] :
    HostChoiceContextualPresheafAmbient.smallMaps (D := D) operation := by
  have same : (NaturalHom.ofNatTrans operation).toNatTrans = operation := by
    apply NatTrans.ext
    funext point
    apply ConcreteCategory.hom_ext
    intro value
    rfl
  have monic : @Mono (D ⥤ Type (u+1)) _ A B (NaturalHom.ofNatTrans operation).toNatTrans := by
    rw [same]
    infer_instance
  exact small_of_injective (NaturalHom.ofNatTrans operation)
    ((HostChoiceContextualPresheafAmbient.natTrans_mono_iff_injective
      (NaturalHom.ofNatTrans operation)).mp monic)

theorem ambient_monic_small {A B : Ambient D} (operation : A ⟶ B) [Mono operation] :
    SmallFibres operation :=
  small_of_injective operation
    ((HostChoiceContextualPresheafAmbient.ambient_mono_iff_injective operation).mp (by infer_instance))

theorem profile_with_monomorphism_smallness :
    HostChoiceContextualPresheafProfile.VerifiedProfile D ∧
      ∀ (A B : D ⥤ Type (u+1)) (operation : A ⟶ B), Mono operation →
        HostChoiceContextualPresheafAmbient.smallMaps (D := D) operation := by
  refine ⟨HostChoiceContextualPresheafProfile.verifiedProfile D, ?_⟩
  intro A B operation monic
  exact @ordinary_monic_small D _ A B operation monic

def duplicateFamily : D ⥤ Type (u+1) where
  obj _ := ULift.{u+1} Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def duplicateProjection : NaturalHom (duplicateFamily (D := D))
    (HostChoiceContextualSmallMapModel.terminal (D := D)) where
  app _ _ := PUnit.unit
  naturality _ _ := rfl

def duplicateFibreEnumeration (point : D)
    (value : (HostChoiceContextualSmallMapModel.terminal (D := D)).obj point) :
    Enumeration.{u, u+1} (Fibre duplicateProjection point value) where
  Carrier := ULift.{u} Bool
  value receipt := ⟨ULift.up receipt.down, by cases value; rfl⟩
  covered receipt := ⟨ULift.up receipt.val.down, Subtype.ext rfl⟩

theorem duplicateProjection_small : SmallFibres (duplicateProjection (D := D)) :=
  fun point value => ⟨duplicateFibreEnumeration point value⟩

theorem duplicateProjection_not_injective (point : D) :
    ¬ Function.Injective ((duplicateProjection (D := D)).app point) := by
  intro injective
  have same := injective (show duplicateProjection.app point (ULift.up false) =
    duplicateProjection.app point (ULift.up true) from rfl)
  exact Bool.false_ne_true (congrArg ULift.down same)

theorem duplicateProjection_not_monic (point : D) :
    ¬ @Mono (D ⥤ Type (u+1)) _ duplicateFamily
      HostChoiceContextualSmallMapModel.terminal duplicateProjection.toNatTrans :=
  fun monic => duplicateProjection_not_injective point
    ((HostChoiceContextualPresheafAmbient.natTrans_mono_iff_injective duplicateProjection).mp monic point)

end Mettapedia.TypeTheory.HostChoiceContextualSmallMapMonics
