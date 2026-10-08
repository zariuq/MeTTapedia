import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfCoherence

/-!
# Unit and composition of generated source family comparisons

The same native family comparison used by the actual generated substitution
parser satisfies the source CwF's unit and composition diagrams. Original
base maps are identified by their earned whole-map laws; type-presentation
comparisons remain explicit display maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations

open _root_.CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension

universe u w w'
variable {K : Cwf.{u, u, w, w'}}

noncomputable section

theorem originalMap_identity (context : K.Ctx) :
    originalMap (show (⟨context⟩ : Base K) ⟶ ⟨context⟩ from K.idS context) =
      𝟙 (objectScope (⟨context⟩ : Base K)).1 :=
  RepresentableDeclarations.originalPresheafArrow_identity (⟨context⟩ : Base K)

theorem originalMap_composition {context middle replacement : K.Ctx}
    (later : K.Sub middle context) (earlier : K.Sub replacement middle) :
    originalMap (show (⟨replacement⟩ : Base K) ⟶ ⟨context⟩ from K.compS later earlier) =
      originalMap (show (⟨replacement⟩ : Base K) ⟶ ⟨middle⟩ from earlier) ≫
        originalMap (show (⟨middle⟩ : Base K) ⟶ ⟨context⟩ from later) :=
  RepresentableDeclarations.originalPresheafArrow_composition
    (show (⟨replacement⟩ : Base K) ⟶ ⟨middle⟩ from earlier)
    (show (⟨middle⟩ : Base K) ⟶ ⟨context⟩ from later)

theorem sourceSubstitutionIso_value {context replacement : K.Ctx} (type : K.Ty context)
    (before : K.Sub replacement context) (point : (objectScope (⟨replacement⟩ : Base K)).1.Elements)
    (receipt : (sourceFamily (K.tySub type before)).obj point) :
    ((sourceSubstitutionIso type before).hom.app point receipt).val =
      K.compS (TypeOver.extensionSubstitution before type) receipt.val :=
  CwfYoneda.substitutionFibreEquiv_val K type before
    ((objectName (⟨replacement⟩ : Base K)).mapElements.obj point) receipt

theorem sourceReindex_eqToHom_value {context replacement : K.Ctx} (type : K.Ty context)
    {first second : (objectScope (⟨replacement⟩ : Base K)).1 ⟶
      (objectScope (⟨context⟩ : Base K)).1} (equal : first = second)
    (point : (objectScope (⟨replacement⟩ : Base K)).1.Elements)
    (receipt : (reindexDisplayed first (sourceFamily type)).obj point) :
    ((eqToHom (congrArg (fun map => reindexDisplayed map (sourceFamily type)) equal)).app
      point receipt).val = receipt.val := by
  cases equal
  rfl

theorem sourceSubstitutionIso_identity {context : K.Ctx} (type : K.Ty context) :
    (sourceSubstitutionIso type (K.idS context)).hom ≫
        eqToHom (congrArg (fun map => reindexDisplayed map (sourceFamily type))
          (originalMap_identity context)) =
      sourceFamilyMap (TypeOver.identityObjectIso (⟨type⟩ : TypeOver K context)).hom := by
  ext point receipt
  apply Subtype.ext
  refine (sourceReindex_eqToHom_value type (originalMap_identity context) point _).trans ?_
  refine (sourceSubstitutionIso_value type (K.idS context) point receipt).trans ?_
  change K.compS (TypeOver.extensionSubstitution (K.idS context) type) receipt.val =
    K.compS (TypeOver.identityObjectIso (⟨type⟩ : TypeOver K context)).hom.substitution receipt.val
  rw [TypeOver.identityObjectIso_hom_substitution]

theorem sourceSubstitutionIso_composition {context middle replacement : K.Ctx}
    (type : K.Ty context) (later : K.Sub middle context) (earlier : K.Sub replacement middle) :
    sourceFamilyMap (TypeOver.compositionObjectIso later earlier
        (⟨type⟩ : TypeOver K context)).hom ≫
        (sourceSubstitutionIso (K.tySub type later) earlier).hom ≫
        Functor.whiskerLeft
          (originalMap (show (⟨replacement⟩ : Base K) ⟶ ⟨middle⟩ from earlier)).mapElements
          (sourceSubstitutionIso type later).hom =
      (sourceSubstitutionIso type (K.compS later earlier)).hom ≫
        eqToHom (congrArg (fun map => reindexDisplayed map (sourceFamily type))
          (originalMap_composition later earlier)) := by
  ext point receipt
  apply Subtype.ext
  symm
  refine (sourceReindex_eqToHom_value type (originalMap_composition later earlier) point _).trans ?_
  refine (sourceSubstitutionIso_value type (K.compS later earlier) point receipt).trans ?_
  refine Eq.trans ?_ (sourceSubstitutionIso_value type later
    ((originalMap (show (⟨replacement⟩ : Base K) ⟶ ⟨middle⟩ from earlier)).mapElements.obj point) _).symm
  refine Eq.trans ?_ (congrArg
    (fun value => K.compS (TypeOver.extensionSubstitution later type) value)
    (sourceSubstitutionIso_value (K.tySub type later) earlier point
      ((sourceFamilyMap (TypeOver.compositionObjectIso later earlier
        (⟨type⟩ : TypeOver K context)).hom).app point receipt))).symm
  change K.compS (TypeOver.extensionSubstitution (K.compS later earlier) type) receipt.val =
    K.compS (TypeOver.extensionSubstitution later type)
      (K.compS (TypeOver.extensionSubstitution earlier (K.tySub type later))
        (K.compS (TypeOver.compositionObjectIso later earlier
          (⟨type⟩ : TypeOver K context)).hom.substitution receipt.val))
  rw [← K.comp_assoc, ← K.comp_assoc]
  exact congrArg (fun lift => K.compS lift receipt.val)
    (TypeOver.compositionObjectIso_hom_lift later earlier (⟨type⟩ : TypeOver K context)).symm

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations
