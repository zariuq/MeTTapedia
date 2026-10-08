import Mettapedia.GSLT.Topos.PresheafTheoryAction

/-!
# Reversed theory cells and coherent precomposition

Both the base functor direction and the direction of its natural
transformations are reversed. The comparison isomorphisms are the actual
associator and unitors of precomposition, with their component readouts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.PresheafTheoryAction

open _root_.CategoryTheory _root_.CategoryTheory.Functor
open Mettapedia.GSLT.Core

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {H : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} H]

/-- A source natural transformation acts in the opposite direction on
presheaves. Its components are restriction along the supplied base component. -/
def cell {F G : C ⥤ D} (α : F ⟶ G) : inverseImage G ⟶ inverseImage F :=
  (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).map (NatTrans.op α)

@[simp] theorem cell_app_app {F G : C ⥤ D} (α : F ⟶ G)
    (P : Dᵒᵖ ⥤ Type w) (X : C) :
    (cell α |>.app P).app (Opposite.op X) = P.map (α.app X).op := rfl

theorem cell_naturality {F G : C ⥤ D} (α : F ⟶ G)
    {P Q : Dᵒᵖ ⥤ Type w} (map : P ⟶ Q) :
    (inverseImage G).map map ≫ (cell α).app Q =
      (cell α).app P ≫ (inverseImage F).map map := (cell α).naturality map

@[simp] theorem cell_id (F : C ⥤ D) :
    cell (𝟙 F) = 𝟙 (inverseImage F : (Dᵒᵖ ⥤ Type w) ⥤ _) := by
  simp [cell, inverseImage]

@[simp] theorem cell_comp {F G K : C ⥤ D} (α : F ⟶ G) (β : G ⟶ K) :
    cell (α ≫ β) =
      (cell β ≫ cell α : inverseImage K ⟶ (inverseImage F : (Dᵒᵖ ⥤ Type w) ⥤ _)) := by
  simp [cell, NatTrans.op_comp, inverseImage]

/-- The hom-category action explicitly uses its opposite category. -/
def homAction : (C ⥤ D)ᵒᵖ ⥤ ((Dᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :=
  Functor.opHom C D ⋙ Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)

@[simp] theorem homAction_map {F G : C ⥤ D} (α : F ⟶ G) :
    (homAction : (C ⥤ D)ᵒᵖ ⥤ _).map α.op = (cell α : inverseImage G ⟶ inverseImage F) := rfl

/-- Inverse image along the identity is identified by the actual left unitor. -/
def identityIso (C : Type u₁) [Category.{v₁} C] :
    inverseImage (𝟭 C) ≅ 𝟭 (Cᵒᵖ ⥤ Type w) :=
  NatIso.ofComponents (fun P => Functor.leftUnitor P)
    (by intros; ext; simp [inverseImage])

/-- The composite base map first restricts along the second map and then
along the first map. The comparison retains the presheaf associator. -/
def compositionIso (F : C ⥤ D) (G : D ⥤ E) :
    inverseImage (F ⋙ G) ≅ inverseImage G ⋙ (inverseImage F : (Dᵒᵖ ⥤ Type w) ⥤ _) :=
  NatIso.ofComponents (fun P => Functor.associator F.op G.op P)
    (by intros; ext; simp [inverseImage])

@[simp] theorem identityIso_hom_app_app (P : Cᵒᵖ ⥤ Type w) (X : C) :
    ((identityIso C).hom.app P).app (Opposite.op X) = 𝟙 (P.obj (Opposite.op X)) := rfl

@[simp] theorem compositionIso_hom_app_app (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type w) (X : C) :
    ((compositionIso F G).hom.app P).app (Opposite.op X) =
      𝟙 (P.obj (Opposite.op (G.obj (F.obj X)))) := rfl

theorem composition_cell_naturality {F F' : C ⥤ D} {G G' : D ⥤ E}
    (α : F ⟶ F') (β : G ⟶ G') :
    cell (whiskerRight α G ≫ whiskerLeft F' β) ≫ (compositionIso F G).hom =
      (compositionIso F' G').hom ≫
        whiskerLeft (inverseImage G') (cell α) ≫
        whiskerRight (cell β) (inverseImage F : (Dᵒᵖ ⥤ Type w) ⥤ _) := by
  apply NatTrans.ext
  funext P
  apply NatTrans.ext
  funext X
  change P.map (G.map (α.app X.unop) ≫ β.app (F'.obj X.unop)).op ≫ 𝟙 _ =
    𝟙 _ ≫ P.map (G'.map (α.app X.unop)).op ≫ P.map (β.app (F.obj X.unop)).op
  rw [β.naturality (α.app X.unop)]
  simp

/-- The two three-stage comparisons agree after the actual functor associator. -/
theorem associativity (F : C ⥤ D) (G : D ⥤ E) (K : E ⥤ H) :
    (compositionIso (F ⋙ G) K).hom ≫
        whiskerLeft (inverseImage K) (compositionIso F G).hom ≫
        (Functor.associator (inverseImage K) (inverseImage G)
          (inverseImage F : (Dᵒᵖ ⥤ Type w) ⥤ _)).inv =
      (cell (Functor.associator F G K).inv) ≫
        (compositionIso F (G ⋙ K)).hom ≫
        whiskerRight (compositionIso G K).hom (inverseImage F) := by
  apply NatTrans.ext
  funext P
  apply NatTrans.ext
  funext X
  change (𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ = P.map (𝟙 _).op ≫ 𝟙 _ ≫ 𝟙 _
  simp

end Mettapedia.GSLT.Topos.PresheafTheoryAction
