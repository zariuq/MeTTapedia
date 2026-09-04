import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.Opposites

/-!
# The one-cell opposite of a pseudofunctor

For bicategories `B` and `C`, a pseudofunctor `F : B ⥤ᵖ C` induces a
pseudofunctor `Bᵒᵖ ⥤ᵖ Cᵒᵖ`.  Objects are sent through `F`; a reversed
one-cell is mapped by `F` and reversed again; 2-cells retain their direction.

This construction is useful for indexed semantics.  A covariant semantic
pseudofunctor into `Cat` becomes contravariant after taking one-cell
opposites, and can then be composed with bicategorical Yoneda.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.Pseudofunctor

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory
open _root_.Opposite

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
variable {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- The underlying prelax functor of the one-cell opposite of a
pseudofunctor. -/
def oneCellOppositePrelax (F : B ⥤ᵖ C) : PrelaxFunctor Bᵒᵖ Cᵒᵖ :=
  PrelaxFunctor.mkOfHomFunctors
    (fun object => op (F.obj object.unop))
    (fun source target =>
      Bicategory.Opposite.unopFunctor source target ⋙
        F.mapFunctor target.unop source.unop ⋙
          Bicategory.Opposite.opFunctor
            (F.obj target.unop) (F.obj source.unop))

@[simp] theorem oneCellOppositePrelax_map_unop (F : B ⥤ᵖ C)
    {source target : Bᵒᵖ} (path : source ⟶ target) :
    ((oneCellOppositePrelax F).map path).unop = F.map path.unop :=
  rfl

@[simp] theorem oneCellOppositePrelax_map₂_unop2 (F : B ⥤ᵖ C)
    {source target : Bᵒᵖ} {first second : source ⟶ target}
    (cell : first ⟶ second) :
    ((oneCellOppositePrelax F).map₂ cell).unop2 = F.map₂ cell.unop2 :=
  rfl

/-- A pseudofunctor acts on the one-cell opposites of its source and target
bicategories. -/
def oneCellOpposite (F : B ⥤ᵖ C) : Bᵒᵖ ⥤ᵖ Cᵒᵖ where
  toPrelaxFunctor := oneCellOppositePrelax F
  mapId object := by
    change (F.map (𝟙 object.unop)).op ≅ 𝟙 (op (F.obj object.unop))
    simpa using (F.mapId object.unop).op2
  mapComp first second := by
    change (F.map (second.unop ≫ first.unop)).op ≅
      (F.map first.unop).op ≫ (F.map second.unop).op
    simpa using (F.mapComp second.unop first.unop).op2
  map₂_whisker_left := @fun _ _ _ first _ _ cell => by
    change Bicategory.Opposite.op2
        (F.map₂ (cell.unop2 ▷ first.unop)) = _
    rw [F.map₂_whisker_right]
    rfl
  map₂_whisker_right := @fun _ _ _ _ _ cell last => by
    change Bicategory.Opposite.op2
        (F.map₂ (last.unop ◁ cell.unop2)) = _
    rw [F.map₂_whisker_left]
    rfl
  map₂_associator := @fun _ _ _ _ first middle last => by
    change Bicategory.Opposite.op2
      (F.map₂ (α_ last.unop middle.unop first.unop).inv) = _
    congr 1
    simp
    change F.map₂ (α_ last.unop middle.unop first.unop).inv =
      (F.mapComp last.unop (middle.unop ≫ first.unop)).hom ≫
        F.map last.unop ◁ (F.mapComp middle.unop first.unop).hom ≫
          (α_ (F.map last.unop) (F.map middle.unop)
            (F.map first.unop)).inv ≫
            (F.mapComp last.unop middle.unop).inv ▷ F.map first.unop ≫
              (F.mapComp (last.unop ≫ middle.unop) first.unop).inv
    rw [show (α_ last.unop middle.unop first.unop).inv =
        inv (α_ last.unop middle.unop first.unop).hom by
      symm
      apply IsIso.inv_eq_of_hom_inv_id
      simp]
    rw [F.map₂_inv]
    apply IsIso.inv_eq_of_hom_inv_id
    rw [F.map₂_associator]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc]
    rw [whiskerLeft_inv_hom_assoc]
    rw [Iso.hom_inv_id_assoc]
    rw [hom_inv_whiskerRight_assoc]
    exact Iso.hom_inv_id _
  map₂_left_unitor := @fun _ _ path => by
    change Bicategory.Opposite.op2
      (F.map₂ (ρ_ path.unop).hom) = _
    congr 1
    change F.map₂ (ρ_ path.unop).hom =
      (F.mapComp path.unop (𝟙 _)).hom ≫
        F.map path.unop ◁ (F.mapId _).hom ≫
          (ρ_ (F.map path.unop)).hom
    exact F.map₂_right_unitor path.unop
  map₂_right_unitor := @fun _ _ path => by
    change Bicategory.Opposite.op2
      (F.map₂ (λ_ path.unop).hom) = _
    congr 1
    change F.map₂ (λ_ path.unop).hom =
      (F.mapComp (𝟙 _) path.unop).hom ≫
        (F.mapId _).hom ▷ F.map path.unop ≫
          (λ_ (F.map path.unop)).hom
    exact F.map₂_left_unitor path.unop

@[simp] theorem oneCellOpposite_obj_unop (F : B ⥤ᵖ C) (object : Bᵒᵖ) :
    ((oneCellOpposite F).obj object).unop = F.obj object.unop :=
  rfl

@[simp] theorem oneCellOpposite_map_unop (F : B ⥤ᵖ C)
    {source target : Bᵒᵖ} (path : source ⟶ target) :
    ((oneCellOpposite F).map path).unop = F.map path.unop :=
  rfl

@[simp] theorem oneCellOpposite_map₂_unop2 (F : B ⥤ᵖ C)
    {source target : Bᵒᵖ} {first second : source ⟶ target}
    (cell : first ⟶ second) :
    ((oneCellOpposite F).map₂ cell).unop2 = F.map₂ cell.unop2 :=
  rfl

/-! ## Axiom audit -/

#print axioms oneCellOpposite

end Mettapedia.CategoryTheory.Pseudofunctor
