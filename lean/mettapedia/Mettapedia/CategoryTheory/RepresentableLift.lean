import Mathlib.CategoryTheory.Yoneda

/-!
# Lifting a pointwise representable functor through the Yoneda embedding

A functor into presheaves whose values are each represented by a chosen
object factors through the Yoneda embedding, up to the chosen
representations: arrows act on the representing objects exactly as the
functor acts on generalized elements.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.RepresentableLift

open _root_.CategoryTheory Opposite

universe v₁ v u₁ u

variable {C : Type u₁} [Category.{v₁} C] {D : Type u} [Category.{v} D]
variable (G : C ⥤ Dᵒᵖ ⥤ Type v) (obj : C → D)
variable (represented : ∀ a, (G.obj a).RepresentableBy (obj a))

/-- The functor on the representing objects. -/
def lift : C ⥤ D where
  obj := obj
  map {a b} arrow := Yoneda.fullyFaithful.preimage
    ((represented a).toIso.hom ≫ G.map arrow ≫ (represented b).toIso.inv)
  map_id a := by
    rw [G.map_id, Category.id_comp, Iso.hom_inv_id]
    exact Yoneda.fullyFaithful.preimage_id
  map_comp {a b c} first second := by
    rw [← Yoneda.fullyFaithful.preimage_comp, G.map_comp]
    congr 1
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The lift followed by the Yoneda embedding is the original functor. -/
def liftIso : lift G obj represented ⋙ yoneda ≅ G :=
  NatIso.ofComponents (fun a => (represented a).toIso) (fun {a b} arrow => by
    change yoneda.map (Yoneda.fullyFaithful.preimage
        ((represented a).toIso.hom ≫ G.map arrow ≫ (represented b).toIso.inv)) ≫
      (represented b).toIso.hom = (represented a).toIso.hom ≫ G.map arrow
    erw [Yoneda.fullyFaithful.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- Arrows act on generalized elements of the representing objects as the
functor acts on the represented presheaves. -/
theorem homEquiv_map {a b : C} (arrow : a ⟶ b) {Z : D} (point : Z ⟶ obj a) :
    (represented b).homEquiv (point ≫ (lift G obj represented).map arrow) =
      (G.map arrow).app (op Z) ((represented a).homEquiv point) := by
  have natural := congrArg (fun φ => φ.app (op Z) point)
    ((liftIso G obj represented).hom.naturality arrow)
  exact natural

section Maps

variable {G G' G'' : C ⥤ Dᵒᵖ ⥤ Type v} {obj obj' obj'' : C → D}
variable {represented : ∀ a, (G.obj a).RepresentableBy (obj a)}
variable {represented' : ∀ a, (G'.obj a).RepresentableBy (obj' a)}
variable {represented'' : ∀ a, (G''.obj a).RepresentableBy (obj'' a)}

/-- A natural transformation of pointwise represented functors lifts to the
representing objects. -/
def liftMap (τ : G ⟶ G') : lift G obj represented ⟶ lift G' obj' represented' :=
  (Yoneda.fullyFaithful.whiskeringRight C).preimage
    ((liftIso G obj represented).hom ≫ τ ≫ (liftIso G' obj' represented').inv)

theorem liftMap_id : liftMap (𝟙 G) = 𝟙 (lift G obj represented) := by
  apply (Yoneda.fullyFaithful.whiskeringRight C).map_injective
  unfold liftMap
  rw [Functor.FullyFaithful.map_preimage, Category.id_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id]

theorem liftMap_comp (τ : G ⟶ G') (υ : G' ⟶ G'') :
    liftMap (represented := represented) (represented' := represented'') (τ ≫ υ) =
      liftMap (represented' := represented') τ ≫ liftMap υ := by
  apply (Yoneda.fullyFaithful.whiskeringRight C).map_injective
  rw [CategoryTheory.Functor.map_comp, liftMap, liftMap, liftMap,
    Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage,
    Functor.FullyFaithful.map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The lifted transformation acts on generalized elements as the original
transformation acts on the represented presheaves. -/
theorem homEquiv_liftMap (τ : G ⟶ G') (a : C) {Z : D} (point : Z ⟶ obj a) :
    (represented' a).homEquiv (point ≫ (liftMap (represented := represented)
      (represented' := represented') τ).app a) =
      (τ.app a).app (op Z) ((represented a).homEquiv point) := by
  have lifted := congrArg (fun φ : lift G obj represented ⋙ yoneda ⟶ lift G' obj' represented' ⋙ yoneda =>
      (φ.app a).app (op Z) point)
    ((Yoneda.fullyFaithful.whiskeringRight C).map_preimage
      ((liftIso G obj represented).hom ≫ τ ≫ (liftIso G' obj' represented').inv))
  refine (congrArg (represented' a).homEquiv lifted).trans ?_
  exact (represented' a).homEquiv.apply_symm_apply _

end Maps

section Iso

/-- A functor whose values represent the given presheaves, compatibly with
arrows, followed by the Yoneda embedding. -/
def representedIso (H : C ⥤ D) (representedH : ∀ a, (G.obj a).RepresentableBy (H.obj a))
    (natural : ∀ {a b : C} (arrow : a ⟶ b) {Z : D} (point : Z ⟶ H.obj a),
      (representedH b).homEquiv (point ≫ H.map arrow) =
        (G.map arrow).app (op Z) ((representedH a).homEquiv point)) :
    H ⋙ yoneda ≅ G :=
  NatIso.ofComponents (fun a => (representedH a).toIso) (fun {a b} arrow => by
    apply NatTrans.ext
    funext Z
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext point
    exact natural arrow point)

/-- **A functor whose values represent the given presheaves, compatibly with
arrows, is the lift.** -/
def isoLift (H : C ⥤ D) (representedH : ∀ a, (G.obj a).RepresentableBy (H.obj a))
    (natural : ∀ {a b : C} (arrow : a ⟶ b) {Z : D} (point : Z ⟶ H.obj a),
      (representedH b).homEquiv (point ≫ H.map arrow) =
        (G.map arrow).app (op Z) ((representedH a).homEquiv point)) :
    H ≅ lift G obj represented :=
  (Yoneda.fullyFaithful.whiskeringRight C).preimageIso
    (representedIso G H representedH natural ≪≫ (liftIso G obj represented).symm)

/-- The comparison with the lift keeps the represented elements. -/
theorem homEquiv_isoLift (H : C ⥤ D) (representedH : ∀ a, (G.obj a).RepresentableBy (H.obj a))
    (natural : ∀ {a b : C} (arrow : a ⟶ b) {Z : D} (point : Z ⟶ H.obj a),
      (representedH b).homEquiv (point ≫ H.map arrow) =
        (G.map arrow).app (op Z) ((representedH a).homEquiv point))
    (a : C) {Z : D} (point : Z ⟶ H.obj a) :
    (represented a).homEquiv (point ≫ (isoLift G obj represented H representedH
      natural).hom.app a) = (representedH a).homEquiv point := by
  have lifted := congrArg (fun φ : H ⋙ yoneda ⟶ lift G obj represented ⋙ yoneda =>
      (φ.app a).app (op Z) point)
    ((Yoneda.fullyFaithful.whiskeringRight C).map_preimage
      (representedIso G H representedH natural ≪≫ (liftIso G obj represented).symm).hom)
  refine (congrArg (represented a).homEquiv lifted).trans ?_
  exact (represented a).homEquiv.apply_symm_apply _

end Iso

/-- **The comparison of two objects representing the same presheaf.** -/
def comparisonIso {F : Dᵒᵖ ⥤ Type v} {Y Y' : D} (e : F.RepresentableBy Y)
    (e' : F.RepresentableBy Y') : Y ≅ Y' where
  hom := e'.homEquiv.symm (e.homEquiv (𝟙 Y))
  inv := e.homEquiv.symm (e'.homEquiv (𝟙 Y'))
  hom_inv_id := e.homEquiv.injective (by
    rw [e.homEquiv_comp, Equiv.apply_symm_apply, ← e'.homEquiv_comp, Category.comp_id,
      Equiv.apply_symm_apply])
  inv_hom_id := e'.homEquiv.injective (by
    rw [e'.homEquiv_comp, Equiv.apply_symm_apply, ← e.homEquiv_comp, Category.comp_id,
      Equiv.apply_symm_apply])

/-- The comparison keeps the represented elements. -/
theorem homEquiv_comp_comparisonIso_hom {F : Dᵒᵖ ⥤ Type v} {Y Y' : D}
    (e : F.RepresentableBy Y) (e' : F.RepresentableBy Y') {Z : D} (f : Z ⟶ Y) :
    e'.homEquiv (f ≫ (comparisonIso e e').hom) = e.homEquiv f := by
  change e'.homEquiv (f ≫ e'.homEquiv.symm (e.homEquiv (𝟙 Y))) = _
  rw [e'.homEquiv_comp, Equiv.apply_symm_apply, ← e.homEquiv_comp, Category.comp_id]

theorem homEquiv_comp_comparisonIso_inv {F : Dᵒᵖ ⥤ Type v} {Y Y' : D}
    (e : F.RepresentableBy Y) (e' : F.RepresentableBy Y') {Z : D} (f : Z ⟶ Y') :
    e.homEquiv (f ≫ (comparisonIso e e').inv) = e'.homEquiv f := by
  change e.homEquiv (f ≫ e.homEquiv.symm (e'.homEquiv (𝟙 Y'))) = _
  rw [e.homEquiv_comp, Equiv.apply_symm_apply, ← e'.homEquiv_comp, Category.comp_id]

end Mettapedia.CategoryTheory.RepresentableLift
