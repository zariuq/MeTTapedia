import Mettapedia.CategoryTheory.InternalCategoryLocalDiagrams

/-!
# Transport of an internal category along its vertex isomorphism

The edge object and every supplied edge remain intact. Endpoints and units
are transported through the independently supplied vertex comparison.
Composition uses an actual comparison of the two chosen matching pullbacks;
its complete reading derives the category laws at every generalized stage.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryVertexIso

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (original : InternalCategory C) {vertex : C} (comparison : vertex ≅ original.vertex)

def source : original.edge ⟶ vertex := original.source ≫ comparison.inv
def target : original.edge ⟶ vertex := original.target ≫ comparison.inv

theorem matching {stage : C} (first second : stage ⟶ original.edge)
    (supplied : first ≫ target original comparison = second ≫ source original comparison) :
    first ≫ original.target = second ≫ original.source := by
  apply (cancel_mono comparison.inv).mp
  simpa only [source, target, Category.assoc] using supplied

def endpoints : InternalCategoryLocalDiagrams.Endpoints C where
  vertex := vertex
  edge := original.edge
  source := source original comparison
  target := target original comparison
  unit := comparison.hom ≫ original.unit
  composition := original.compose
    (pullback.fst (target original comparison) (source original comparison))
    (pullback.snd (target original comparison) (source original comparison))
    (matching original comparison _ _ pullback.condition)
  unit_source := by
    change (comparison.hom ≫ original.unit) ≫ (original.source ≫ comparison.inv) = 𝟙 vertex
    rw [Category.assoc, ← Category.assoc original.unit original.source comparison.inv,
      original.unit_source, Category.id_comp, Iso.hom_inv_id]
  unit_target := by
    change (comparison.hom ≫ original.unit) ≫ (original.target ≫ comparison.inv) = 𝟙 vertex
    rw [Category.assoc, ← Category.assoc original.unit original.target comparison.inv,
      original.unit_target, Category.id_comp, Iso.hom_inv_id]
  composition_source := by
    change original.compose _ _ _ ≫ (original.source ≫ comparison.inv) =
      pullback.fst (target original comparison) (source original comparison) ≫ (original.source ≫ comparison.inv)
    rw [← Category.assoc, original.compose_source, Category.assoc]
  composition_target := by
    change original.compose _ _ _ ≫ (original.target ≫ comparison.inv) =
      pullback.snd (target original comparison) (source original comparison) ≫ (original.target ≫ comparison.inv)
    rw [← Category.assoc, original.compose_target, Category.assoc]

theorem complete_compose_read {stage : C} (first second : stage ⟶ original.edge)
    (supplied : first ≫ target original comparison = second ≫ source original comparison) :
    InternalCategoryLocalDiagrams.compose (endpoints original comparison) first second supplied =
      original.compose first second (matching original comparison first second supplied) := by
  change pullback.lift first second supplied ≫
      (pullback.lift _ _ _ ≫ original.composition) =
        pullback.lift first second _ ≫ original.composition
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]

theorem compose_congr {stage : C} {first first' second second' : stage ⟶ original.edge}
    (firstRead : first = first') (secondRead : second = second')
    (before : first ≫ original.target = second ≫ original.source)
    (after : first' ≫ original.target = second' ≫ original.source) :
    original.compose first second before = original.compose first' second' after := by
  subst first'
  subst second'
  rfl

def category : InternalCategory C where
  toInternalGraph := (endpoints original comparison).toInternalGraph
  unit := (endpoints original comparison).unit
  composition := (endpoints original comparison).composition
  unit_source := (endpoints original comparison).unit_source
  unit_target := (endpoints original comparison).unit_target
  composition_source := (endpoints original comparison).composition_source
  composition_target := (endpoints original comparison).composition_target
  unit_left := by
    have input : source original comparison ≫ (comparison.hom ≫ original.unit) =
        original.source ≫ original.unit := by
      simp only [source, Category.assoc, Iso.inv_hom_id_assoc]
    exact (complete_compose_read original comparison _ _ _).trans
      ((compose_congr original input rfl _ _).trans original.unit_left)
  unit_right := by
    have input : target original comparison ≫ (comparison.hom ≫ original.unit) =
        original.target ≫ original.unit := by
      simp only [target, Category.assoc, Iso.inv_hom_id_assoc]
    exact (complete_compose_read original comparison _ _ _).trans
      ((compose_congr original rfl input _ _).trans original.unit_right)
  associativity := by
    intro stage first second third firstMatch secondMatch
    have firstRead := complete_compose_read original comparison first second firstMatch
    have secondRead := complete_compose_read original comparison second third secondMatch
    have before := matching original comparison first second firstMatch
    have after := matching original comparison second third secondMatch
    have leftRead : InternalCategoryLocalDiagrams.compose (endpoints original comparison)
        (InternalCategoryLocalDiagrams.compose (endpoints original comparison) first second firstMatch)
          third (by rw [InternalCategoryLocalDiagrams.compose_target]; exact secondMatch) =
        original.compose (original.compose first second before) third
          (by rw [original.compose_target]; exact after) :=
      (complete_compose_read original comparison _ _ _).trans
        (compose_congr original firstRead rfl _ _)
    have rightRead : InternalCategoryLocalDiagrams.compose (endpoints original comparison) first
        (InternalCategoryLocalDiagrams.compose (endpoints original comparison) second third secondMatch)
          (by rw [InternalCategoryLocalDiagrams.compose_source]; exact firstMatch) =
        original.compose first (original.compose second third after)
          (by rw [original.compose_source]; exact before) :=
      (complete_compose_read original comparison _ _ _).trans
        (compose_congr original rfl secondRead _ _)
    exact leftRead.trans ((original.associativity stage first second third before after).trans rightRead.symm)

def toOriginal : InternalCategory.Hom (category original comparison) original where
  vertex := comparison.hom
  edge := 𝟙 original.edge
  source := by simp only [category, endpoints, source, Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  target := by simp only [category, endpoints, target, Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  unit := Category.comp_id _
  composition := by
    change (pullback.lift _ _ _ ≫ original.composition) ≫ 𝟙 original.edge = _ ≫ original.composition
    rw [Category.comp_id]
    congr 1
    apply pullback.hom_ext
    · simp only [InternalGraph.Hom.composableMap, pullback.lift_fst]
      exact (Category.comp_id _).symm
    · simp only [InternalGraph.Hom.composableMap, pullback.lift_snd]
      exact (Category.comp_id _).symm

end Mettapedia.CategoryTheory.InternalCategoryVertexIso
