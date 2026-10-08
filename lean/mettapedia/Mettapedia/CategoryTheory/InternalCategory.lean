import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Internal graphs, categories and their complete arrow maps

Composition has the actual chosen pullback of target and source as its
domain. Associativity is stated on arbitrary generalized elements with both
matching equations; identities and composition keep both endpoint maps.
This interface supplies no existence theorem for an arbitrary graph.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable (C : Type u) [Category.{v} C]

structure InternalGraph where
  vertex : C
  edge : C
  source : edge ⟶ vertex
  target : edge ⟶ vertex

namespace InternalGraph

variable {C}

structure Hom (first second : InternalGraph C) where
  vertex : first.vertex ⟶ second.vertex
  edge : first.edge ⟶ second.edge
  source : edge ≫ second.source = first.source ≫ vertex
  target : edge ≫ second.target = first.target ≫ vertex

variable [HasPullbacks C]

abbrev Composable (graph : InternalGraph C) := pullback graph.target graph.source

def composeWith (graph : InternalGraph C)
    (composition : graph.Composable ⟶ graph.edge)
    {X : C} (first second : X ⟶ graph.edge)
    (matching : first ≫ graph.target = second ≫ graph.source) : X ⟶ graph.edge :=
  pullback.lift first second matching ≫ composition

def Hom.composableMap {first second : InternalGraph C} (map : Hom first second) :
    first.Composable ⟶ second.Composable :=
  pullback.lift (pullback.fst _ _ ≫ map.edge) (pullback.snd _ _ ≫ map.edge)
    (by
      rw [Category.assoc, map.target, ← Category.assoc, pullback.condition,
        Category.assoc, ← map.source, ← Category.assoc])

@[reassoc (attr := simp)] theorem Hom.composableMap_first
    {first second : InternalGraph C} (map : Hom first second) :
    map.composableMap ≫ pullback.fst _ _ = pullback.fst _ _ ≫ map.edge :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem Hom.composableMap_second
    {first second : InternalGraph C} (map : Hom first second) :
    map.composableMap ≫ pullback.snd _ _ = pullback.snd _ _ ≫ map.edge :=
  pullback.lift_snd _ _ _

end InternalGraph

variable [HasPullbacks C]

structure InternalCategory extends InternalGraph C where
  unit : vertex ⟶ edge
  composition : toInternalGraph.Composable ⟶ edge
  unit_source : unit ≫ source = 𝟙 vertex
  unit_target : unit ≫ target = 𝟙 vertex
  composition_source : composition ≫ source = pullback.fst target source ≫ source
  composition_target : composition ≫ target = pullback.snd target source ≫ target
  unit_left : toInternalGraph.composeWith composition (source ≫ unit) (𝟙 edge)
      (by rw [Category.assoc, unit_target, Category.comp_id, Category.id_comp]) = 𝟙 edge
  unit_right : toInternalGraph.composeWith composition (𝟙 edge) (target ≫ unit)
      (by rw [Category.assoc, unit_source, Category.comp_id, Category.id_comp]) = 𝟙 edge
  associativity : ∀ (X : C) (first second third : X ⟶ edge)
      (firstMatch : first ≫ target = second ≫ source)
      (secondMatch : second ≫ target = third ≫ source),
    toInternalGraph.composeWith composition
      (toInternalGraph.composeWith composition first second firstMatch) third
      (by
        rw [InternalGraph.composeWith, Category.assoc, composition_target,
          ← Category.assoc, pullback.lift_snd]
        exact secondMatch) =
    toInternalGraph.composeWith composition first
      (toInternalGraph.composeWith composition second third secondMatch)
      (by
        rw [InternalGraph.composeWith, Category.assoc, composition_source,
          ← Category.assoc, pullback.lift_fst]
        exact firstMatch)

namespace InternalCategory

variable {C}

abbrev compose (category : InternalCategory C) {X : C}
    (first second : X ⟶ category.edge)
    (matching : first ≫ category.target = second ≫ category.source) : X ⟶ category.edge :=
  category.toInternalGraph.composeWith category.composition first second matching

@[reassoc] theorem compose_source (category : InternalCategory C) {X : C}
    (first second : X ⟶ category.edge)
    (matching : first ≫ category.target = second ≫ category.source) :
    category.compose first second matching ≫ category.source = first ≫ category.source := by
  rw [compose, InternalGraph.composeWith, Category.assoc, category.composition_source,
    ← Category.assoc, pullback.lift_fst]

@[reassoc] theorem compose_target (category : InternalCategory C) {X : C}
    (first second : X ⟶ category.edge)
    (matching : first ≫ category.target = second ≫ category.source) :
    category.compose first second matching ≫ category.target = second ≫ category.target := by
  rw [compose, InternalGraph.composeWith, Category.assoc, category.composition_target,
    ← Category.assoc, pullback.lift_snd]

structure Hom (first second : InternalCategory C) extends
    InternalGraph.Hom first.toInternalGraph second.toInternalGraph where
  unit : first.unit ≫ edge = vertex ≫ second.unit
  composition : first.composition ≫ edge = toHom.composableMap ≫ second.composition

theorem Hom.compose_readout {first second : InternalCategory C} (map : Hom first second)
    {X : C} (left right : X ⟶ first.edge)
    (matching : left ≫ first.target = right ≫ first.source) :
    first.compose left right matching ≫ map.edge =
      second.compose (left ≫ map.edge) (right ≫ map.edge)
        (by rw [Category.assoc, map.target, ← Category.assoc, matching,
          Category.assoc, ← map.source, ← Category.assoc]) := by
  simp only [compose, InternalGraph.composeWith, Category.assoc]
  rw [map.composition]
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, map.toHom.composableMap_first, ← Category.assoc,
      pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, map.toHom.composableMap_second, ← Category.assoc,
      pullback.lift_snd, pullback.lift_snd]

end InternalCategory

end Mettapedia.CategoryTheory
