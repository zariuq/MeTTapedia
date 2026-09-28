import Mettapedia.OSLF.Syntax.ContextualEquationClassEvents
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Free adjoining of retained events over a fixed state presheaf

A graph over a fixed presheaf of states has an edge presheaf and natural
source/target maps. Given an authored generator graph, the pointwise disjoint
sum freely adjoins those events to any existing graph. Both injections and
the copairing property preserve the endpoint maps, rather than only the
underlying edge sets. This is the graph-adjunction layer of an operational
presentation; it does not assert finite limits or cartesian closure of the
larger classifying theory.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FreePresheafEventExtension

open _root_.CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]

/-- A presheaf-internal graph whose state object is fixed. -/
structure Graph (vertex : C ⥤ Type w) where
  edge : C ⥤ Type w
  source : edge ⟶ vertex
  target : edge ⟶ vertex

/-- A map of event graphs over the identity on states. -/
structure Hom {vertex : C ⥤ Type w} (first later : Graph vertex) where
  edgeMap : first.edge ⟶ later.edge
  source_comm : edgeMap ≫ later.source = first.source
  target_comm : edgeMap ≫ later.target = first.target

namespace Hom

@[ext] theorem ext {vertex : C ⥤ Type w} {first later : Graph vertex}
    {f g : Hom first later} (agree : f.edgeMap = g.edgeMap) : f = g := by
  cases f
  cases g
  congr

def id {vertex : C ⥤ Type w} (G : Graph vertex) : Hom G G where
  edgeMap := 𝟙 G.edge
  source_comm := by simp
  target_comm := by simp

def comp {vertex : C ⥤ Type w} {G H K : Graph vertex}
    (f : Hom G H) (g : Hom H K) : Hom G K where
  edgeMap := f.edgeMap ≫ g.edgeMap
  source_comm := by rw [Category.assoc, g.source_comm, f.source_comm]
  target_comm := by rw [Category.assoc, g.target_comm, f.target_comm]

end Hom

instance graphCategory (vertex : C ⥤ Type w) : Category (Graph vertex) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro G H f
    apply Hom.ext
    simp [Hom.comp, Hom.id]
  comp_id := by
    intro G H f
    apply Hom.ext
    simp [Hom.comp, Hom.id]
  assoc := by
    intro G H K L f g h
    apply Hom.ext
    simp [Hom.comp, Category.assoc]

/-- Pointwise sum of edge presheaves, retaining their individual reindexing. -/
def edgeSum (left right : C ⥤ Type w) : C ⥤ Type w where
  obj X := Sum (left.obj X) (right.obj X)
  map f := TypeCat.ofHom (fun
    | .inl event => .inl (left.map f event)
    | .inr event => .inr (right.map f event))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro event
    cases event <;> simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro event
    cases event <;> simp

/-- The left injection is natural under all substitutions in the base. -/
def inlEdge (left right : C ⥤ Type w) : left ⟶ edgeSum left right where
  app X := TypeCat.ofHom Sum.inl
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    rfl

/-- The right injection is natural under all substitutions in the base. -/
def inrEdge (left right : C ⥤ Type w) : right ⟶ edgeSum left right where
  app X := TypeCat.ofHom Sum.inr
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    rfl

/-- Copair two natural transformations out of the summands. -/
def copair {left right target : C ⥤ Type w}
    (f : left ⟶ target) (g : right ⟶ target) :
    edgeSum left right ⟶ target where
  app X := TypeCat.ofHom (fun
    | .inl event => f.app X event
    | .inr event => g.app X event)
  naturality X Y arrow := by
    apply ConcreteCategory.hom_ext
    intro event
    cases event with
    | inl event =>
        exact congrArg (fun h : left.obj X ⟶ target.obj Y => h event)
          (f.naturality arrow)
    | inr event =>
        exact congrArg (fun h : right.obj X ⟶ target.obj Y => h event)
          (g.naturality arrow)

theorem inl_copair {left right target : C ⥤ Type w}
    (f : left ⟶ target) (g : right ⟶ target) :
    inlEdge left right ≫ copair f g = f := by
  ext X event
  rfl

theorem inr_copair {left right target : C ⥤ Type w}
    (f : left ⟶ target) (g : right ⟶ target) :
    inrEdge left right ≫ copair f g = g := by
  ext X event
  rfl

theorem copair_unique {left right target : C ⥤ Type w}
    (f : left ⟶ target) (g : right ⟶ target)
    (h : edgeSum left right ⟶ target)
    (leftEq : inlEdge left right ≫ h = f)
    (rightEq : inrEdge left right ≫ h = g) :
    h = copair f g := by
  ext X event
  cases event with
  | inl event =>
      have atEvent := congrArg
        (fun morphism : left.obj X ⟶ target.obj X => morphism event)
        (NatTrans.congr_app leftEq X)
      exact atEvent
  | inr event =>
      have atEvent := congrArg
        (fun morphism : right.obj X ⟶ target.obj X => morphism event)
        (NatTrans.congr_app rightEq X)
      exact atEvent

/-- Disjointly adjoin the events of `right` to the events of `left`. -/
def graphSum {vertex : C ⥤ Type w}
    (left right : Graph vertex) : Graph vertex where
  edge := edgeSum left.edge right.edge
  source := copair left.source right.source
  target := copair left.target right.target

/-- The original graph embeds into the free extension. -/
def graphInl {vertex : C ⥤ Type w}
    (left right : Graph vertex) : Hom left (graphSum left right) where
  edgeMap := inlEdge left.edge right.edge
  source_comm := inl_copair left.source right.source
  target_comm := inl_copair left.target right.target

/-- The authored generator graph embeds into the free extension. -/
def graphInr {vertex : C ⥤ Type w}
    (left right : Graph vertex) : Hom right (graphSum left right) where
  edgeMap := inrEdge left.edge right.edge
  source_comm := inr_copair left.source right.source
  target_comm := inr_copair left.target right.target

/-- A pair of endpoint-preserving graph maps extends to exactly one map from
the graph with both sets of events. -/
def graphCopair {vertex : C ⥤ Type w}
    {left right target : Graph vertex}
    (f : Hom left target) (g : Hom right target) :
    Hom (graphSum left right) target where
  edgeMap := copair f.edgeMap g.edgeMap
  source_comm := by
    change copair f.edgeMap g.edgeMap ≫ target.source =
      copair left.source right.source
    apply copair_unique left.source right.source
    · rw [← Category.assoc, inl_copair, f.source_comm]
    · rw [← Category.assoc, inr_copair, g.source_comm]
  target_comm := by
    change copair f.edgeMap g.edgeMap ≫ target.target =
      copair left.target right.target
    apply copair_unique left.target right.target
    · rw [← Category.assoc, inl_copair, f.target_comm]
    · rw [← Category.assoc, inr_copair, g.target_comm]

theorem graphInl_copair {vertex : C ⥤ Type w}
    {left right target : Graph vertex}
    (f : Hom left target) (g : Hom right target) :
    Hom.comp (graphInl left right) (graphCopair f g) = f := by
  apply Hom.ext
  exact inl_copair f.edgeMap g.edgeMap

theorem graphInr_copair {vertex : C ⥤ Type w}
    {left right target : Graph vertex}
    (f : Hom left target) (g : Hom right target) :
    Hom.comp (graphInr left right) (graphCopair f g) = g := by
  apply Hom.ext
  exact inr_copair f.edgeMap g.edgeMap

theorem graphCopair_unique {vertex : C ⥤ Type w}
    {left right target : Graph vertex}
    (f : Hom left target) (g : Hom right target)
    (h : Hom (graphSum left right) target)
    (leftEq : Hom.comp (graphInl left right) h = f)
    (rightEq : Hom.comp (graphInr left right) h = g) :
    h = graphCopair f g := by
  apply Hom.ext
  exact copair_unique f.edgeMap g.edgeMap h.edgeMap
    (congrArg Hom.edgeMap leftEq) (congrArg Hom.edgeMap rightEq)

/-! ## Graphs equipped with an interpretation of authored generators -/

/-- A graph with a chosen, endpoint-preserving interpretation of the authored
generator events. -/
structure Equipped {vertex : C ⥤ Type w} (generators : Graph vertex) where
  graph : Graph vertex
  generatorMap : Hom generators graph

/-- Maps of equipped graphs commute with the chosen generator interpretation. -/
structure EquippedHom {vertex : C ⥤ Type w} {generators : Graph vertex}
    (first later : Equipped generators) where
  graphMap : Hom first.graph later.graph
  generator_comm : Hom.comp first.generatorMap graphMap = later.generatorMap

namespace EquippedHom

@[ext] theorem ext {vertex : C ⥤ Type w} {generators : Graph vertex}
    {first later : Equipped generators} {f g : EquippedHom first later}
    (agree : f.graphMap = g.graphMap) : f = g := by
  cases f
  cases g
  congr

def id {vertex : C ⥤ Type w} {generators : Graph vertex}
    (A : Equipped generators) : EquippedHom A A where
  graphMap := Hom.id A.graph
  generator_comm := by
    apply Hom.ext
    simp [Hom.comp, Hom.id]

def comp {vertex : C ⥤ Type w} {generators : Graph vertex}
    {A B D : Equipped generators}
    (f : EquippedHom A B) (g : EquippedHom B D) : EquippedHom A D where
  graphMap := Hom.comp f.graphMap g.graphMap
  generator_comm := by
    calc
      Hom.comp A.generatorMap (Hom.comp f.graphMap g.graphMap) =
          Hom.comp (Hom.comp A.generatorMap f.graphMap) g.graphMap := by
            apply Hom.ext
            simp [Hom.comp, Category.assoc]
      _ = Hom.comp B.generatorMap g.graphMap := by rw [f.generator_comm]
      _ = D.generatorMap := g.generator_comm

end EquippedHom

instance equippedCategory {vertex : C ⥤ Type w}
    (generators : Graph vertex) : Category (Equipped generators) where
  Hom := EquippedHom
  id := EquippedHom.id
  comp := EquippedHom.comp
  id_comp := by
    intro A B f
    apply EquippedHom.ext
    apply Hom.ext
    simp [EquippedHom.comp, EquippedHom.id, Hom.comp, Hom.id]
  comp_id := by
    intro A B f
    apply EquippedHom.ext
    apply Hom.ext
    simp [EquippedHom.comp, EquippedHom.id, Hom.comp, Hom.id]
  assoc := by
    intro A B D E f g h
    apply EquippedHom.ext
    apply Hom.ext
    simp [EquippedHom.comp, Hom.comp, Category.assoc]

/-- Forget the chosen generator interpretation, retaining the entire graph. -/
def forget {vertex : C ⥤ Type w}
    (generators : Graph vertex) : Equipped generators ⥤ Graph vertex where
  obj A := A.graph
  map f := f.graphMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The disjoint-sum graph interprets each authored event by its right
injection. No event of the original graph is identified with a new one. -/
def freeObject {vertex : C ⥤ Type w}
    (generators G : Graph vertex) : Equipped generators where
  graph := graphSum G generators
  generatorMap := graphInr G generators

/-- A graph map acts on the old summand; the newly adjoined generators remain
the same authored events. -/
def freeMap {vertex : C ⥤ Type w} {generators G H : Graph vertex}
    (f : Hom G H) : EquippedHom (freeObject generators G)
      (freeObject generators H) where
  graphMap := graphCopair
    (Hom.comp f (graphInl H generators)) (graphInr H generators)
  generator_comm := graphInr_copair _ _

theorem freeMap_old {vertex : C ⥤ Type w}
    {generators G H : Graph vertex} (f : Hom G H) :
    Hom.comp (graphInl G generators) (freeMap f).graphMap =
      Hom.comp f (graphInl H generators) :=
  graphInl_copair _ _

/-- Free adjoining of one fixed graph of event generators acts functorially
on all endpoint-preserving maps of existing graphs. -/
def free {vertex : C ⥤ Type w}
    (generators : Graph vertex) : Graph vertex ⥤ Equipped generators where
  obj := freeObject generators
  map := freeMap
  map_id G := by
    apply EquippedHom.ext
    apply Hom.ext
    ext X event
    cases event <;> rfl
  map_comp f g := by
    apply EquippedHom.ext
    apply Hom.ext
    ext X event
    cases event <;> rfl

/-- An interpretation of the freely adjoined graph is exactly a graph map
out of the old part, together with the target's already chosen interpretation
of the authored generators. -/
def freeHomEquiv {vertex : C ⥤ Type w}
    (generators G : Graph vertex) (A : Equipped generators) :
    ((freeObject generators G) ⟶ A) ≃ (G ⟶ A.graph) where
  toFun h := Hom.comp (graphInl G generators) h.graphMap
  invFun f :=
    { graphMap := graphCopair f A.generatorMap
      generator_comm := graphInr_copair f A.generatorMap }
  left_inv h := by
    apply EquippedHom.ext
    exact (graphCopair_unique
      (Hom.comp (graphInl G generators) h.graphMap)
      A.generatorMap h.graphMap rfl h.generator_comm).symm
  right_inv f := graphInl_copair f A.generatorMap

/-- Free adjoining of a fixed graph of authored events is left adjoint to
forgetting its chosen interpretation. The hom equivalence is the explicit
copairing construction above, not an assumed adjunction field. -/
def freeAdjunction {vertex : C ⥤ Type w}
    (generators : Graph vertex) : free generators ⊣ forget generators :=
  Adjunction.mkOfHomEquiv
    { homEquiv := freeHomEquiv generators
      homEquiv_naturality_left_symm := by
        intro G H A f h
        apply EquippedHom.ext
        apply Hom.ext
        ext X event
        cases event <;> rfl
      homEquiv_naturality_right := by
        intro G A B f h
        apply Hom.ext
        ext X event
        rfl }

/-! ## The generator graph as the free extension of no prior events -/

/-- The empty edge presheaf is the true no-event graph carrier. -/
def emptyEdge : C ⥤ Type w where
  obj _ := PEmpty
  map _ := TypeCat.ofHom PEmpty.elim
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro event
    exact event.elim
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro event
    exact event.elim

/-- There is exactly one natural map out of the empty edge presheaf. -/
def emptyEdgeMap (target : C ⥤ Type w) : emptyEdge ⟶ target where
  app X := TypeCat.ofHom PEmpty.elim
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    exact event.elim

/-- An event graph with the given vertices and no events. -/
def emptyGraph (vertex : C ⥤ Type w) : Graph vertex where
  edge := emptyEdge
  source := emptyEdgeMap vertex
  target := emptyEdgeMap vertex

/-- The empty graph has a unique endpoint-preserving map to every graph over
the same state presheaf. -/
def fromEmptyGraph {vertex : C ⥤ Type w}
    (target : Graph vertex) : Hom (emptyGraph vertex) target where
  edgeMap := emptyEdgeMap target.edge
  source_comm := by
    ext X event
    exact event.elim
  target_comm := by
    ext X event
    exact event.elim

theorem fromEmptyGraph_unique {vertex : C ⥤ Type w}
    (target : Graph vertex) (candidate : Hom (emptyGraph vertex) target) :
    candidate = fromEmptyGraph target := by
  apply Hom.ext
  ext X event
  exact event.elim

/-- The no-event graph is initial in the category of graphs over fixed
states. This is not the empty graph of states: all states remain present. -/
def emptyGraphIsInitial (vertex : C ⥤ Type w) :
    CategoryTheory.Limits.IsInitial (emptyGraph vertex) :=
  CategoryTheory.Limits.IsInitial.ofUniqueHom fromEmptyGraph
    (fun target candidate => fromEmptyGraph_unique target candidate)

/-- The free extension of the no-event graph is initial among graph models
equipped with an interpretation of the specified authored generators. -/
def freeGeneratedIsInitial {vertex : C ⥤ Type w}
    (generators : Graph vertex) :
    CategoryTheory.Limits.IsInitial
      (freeObject generators (emptyGraph vertex)) :=
  CategoryTheory.Limits.IsInitial.ofUniqueHom
    (fun A => (freeHomEquiv generators (emptyGraph vertex) A).symm
      (fromEmptyGraph A.graph))
    (fun A candidate => by
      apply (freeHomEquiv generators (emptyGraph vertex) A).injective
      exact fromEmptyGraph_unique A.graph _)

end Mettapedia.OSLF.Binding.FreePresheafEventExtension
