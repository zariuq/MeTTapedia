import Mettapedia.TypeTheory.MaterialSets.Hypersets.LabelledDependentProducts
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedLabelledBisimulation

/-!
# Actual graph labels for indexed contextual W branches

Root observations retain the current world and actual material shape value.
Branch observations retain that root, the future world, the actual arrow,
and the actual dependent position value. The encoders are constructed from
authored world/arrow graph labels and the material shape/position models.
Their injectivity is proved; no inverse for a host world or arrow is needed.
All label graphs stay at the input graph bound.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWLabels

open CategoryTheory
open AccessiblePointedGraph

universe u
variable {D : Type u} [Category.{u} D]
variable (shape : D ⥤ Type u) (position : shape.Elements ⥤ Type u)
variable (worlds : ArgumentCoding D)
variable (arrows : (source target : D) → ArgumentCoding (source ⟶ target))
variable (shapes : (world : D) → PresentedType (shape.obj world))
variable (positions : (point : shape.Elements) → PresentedType (position.obj point))

def materialCoding {A : Type u} (model : PresentedType A) : ArgumentCoding A where
  graph := model.termGraph
  injective := by
    intro first second same
    change HSet.mk (model.termGraph first) = HSet.mk (model.termGraph second) at same
    rw [PresentedType.mk_termGraph, PresentedType.mk_termGraph] at same
    exact model.value_injective same

abbrev Branch {X : D} (label : shape.obj X) :=
  (Y : D) × (arrow : X ⟶ Y) × position.obj ⟨Y, shape.map arrow label⟩

def shapeCoding : ArgumentCoding shape.Elements :=
  worlds.sigma (fun X => materialCoding (shapes X))

def branchCoding {X : D} (label : shape.obj X) : ArgumentCoding (Branch shape position label) :=
  worlds.sigma (fun Y => (arrows X Y).sigma
    (fun arrow => materialCoding (positions ⟨Y, shape.map arrow label⟩)))

abbrev Label := Sum shape.Elements ((point : shape.Elements) × Branch shape position point.2)

def shapeTag (world : D) (original : HSet.{u}) : HSet.{u} :=
  HSet.kpair ∅ (HSet.kpair (worlds.reading world) original)

def positionTag (point : shape.Elements) (branch : Branch shape position point.2) : HSet.{u} :=
  HSet.kpair {∅} (HSet.kpair ((shapeCoding shape worlds shapes).reading point)
    ((branchCoding shape position worlds arrows positions point.2).reading branch))

theorem shapeTag_ne_positionTag (world : D) (original : HSet.{u})
    (point : shape.Elements) (branch : Branch shape position point.2) :
    shapeTag worlds world original ≠ positionTag shape position worlds arrows shapes positions point branch :=
  fun same => HSet.empty_ne_singleton_empty (HSet.kpair_inj.mp same).1

def labelValue : Label shape position → HSet.{u}
  | .inl point => shapeTag worlds point.1 ((shapes point.1).value point.2)
  | .inr ⟨point, branch⟩ => positionTag shape position worlds arrows shapes positions point branch

theorem shapeCoding_reading (point : shape.Elements) :
    (shapeCoding shape worlds shapes).reading point =
      HSet.kpair (worlds.reading point.1) ((shapes point.1).value point.2) := by
  dsimp only [ArgumentCoding.reading, shapeCoding, ArgumentCoding.sigma, materialCoding]
  rw [mk_kpairGraph]
  rw [PresentedType.mk_termGraph]

theorem labelValue_injective : Function.Injective (labelValue shape position worlds arrows shapes positions) := by
  intro first second same
  cases first with
  | inl point =>
    cases second with
    | inl other =>
      have values := (HSet.kpair_inj.mp same).2
      have pointSame := (shapeCoding shape worlds shapes).injective
        ((shapeCoding_reading shape worlds shapes point).trans
          (values.trans (shapeCoding_reading shape worlds shapes other).symm))
      exact congrArg Sum.inl pointSame
    | inr pair => exact (shapeTag_ne_positionTag shape position worlds arrows shapes positions point.1 _ pair.1 pair.2 same).elim
  | inr pair =>
    cases second with
    | inl point => exact (shapeTag_ne_positionTag shape position worlds arrows shapes positions point.1 _ pair.1 pair.2 same.symm).elim
    | inr other =>
      rcases pair with ⟨point, branch⟩
      rcases other with ⟨otherPoint, otherBranch⟩
      have components := HSet.kpair_inj.mp (HSet.kpair_inj.mp same).2
      have pointSame := (shapeCoding shape worlds shapes).injective components.1
      cases pointSame
      have branchSame := (branchCoding shape position worlds arrows positions point.2).injective components.2
      cases branchSame
      rfl

def labelGraph : Label shape position → AccessiblePointedGraph.{u}
  | .inl point => kpairGraph empty ((shapeCoding shape worlds shapes).graph point)
  | .inr ⟨point, branch⟩ => kpairGraph (singletonGraph empty)
      (kpairGraph ((shapeCoding shape worlds shapes).graph point)
        ((branchCoding shape position worlds arrows positions point.2).graph branch))

theorem mk_labelGraph (label : Label shape position) :
    HSet.mk (labelGraph shape position worlds arrows shapes positions label) =
      labelValue shape position worlds arrows shapes positions label := by
  cases label with
  | inl point =>
    rw [labelGraph, mk_kpairGraph, HSet.mk_empty, ArgumentCoding.mk_graph, shapeCoding_reading]
    rfl
  | inr pair =>
    rw [labelGraph, mk_kpairGraph, mk_singletonGraph, HSet.mk_empty, mk_kpairGraph,
      ArgumentCoding.mk_graph, ArgumentCoding.mk_graph]
    rfl

def labels : HSet.PresentedLabels (labelValue shape position worlds arrows shapes positions) :=
  ⟨labelGraph shape position worlds arrows shapes positions, mk_labelGraph shape position worlds arrows shapes positions⟩

theorem branchCoding_reading {X : D} (label : shape.obj X) (branch : Branch shape position label) :
    (branchCoding shape position worlds arrows positions label).reading branch =
      HSet.kpair (worlds.reading branch.1)
        (HSet.kpair ((arrows X branch.1).reading branch.2.1)
          ((positions ⟨branch.1, shape.map branch.2.1 label⟩).value branch.2.2)) := by
  dsimp only [ArgumentCoding.reading, branchCoding, ArgumentCoding.sigma, materialCoding]
  rw [mk_kpairGraph, mk_kpairGraph, PresentedType.mk_termGraph]

/-- Parallel arrows remain observable even when their actual transported
shape and position values agree. -/
theorem parallel_arrows_distinguished {X Y : D} (label : shape.obj X)
    (first second : X ⟶ Y) (different : first ≠ second)
    (left : position.obj ⟨Y, shape.map first label⟩)
    (right : position.obj ⟨Y, shape.map second label⟩) :
    (branchCoding shape position worlds arrows positions label).reading ⟨Y, first, left⟩ ≠
      (branchCoding shape position worlds arrows positions label).reading ⟨Y, second, right⟩ := by
  intro same
  rw [branchCoding_reading, branchCoding_reading] at same
  exact different ((arrows X Y).injective (HSet.kpair_inj.mp (HSet.kpair_inj.mp same).2).1)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWLabels
