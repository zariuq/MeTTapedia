import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadout

/-!
# Literal child recovery for constructed polynomial readouts

The left and right tags in the constructed graph let child recovery
retain a computational orientation. No existential graph edge is used
to choose a child or select a presentation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutChildren

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams
open ContextualGraphPolynomialReadoutNodes
universe u
variable {D : Type u} [Category.{u} D] {states : D ⥤ Type u}
variable (branches : states.Elements ⥤ Type u) (labels : NaturalHom states (values D))
variable (arguments : NaturalHom (total branches) (values D)) (successor : NaturalHom (total branches) states)
variable {point : D}

def pairChild (left right : Node branches labels arguments point)
    (child : Child D (value branches labels arguments successor (.pair left right))) :
    PLift (child.val = .left left) ⊕ PLift (child.val = .right right) := by
  rcases child with ⟨node, edge⟩
  cases node with
  | left node => exact .inl ⟨by cases edge; rfl⟩
  | right node => exact .inr ⟨by cases edge; rfl⟩
  | state _ | collection _ | branch _ | label _ | argument _ | pair _ _ => exact False.elim (by cases edge)

def stateChild (state : states.obj point)
    (child : Child D (value branches labels arguments successor (.state state))) :
    PLift (child.val = .left (.pair (labelRoot branches labels arguments point state)
      (labelRoot branches labels arguments point state))) ⊕
    PLift (child.val = .right (.pair (labelRoot branches labels arguments point state) (.collection state))) := by
  rcases child with ⟨node, edge⟩
  cases node with
  | left node => exact .inl ⟨by cases edge; rfl⟩
  | right node => exact .inr ⟨by cases edge; rfl⟩
  | state _ | collection _ | branch _ | label _ | argument _ | pair _ _ => exact False.elim (by cases edge)

def branchChild (receipt : (total branches).obj point)
    (child : Child D (value branches labels arguments successor (.branch receipt))) :
    PLift (child.val = .left (.pair (argumentRoot branches labels arguments point receipt)
      (argumentRoot branches labels arguments point receipt))) ⊕
    PLift (child.val = .right (.pair (argumentRoot branches labels arguments point receipt)
      (.state (successor.app point receipt)))) := by
  rcases child with ⟨node, edge⟩
  cases node with
  | left node => exact .inl ⟨by cases edge; rfl⟩
  | right node => exact .inr ⟨by cases edge; rfl⟩
  | state _ | collection _ | branch _ | label _ | argument _ | pair _ _ => exact False.elim (by cases edge)

def collectionChild (state : states.obj point)
    (child : Child D (value branches labels arguments successor (.collection state))) :
    Σ branch : branches.obj ⟨point, state⟩, PLift (child.val = .branch ⟨state, branch⟩) := by
  rcases child with ⟨node, edge⟩
  cases node with
  | branch receipt =>
    rcases receipt with ⟨other, branch⟩
    have same : other = state := by cases edge; rfl
    subst other
    exact ⟨branch, ⟨rfl⟩⟩
  | state _ | collection _ | label _ | argument _ | pair _ _ | left _ | right _ => exact False.elim (by cases edge)

def leftChild (parent : Node branches labels arguments point)
    (child : Child D (value branches labels arguments successor (.left parent))) :
    Σ actual : Child D (value branches labels arguments successor parent), PLift (child.val = .left actual.val) := by
  rcases child with ⟨node, edge⟩
  cases node with
  | left node =>
    exact ⟨⟨node, by cases edge with | left edge => exact edge⟩, ⟨rfl⟩⟩
  | state _ | collection _ | branch _ | label _ | argument _ | pair _ _ | right _ => exact False.elim (by cases edge)

def rightChild (parent : Node branches labels arguments point)
    (child : Child D (value branches labels arguments successor (.right parent))) :
    Σ actual : Child D (value branches labels arguments successor parent), PLift (child.val = .right actual.val) := by
  rcases child with ⟨node, edge⟩
  cases node with
  | right node =>
    exact ⟨⟨node, by cases edge with | right edge => exact edge⟩, ⟨rfl⟩⟩
  | state _ | collection _ | branch _ | label _ | argument _ | pair _ _ | left _ => exact False.elim (by cases edge)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutChildren
