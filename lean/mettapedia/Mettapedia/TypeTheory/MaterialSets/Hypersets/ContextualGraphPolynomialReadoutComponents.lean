import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutNodes
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphNaturalBodyEmbedding

/-!
# Actual body and component comparisons for polynomial readouts

All declared label and argument bodies are compared by the constructed
node embeddings and exact child recovery. The two component embeddings
of pairing preserve full future matching with their unwrapped values.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutComponents

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphPolynomialReadoutNodes
universe u
variable {D : Type u} [Category.{u} D] {states : D ⥤ Type u}
variable (branches : states.Elements ⥤ Type u) (labels : NaturalHom states (values D))
variable (arguments : NaturalHom (total branches) (values D))
variable (successor : NaturalHom (total branches) states)

def labelEmbedding : NaturalHom (total (ContextualGraphNaturalBodyEmbedding.bodyNodes labels))
    (diagram branches labels arguments successor).nodes where
  app _ receipt := .label receipt
  naturality _ _ := rfl

theorem labelForth : ContextualGraphNaturalBodyEmbedding.Forth labels
    (diagram branches labels arguments successor) (labelEmbedding branches labels arguments successor) :=
  fun _ receipt child => Edge.label receipt.1 child.property

def labelBack : ContextualGraphNaturalBodyEmbedding.Back labels
    (diagram branches labels arguments successor) (labelEmbedding branches labels arguments successor) := by
  intro point receipt child
  rcases child with ⟨node, available⟩
  cases node with
  | state state => exact False.elim (by cases available)
  | collection state => exact False.elim (by cases available)
  | branch receipt => exact False.elim (by cases available)
  | label other =>
    have same : other.1 = receipt.1 := by cases available; rfl
    rcases receipt with ⟨receipt, root⟩
    rcases other with ⟨other, node⟩
    change other = receipt at same
    subst other
    have edge : (labels.app point receipt).1.edge point root node := by
      cases available with | label _ edge => exact edge
    exact ⟨⟨node, edge⟩, ⟨rfl⟩⟩
  | argument receipt => exact False.elim (by cases available)
  | pair left right => exact False.elim (by cases available)
  | left node => exact False.elim (by cases available)
  | right node => exact False.elim (by cases available)

def labelComparison (point : D) (receipt : (states).obj point) :
    Equal (labels.app point receipt)
      (value branches labels arguments successor (labelRoot branches labels arguments point receipt)) :=
  ContextualGraphNaturalBodyEmbedding.rootComparison labels (diagram branches labels arguments successor)
    (labelEmbedding branches labels arguments successor) (labelForth branches labels arguments successor)
    (labelBack branches labels arguments successor) point receipt

def argumentEmbedding : NaturalHom (total (ContextualGraphNaturalBodyEmbedding.bodyNodes arguments))
    (diagram branches labels arguments successor).nodes where
  app _ receipt := .argument receipt
  naturality _ _ := rfl

theorem argumentForth : ContextualGraphNaturalBodyEmbedding.Forth arguments
    (diagram branches labels arguments successor) (argumentEmbedding branches labels arguments successor) :=
  fun _ receipt child => Edge.argument receipt.1 child.property

def argumentBack : ContextualGraphNaturalBodyEmbedding.Back arguments
    (diagram branches labels arguments successor) (argumentEmbedding branches labels arguments successor) := by
  intro point receipt child
  rcases child with ⟨node, available⟩
  cases node with
  | state state => exact False.elim (by cases available)
  | collection state => exact False.elim (by cases available)
  | branch receipt => exact False.elim (by cases available)
  | label receipt => exact False.elim (by cases available)
  | argument other =>
    have same : other.1 = receipt.1 := by cases available; rfl
    rcases receipt with ⟨receipt, root⟩
    rcases other with ⟨other, node⟩
    change other = receipt at same
    subst other
    have edge : (arguments.app point receipt).1.edge point root node := by
      cases available with | argument _ edge => exact edge
    exact ⟨⟨node, edge⟩, ⟨rfl⟩⟩
  | pair left right => exact False.elim (by cases available)
  | left node => exact False.elim (by cases available)
  | right node => exact False.elim (by cases available)

def argumentComparison (point : D) (receipt : (total branches).obj point) :
    Equal (arguments.app point receipt)
      (value branches labels arguments successor (argumentRoot branches labels arguments point receipt)) :=
  ContextualGraphNaturalBodyEmbedding.rootComparison arguments (diagram branches labels arguments successor)
    (argumentEmbedding branches labels arguments successor) (argumentForth branches labels arguments successor)
    (argumentBack branches labels arguments successor) point receipt

def nodeReading : NaturalHom (nodes branches labels arguments) (values D) where
  app _ := value branches labels arguments successor
  naturality _ _ := rfl

def leftEmbedding : NaturalHom
    (total (ContextualGraphNaturalBodyEmbedding.bodyNodes (nodeReading branches labels arguments successor)))
    (diagram branches labels arguments successor).nodes where
  app _ receipt := .left receipt.2
  naturality _ _ := rfl

theorem leftForth : ContextualGraphNaturalBodyEmbedding.Forth (nodeReading branches labels arguments successor)
    (diagram branches labels arguments successor) (leftEmbedding branches labels arguments successor) :=
  fun _ _ child => Edge.left child.property

def leftBack : ContextualGraphNaturalBodyEmbedding.Back (nodeReading branches labels arguments successor)
    (diagram branches labels arguments successor) (leftEmbedding branches labels arguments successor) := by
  intro point receipt child
  rcases child with ⟨node, available⟩
  cases node with
  | state state => exact False.elim (by cases available)
  | collection state => exact False.elim (by cases available)
  | branch receipt => exact False.elim (by cases available)
  | label receipt => exact False.elim (by cases available)
  | argument receipt => exact False.elim (by cases available)
  | pair left right => exact False.elim (by cases available)
  | left node =>
    have edge : Edge branches labels arguments successor point receipt.2 node := by
      cases available with | left edge => exact edge
    exact ⟨⟨node, edge⟩, ⟨rfl⟩⟩
  | right node => exact False.elim (by cases available)

def leftComparison (point : D) (node : Node branches labels arguments point) :
    Equal (value branches labels arguments successor node) (value branches labels arguments successor (.left node)) :=
  ContextualGraphNaturalBodyEmbedding.rootComparison (nodeReading branches labels arguments successor)
    (diagram branches labels arguments successor) (leftEmbedding branches labels arguments successor)
    (leftForth branches labels arguments successor) (leftBack branches labels arguments successor) point node

def rightEmbedding : NaturalHom
    (total (ContextualGraphNaturalBodyEmbedding.bodyNodes (nodeReading branches labels arguments successor)))
    (diagram branches labels arguments successor).nodes where
  app _ receipt := .right receipt.2
  naturality _ _ := rfl

theorem rightForth : ContextualGraphNaturalBodyEmbedding.Forth (nodeReading branches labels arguments successor)
    (diagram branches labels arguments successor) (rightEmbedding branches labels arguments successor) :=
  fun _ _ child => Edge.right child.property

def rightBack : ContextualGraphNaturalBodyEmbedding.Back (nodeReading branches labels arguments successor)
    (diagram branches labels arguments successor) (rightEmbedding branches labels arguments successor) := by
  intro point receipt child
  rcases child with ⟨node, available⟩
  cases node with
  | state state => exact False.elim (by cases available)
  | collection state => exact False.elim (by cases available)
  | branch receipt => exact False.elim (by cases available)
  | label receipt => exact False.elim (by cases available)
  | argument receipt => exact False.elim (by cases available)
  | pair left right => exact False.elim (by cases available)
  | left node => exact False.elim (by cases available)
  | right node =>
    have edge : Edge branches labels arguments successor point receipt.2 node := by
      cases available with | right edge => exact edge
    exact ⟨⟨node, edge⟩, ⟨rfl⟩⟩

def rightComparison (point : D) (node : Node branches labels arguments point) :
    Equal (value branches labels arguments successor node) (value branches labels arguments successor (.right node)) :=
  ContextualGraphNaturalBodyEmbedding.rootComparison (nodeReading branches labels arguments successor)
    (diagram branches labels arguments successor) (rightEmbedding branches labels arguments successor)
    (rightForth branches labels arguments successor) (rightBack branches labels arguments successor) point node

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutComponents
