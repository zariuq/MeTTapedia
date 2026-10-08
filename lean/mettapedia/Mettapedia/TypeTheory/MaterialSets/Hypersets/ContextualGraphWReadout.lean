import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphWBranchSpan
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadout

/-!
# Constructed material readings of hereditary future W trees

Labels and dependent positions have declared natural material readings.
The reading of trees is then constructed from their actual root labels,
current branches and recursively reached children. It retains all future
contexts through the hereditary W action. No material tree-reading or
closure operator is supplied as construction data.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphWReadout

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualWTypes
universe u
variable {D : Type u} [Category.{u} D]
variable (shape : D ⥤ Type u) (position : shape.Elements ⥤ Type u)
variable (shapeReading : NaturalHom shape (values D))
variable (positionReading : NaturalHom (total position) (values D))

def labels : NaturalHom (family shape position) (values D) :=
  (ContextualGraphWBranchSpan.labelMap shape position).comp shapeReading

def argumentTarget : NaturalHom (total (ContextualGraphWBranchSpan.branches shape position))
    (total position) where
  app _ receipt := ⟨ContextualGraphWBranchSpan.label shape position receipt.1, receipt.2⟩
  naturality _ receipt := by
    rcases receipt with ⟨tree, branch⟩
    rcases tree with ⟨tree, natural⟩
    cases tree
    rfl

def arguments : NaturalHom (total (ContextualGraphWBranchSpan.branches shape position)) (values D) :=
  (argumentTarget shape position).comp positionReading

def reading : NaturalHom (family shape position) (values D) :=
  ContextualGraphPolynomialReadoutNodes.reading (ContextualGraphWBranchSpan.branches shape position)
    (labels shape position shapeReading) (arguments shape position positionReading)
    (ContextualGraphWBranchSpan.childMap shape position)

def branchReading : NaturalHom (total (ContextualGraphWBranchSpan.branches shape position)) (values D) :=
  ContextualGraphPolynomialReadout.branchReading (ContextualGraphWBranchSpan.branches shape position)
    (labels shape position shapeReading) (arguments shape position positionReading)
    (ContextualGraphWBranchSpan.childMap shape position)

def branchCollection : NaturalHom (family shape position) (values D) :=
  ContextualGraphPolynomialReadout.collectionReading (ContextualGraphWBranchSpan.branches shape position)
    (labels shape position shapeReading) (arguments shape position positionReading)
    (ContextualGraphWBranchSpan.childMap shape position)

/-- The branching readout exposes the declared argument and recursively
constructed child reading, retaining the actual branch receipt. -/
theorem branch_value (point : D) (tree : (family shape position).obj point)
    (branch : (ContextualGraphWBranchSpan.branches shape position).obj ⟨point, tree⟩) :
    (branchReading shape position shapeReading positionReading).app point ⟨tree, branch⟩ =
      ContextualGraphOrderedPairs.orderedPair
        (positionReading.app point ⟨ContextualGraphWBranchSpan.label shape position tree, branch⟩)
        ((reading shape position shapeReading positionReading).app point
          (ContextualGraphWBranchSpan.child shape position tree branch)) := rfl

def unfold {point : D} (tree : (family shape position).obj point) :
    Equal ((reading shape position shapeReading positionReading).app point tree)
      (ContextualGraphOrderedPairs.orderedPair
        (shapeReading.app point (ContextualGraphWBranchSpan.label shape position tree))
        ((branchCollection shape position shapeReading positionReading).app point tree)) :=
  ContextualGraphPolynomialReadout.unfold (ContextualGraphWBranchSpan.branches shape position)
    (labels shape position shapeReading) (arguments shape position positionReading)
    (ContextualGraphWBranchSpan.childMap shape position) tree

def constructorComparison {point : D} (label : shape.obj point)
    (children : Branches shape position (family shape position) label) :
    Equal ((reading shape position shapeReading positionReading).app point
      ((treeAlgebra shape position).make point label children))
      (ContextualGraphOrderedPairs.orderedPair (shapeReading.app point label)
        ((branchCollection shape position shapeReading positionReading).app point
          ((treeAlgebra shape position).make point label children))) :=
  unfold shape position shapeReading positionReading ((treeAlgebra shape position).make point label children)

theorem constructor_branch {point : D} (label : shape.obj point)
    (children : Branches shape position (family shape position) label)
    (branch : position.obj ⟨point, label⟩) :
    ContextualGraphWBranchSpan.child shape position
      ((treeAlgebra shape position).make point label children) branch =
        children.app point (𝟙 point) (ContextualGraphWBranchSpan.rootPosition shape position label branch) :=
  Subtype.ext rfl

def reflectLabel {point : D} {first second : (family shape position).obj point}
    (same : Equal ((reading shape position shapeReading positionReading).app point first)
      ((reading shape position shapeReading positionReading).app point second)) :
    Equal (shapeReading.app point (ContextualGraphWBranchSpan.label shape position first))
      (shapeReading.app point (ContextualGraphWBranchSpan.label shape position second)) :=
  ContextualGraphPolynomialReadout.reflectLabel (ContextualGraphWBranchSpan.branches shape position)
    (labels shape position shapeReading) (arguments shape position positionReading)
    (ContextualGraphWBranchSpan.childMap shape position) same

/-- Complete native sections induce complete material readings. -/
def sectionReading (trees : (family shape position).sections) : (values D).sections :=
  (reading shape position shapeReading positionReading).mapSection trees

theorem section_reading_commutes (trees : (family shape position).sections)
    {first second : D} (arrival : first ⟶ second) :
    move D arrival ((sectionReading shape position shapeReading positionReading trees).val first) =
      (sectionReading shape position shapeReading positionReading trees).val second :=
  (sectionReading shape position shapeReading positionReading trees).property arrival

section Fold
variable {target : D ⥤ Type u} (algebra : Algebra shape position target)
variable (targetReading : NaturalHom target (values D))

/-- A native fold is observed through the declared result reading. This
makes no claim that every fold descends through material tree equality. -/
noncomputable def foldedReading : NaturalHom (family shape position) (values D) :=
  (NaturalHom.ofNatTrans (foldMap shape position algebra)).comp targetReading

theorem folded_constructor {point : D} (label : shape.obj point)
    (children : Branches shape position (family shape position) label) :
    (foldedReading shape position algebra targetReading).app point
      ((treeAlgebra shape position).make point label children) =
        targetReading.app point
          (algebra.make point label (children.map (foldMap shape position algebra))) :=
  congrArg (targetReading.app point) (fold_beta shape position algebra label children)

theorem fold_whole_section (trees : (family shape position).sections) :
    (foldedReading shape position algebra targetReading).mapSection trees =
      targetReading.mapSection ((NaturalHom.ofNatTrans (foldMap shape position algebra)).mapSection trees) := by
  apply Subtype.ext
  rfl

end Fold

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphWReadout
