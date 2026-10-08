import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWTypes
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphDiagrams
import Mettapedia.TypeTheory.ContextualSmallFamilyUniverse

/-!
# The actual current branch span of hereditary future W trees

Every node retains a complete hereditary future tree. The branch family
is pulled from the actual transported root label. Evaluating a current
branch is natural because the tree's hereditary law already compares
all future arrows and positions. This constructs the span from the W
data, rather than assuming a material reading of trees.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphWBranchSpan

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams
open ContextualWTypes
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {D : Type u} [Category.{u} D]
variable (shape : D ⥤ Type u) (position : shape.Elements ⥤ Type u)

def label {point : D} (tree : (family shape position).obj point) : shape.obj point :=
  match tree.val with | .sup root _ => root

def labelMap : NaturalHom (family shape position) shape where
  app _ := label shape position
  naturality _ tree := by
    rcases tree with ⟨tree, natural⟩
    cases tree
    rfl

def branches : (family shape position).Elements ⥤ Type u :=
  ContextualSmallFamilyUniverse.restrict (elementMap (labelMap shape position)) position

def rootPosition {point : D} (root : shape.obj point) (branch : position.obj ⟨point, root⟩) :
    Position shape position root (𝟙 point) :=
  cast (congrArg (fun value => position.obj ⟨point, value⟩) (shape.map_id_apply point root).symm) branch

def child {point : D} (tree : (family shape position).obj point)
    (branch : position.obj ⟨point, label shape position tree⟩) : (family shape position).obj point :=
  match tree with
  | ⟨.sup root children, natural⟩ =>
    ⟨children point (𝟙 point) (rootPosition shape position root branch),
      natural.1 point (𝟙 point) (rootPosition shape position root branch)⟩

theorem child_natural {first second : D} (arrival : first ⟶ second)
    (tree : (family shape position).obj first)
    (branch : (branches shape position).obj ⟨first, tree⟩) :
    (family shape position).map arrival (child shape position tree branch) =
      child shape position ((family shape position).map arrival tree)
        ((branches shape position).map (CategoryOfElements.homMk (F := family shape position)
          ⟨first, tree⟩ ⟨second, (family shape position).map arrival tree⟩ arrival rfl) branch) := by
  rcases tree with ⟨tree, natural⟩
  cases tree with
  | sup root children =>
    change position.obj ⟨first, root⟩ at branch
    apply Subtype.ext
    change ContextualWTypes.restrict shape position arrival
        (children first (𝟙 first) (rootPosition shape position root branch)) =
      children second (arrival ≫ 𝟙 second)
        (compositePosition shape position root arrival (𝟙 second)
          (rootPosition shape position (shape.map arrival root)
            (position.map (argumentMap shape arrival root) branch)))
    refine (natural.2 first second (𝟙 first) arrival (rootPosition shape position root branch)).trans ?_
    apply RawTree.children_eq root children (by simp)
    exact ((ContextualSmallFamilyUniverse.cast_heq _ _).trans
      (position_map_heq shape position arrival (shape.map_id_apply first root)
        (rootPosition shape position root branch) branch (ContextualSmallFamilyUniverse.cast_heq _ _))).trans
      ((ContextualSmallFamilyUniverse.cast_heq _ _).trans (ContextualSmallFamilyUniverse.cast_heq _ _)).symm

def childMap : NaturalHom (total (branches shape position)) (family shape position) where
  app _ receipt := child shape position receipt.1 receipt.2
  naturality arrival receipt := child_natural shape position arrival receipt.1 receipt.2

def source : NaturalHom (total (branches shape position)) (family shape position) :=
  projection (branches shape position)

/-- The graph forgets the root labels and branch receipts as material
observations; the original W family and branch span retain them. -/
def unlabelledDiagram : Diagram D where
  nodes := family shape position
  edge _ first second := ∃ branch : position.obj ⟨_, label shape position first⟩,
    child shape position first branch = second
  edge_transport := by
    intro first second arrival parent descendant available
    rcases available with ⟨branch, rfl⟩
    exact ⟨(branches shape position).map (CategoryOfElements.homMk (F := family shape position)
      ⟨first, parent⟩ ⟨second, (family shape position).map arrival parent⟩ arrival rfl) branch,
      (child_natural shape position arrival parent branch).symm⟩

def unlabelledReading : NaturalHom (family shape position) (values D) where
  app _ tree := ⟨unlabelledDiagram shape position, tree⟩
  naturality _ _ := rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphWBranchSpan
