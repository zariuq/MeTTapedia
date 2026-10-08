import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportCoherence
import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportControls

/-!
# Actual future cells on complete operational paths

A scalar context change gives a natural transformation of actual evaluation
functors, hence a complete internal functor through the earned category
action. Nonzero changes act on both endpoints and preserve occurrence
identifiers. The zero change identifies paths with different original
endpoints, despite retaining their origins; a cell needs its own inverse
before complete path recovery is possible.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportCellControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalCategoryFunctorCategory InternalCategoryControls
open InternalCategoryFiniteLimitTransportControls (evaluate original transported)

def futureCell (factor : Nat) : evaluate ⟶ evaluate where
  app diagram := diagram.map (show stage ⟶ stage from factor)
  naturality {_ _} mapping := (mapping.naturality (show stage ⟶ stage from factor)).symm

def wholeCell (factor : Nat) : transported ⟶ transported :=
  InternalCategoryFiniteLimitTransportCells.component (futureCell factor) original

theorem complete_vertex (factor number : Nat) : (wholeCell factor).vertex number = factor * number := rfl

theorem complete_edge (factor : Nat) (supplied : Event) :
    (wholeCell factor).edge (InternalCategoryPathDiagram.edge graph stage supplied) =
      InternalCategoryPathDiagram.edge graph stage
        (supplied.1, factor * supplied.2.1, factor * supplied.2.2) :=
  InternalCategoryPathDiagram.edge_restriction graph (show stage ⟶ stage from factor) supplied

theorem actual_nonidentity_cell : wholeCell 3 ≠ 𝟙 transported := by
  intro same
  have reading := congrArg (fun mapping : transported ⟶ transported => mapping.vertex (1 : Nat)) same
  change (3 : Nat) = 1 at reading
  cases reading

theorem actual_changed_future_path :
    (wholeCell 3).edge (InternalCategoryPathDiagram.edge graph stage (7, 1, 2)) =
      InternalCategoryPathDiagram.edge graph stage (7, 3, 6) := complete_edge 3 _

theorem actual_composed_future_paths :
    (wholeCell 2 ≫ wholeCell 3).edge (InternalCategoryPathDiagram.edge graph stage (7, 1, 2)) =
      InternalCategoryPathDiagram.edge graph stage (7, 6, 12) := by
  change (wholeCell 3).edge ((wholeCell 2).edge
    (InternalCategoryPathDiagram.edge graph stage (7, 1, 2))) = _
  rw [complete_edge, complete_edge]
  rfl

theorem whole_vertical_comparison :
    InternalCategoryFiniteLimitTransportCells.transformation (futureCell 2 ≫ futureCell 3) =
      InternalCategoryFiniteLimitTransportCells.transformation (futureCell 2) ≫
        InternalCategoryFiniteLimitTransportCells.transformation (futureCell 3) :=
  InternalCategoryFiniteLimitTransportCells.whole_vertical_composition _ _

theorem complete_original_paths_are_distinct :
    InternalCategoryPathDiagram.edge graph stage (7, 1, 2) ≠
      InternalCategoryPathDiagram.edge graph stage (7, 2, 4) := by
  intro same
  have endpoints := congrArg InternalCategoryDiagram.Arrow.source same
  change (1 : Nat) = 2 at endpoints
  cases endpoints

theorem zero_cell_identifies_distinct_paths :
    (wholeCell 0).edge (InternalCategoryPathDiagram.edge graph stage (7, 1, 2)) =
      (wholeCell 0).edge (InternalCategoryPathDiagram.edge graph stage (7, 2, 4)) := by
  rw [complete_edge, complete_edge]
  rfl

theorem zero_cell_still_retains_the_origin :
    readout ((wholeCell 0).edge (InternalCategoryPathDiagram.edge graph stage (7, 1, 2))) = [7] := by
  rw [complete_edge]
  rfl

theorem zero_cell_does_not_recover_paths : ¬ Function.Injective (wholeCell 0).edge := by
  intro recovers
  exact complete_original_paths_are_distinct (recovers zero_cell_identifies_distinct_paths)

end Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportCellControls
