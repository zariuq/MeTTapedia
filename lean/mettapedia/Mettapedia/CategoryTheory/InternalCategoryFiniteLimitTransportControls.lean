import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportMaps
import Mettapedia.CategoryTheory.InternalCategoryControls

/-!
# Evaluation preserves complete paths and nonidentity internal maps

Evaluation at a context transports the category of retained occurrences.
Its earned composition retains both supplied events. A nonidentity map
changes endpoint values and occurrence identifiers. Context changes which
identify endpoint values still retain the entire occurrence list.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalCategoryControls

abbrev evaluate : (Stage ⥤ Type) ⥤ Type := (evaluation Stage Type).obj stage
abbrev original := InternalCategoryPathDiagram.category graph
abbrev transported := InternalCategoryFiniteLimitTransport.category evaluate original

def first : Nat ⟶ transported.edge := evaluate.map InternalCategoryControls.first
def second : Nat ⟶ transported.edge := evaluate.map InternalCategoryControls.second

theorem matching : first ≫ transported.target = second ≫ transported.source :=
  InternalCategoryFiniteLimitTransport.mapped_matching evaluate original _ _ InternalCategoryControls.matching

def composed : Nat ⟶ transported.edge := transported.compose first second matching

theorem complete_composed : composed = evaluate.map InternalCategoryControls.composed :=
  InternalCategoryFiniteLimitTransport.category_compose_read evaluate original _ _ InternalCategoryControls.matching

theorem complete_occurrences (number : Nat) : readout (composed number) = [7, 9] :=
  (congrArg (fun arrow : Nat ⟶ transported.edge => readout (arrow number)) complete_composed).trans
    (InternalCategoryControls.complete_composition_readout number)

theorem complete_source (number : Nat) : transported.source (composed number) = number :=
  (congrArg (fun arrow : Nat ⟶ transported.edge => transported.source (arrow number)) complete_composed).trans
    (InternalCategoryControls.complete_source_readout number)

theorem complete_target (number : Nat) : transported.target (composed number) = 3 * number :=
  (congrArg (fun arrow : Nat ⟶ transported.edge => transported.target (arrow number)) complete_composed).trans
    (InternalCategoryControls.complete_target_readout number)

def doubled : InternalCategory.Hom transported transported :=
  InternalCategoryFiniteLimitTransportMaps.map evaluate
    (InternalCategoryPathMaps.internalFunctor doubling)

theorem complete_nonidentity_image :
    doubled.edge (InternalCategoryPathDiagram.edge graph stage (7, 1, 2)) =
      InternalCategoryPathDiagram.edge graph stage (107, 2, 4) :=
  InternalCategoryControls.actual_nonidentity_edge_image

theorem changed_occurrences :
    readout (doubled.edge (InternalCategoryPathDiagram.edge graph stage (7, 1, 2))) = [107] :=
  congrArg readout complete_nonidentity_image

theorem transported_map_preserves_composition :
    composed ≫ doubled.edge = transported.compose (first ≫ doubled.edge) (second ≫ doubled.edge)
      (by rw [Category.assoc, doubled.target, ← Category.assoc, matching,
        Category.assoc, ← doubled.source, ← Category.assoc]) :=
  doubled.compose_readout first second matching

theorem equal_endpoints_do_not_recover_occurrences :
    ¬ ∃ decode : Nat × Nat → List Nat,
      ∀ path : transported.edge,
        decode (transported.source path, transported.target path) = readout path :=
  InternalCategoryControls.no_endpoint_origin_decoder

theorem unit_does_not_replace_an_occurrence :
    InternalCategoryPathDiagram.edge graph stage (7, 1, 1) ≠ transported.unit (1 : Nat) :=
  InternalCategoryControls.singleton_is_not_identity

theorem nonmatching_pair_remains_excluded :
    transported.target (InternalCategoryPathDiagram.edge graph stage (7, 1, 2)) ≠
      transported.source (InternalCategoryPathDiagram.edge graph stage (9, 4, 5)) :=
  InternalCategoryControls.nonmatching_edges_do_not_compose

theorem endpoint_collisions_retain_occurrences :
    original.edge.map (show stage ⟶ stage from (0 : Nat))
      (InternalCategoryPathDiagram.edge graph stage (7, 1, 2)) =
        InternalCategoryPathDiagram.edge graph stage (7, 0, 0) :=
  InternalCategoryControls.zero_context_change_keeps_origins

end Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportControls
