import Mettapedia.GSLT.Core.InternalCategoryTheoryAction
import Mettapedia.GSLT.Core.RelativeClosedTheoryModelActionControls
import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportCellControls
import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransportFunctorControls

/-!
# Nonidentity theory transport with complete operational evidence

The independently earned closed ULift theory map changes the representation
of the entire vertex and edge objects. Its genuine invertible natural cell
decodes all supplied paths and distinguishes retained occurrences. Direct
double transport and successive double transport retain both wrappers and
their exact nonidentity operational map. Scalar future changes supply the
separate noninvertible-cell boundary.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.InternalCategoryTheoryActionControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory InternalCategoryFunctorCategory InternalCategoryControls
open InternalCategoryFiniteLimitTransportControls (transported)
open InternalCategoryTheoryAction

abbrev theory := RelativeClosedTheoryModelActionControls.nativeTheory
abbrev raiseTheory := RelativeClosedTheoryModelActionControls.raisedMap
abbrev changedMap := InternalCategoryFiniteLimitTransportFunctorControls.mapped
abbrev path := InternalCategoryPathDiagram.edge graph stage (7, 1, 2)

abbrev raised := (operationalModels.map raiseTheory).toFunctor.obj transported
abbrev raisedMap := (operationalModels.map raiseTheory).toFunctor.map changedMap

abbrev raisedEdgeMap : ULift transported.edge ⟶ ULift transported.edge := raisedMap.edge

theorem full_vertex_representation : raised.vertex = ULift transported.vertex := rfl
theorem full_edge_representation : raised.edge = ULift transported.edge := rfl

theorem whole_raised_map_changes_the_actual_occurrence :
    (raisedEdgeMap (ULift.up path)).down =
      InternalCategoryPathDiagram.edge graph stage (107, 2, 4) :=
  InternalCategoryFiniteLimitTransportFunctorControls.complete_mapped_occurrence

def decodeCell : raiseTheory ⟶ (𝟙 theory : theory ⟶ theory) := uliftFunctorTrivial.hom

abbrev decoded := (operationalModels.map₂ decodeCell).toNatTrans.app transported

abbrev decodedEdge : ULift transported.edge ⟶ transported.edge := decoded.edge

theorem full_cell_decoder (supplied : transported.edge) :
    decodedEdge (ULift.up supplied) = supplied := rfl

theorem decoder_retains_actual_changed_origin :
    readout (decodedEdge (raisedEdgeMap (ULift.up path))) = [107] :=
  congrArg readout whole_raised_map_changes_the_actual_occurrence

theorem decoded_distinct_receipts_remain_distinct :
    decodedEdge (ULift.up (InternalCategoryPathDiagram.edge graph stage (7, 1, 2))) ≠
      decodedEdge (ULift.up (InternalCategoryPathDiagram.edge graph stage (8, 1, 2))) :=
  same_endpoints_distinct_paths

abbrev twice := (operationalModels.map (raiseTheory ≫ raiseTheory)).toFunctor.obj transported
abbrev twiceMap := (operationalModels.map (raiseTheory ≫ raiseTheory)).toFunctor.map
  (changedMap ≫ changedMap)

abbrev twiceEdgeMap : ULift.{0} (ULift.{0} transported.edge) ⟶
    ULift.{0} (ULift.{0} transported.edge) :=
  twiceMap.edge

abbrev compositionEdgeMap : ULift.{0} (ULift.{0} transported.edge) ⟶
    ULift.{0} (ULift.{0} transported.edge) :=
  ((operationalModels.mapComp raiseTheory raiseTheory).hom.toNatTrans.app transported).edge

theorem whole_double_vertex_representation : twice.vertex = ULift (ULift transported.vertex) := rfl
theorem whole_double_edge_representation : twice.edge = ULift (ULift transported.edge) := rfl

theorem whole_double_operational_occurrence :
    ((twiceEdgeMap (ULift.up (ULift.up path))).down).down =
      InternalCategoryPathDiagram.edge graph stage (207, 4, 8) :=
  InternalCategoryFiniteLimitTransportFunctorControls.actual_twice_changed_occurrence

theorem actual_composition_comparison_retains_both_wrappers :
    compositionEdgeMap (ULift.up (ULift.up path)) = ULift.up (ULift.up path) := rfl

theorem entire_operational_map_composition :
    (operationalModels.map raiseTheory).toFunctor.map (changedMap ≫ changedMap) =
      raisedMap ≫ raisedMap := (operationalModels.map raiseTheory).toFunctor.map_comp _ _

theorem noninvertible_future_cell_cannot_recover_paths :
    ¬ Function.Injective (InternalCategoryFiniteLimitTransportCellControls.wholeCell 0).edge :=
  InternalCategoryFiniteLimitTransportCellControls.zero_cell_does_not_recover_paths

end Mettapedia.GSLT.Core.InternalCategoryTheoryActionControls
