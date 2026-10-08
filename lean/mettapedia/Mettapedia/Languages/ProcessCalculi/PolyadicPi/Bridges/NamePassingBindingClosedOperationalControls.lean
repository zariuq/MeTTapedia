import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalInterpretation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemasControls
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperationalCategoryControls

/-!
# Generated evidence with complete functions and changed future bindings

Actual generated firing decoders receive independent complete metadata and
ordinary environments. They recover genuine scope/binary and unary COMM
receipts. The future assay changes an ambient captured name while retaining
both received binder coordinates. Exchanged coordinates and identity-path
substitutes are rejected by actual result and occurrence readings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalInterpretation.Controls

open _root_.CategoryTheory
open Mettapedia.CategoryTheory
open NamePassingCategoricalCompiler NamePassingBindingClosedOperations
open NamePassingBindingClosedOperationalPresentation NamePassingBindingClosedOperationalNativeReadout

attribute [local irreducible] NamePassingCategoricalOperational.betaReaction
  NamePassingCategoricalOperational.fetchFiring

abbrev world := NamePassingCategoricalOperational.Controls.world
abbrev rawFunction := NamePassingCategoricalOperational.Controls.function
abbrev argument := NamePassingCategoricalOperational.Controls.argument
abbrev result := NamePassingCategoricalOperational.Controls.result

def betaSupplied : (domain .beta).obj world :=
  ((argument,PUnit.unit),
    (NamePassingBindingClosedSchemas.Controls.unitMeta.app world rawFunction,PUnit.unit))

def capturedSupplied : (domain .beta).obj world :=
  ((NamePassingCategoricalOperational.Controls.result,PUnit.unit),
    (NamePassingBindingClosedSchemas.Controls.unitMeta.app world
      NamePassingCategoricalOperational.Controls.capturedFunction,PUnit.unit))

def fetchSupplied : (domain .fetch).obj world :=
  ((argument,(NamePassingCategoricalOperational.Controls.stored,PUnit.unit)),PUnit.unit)

private theorem body_unit_read (body : operations.boundBodyObject.obj world) :
    (boundValue operations).app world
      (NamePassingBindingClosedSchemas.Controls.unitMeta.app world body) = body := by
  have full := congrArg (fun arrow => arrow.app world body)
    NamePassingBindingClosedSchemas.Controls.unitMeta_inverse
  exact full

theorem beta_input : betaInput.app world betaSupplied = (rawFunction,argument) := by
  apply Prod.ext
  · exact body_unit_read rawFunction
  · rfl

theorem captured_input : betaInput.app world capturedSupplied =
    (NamePassingCategoricalOperational.Controls.capturedFunction,
      NamePassingCategoricalOperational.Controls.result) := by
  apply Prod.ext
  · exact body_unit_read NamePassingCategoricalOperational.Controls.capturedFunction
  · rfl

theorem fetch_input : fetchInput.app world fetchSupplied =
    (argument,NamePassingCategoricalOperational.Controls.stored) := rfl

def decodedBeta : Option (CategoricalOperationalContinuations.pathEdges.obj world) :=
  (readFire .beta).map (fun arrow =>
    ((CategoricalOperationalContinuations.edgeComparison.inv.app world
      (arrow.app world betaSupplied)).app world (𝟙 world)) result)

def decodedFetch : Option (CategoricalOperationalContinuations.pathEdges.obj world) :=
  (readFire .fetch).map (fun arrow =>
    ((CategoricalOperationalContinuations.edgeComparison.inv.app world
      (arrow.app world fetchSupplied)).app world (𝟙 world)) result)

theorem generated_beta_exact_receipt : decodedBeta = some
    (InternalCategoryPathDiagram.edge CategoricalOperational.graph world
      NamePassingCategoricalOperational.Controls.firing) := by
  unfold decodedBeta
  rw [generated_function]
  change some (((CategoricalOperationalContinuations.edgeComparison.inv.app world
    ((nativeReceipt .beta).app world betaSupplied)).app world (𝟙 world)) result) = _
  rw [beta_future,beta_input]
  rw [NamePassingCategoricalOperational.beta_future,Functor.map_id_apply]
  rfl

theorem generated_fetch_exact_receipt : decodedFetch = some
    (InternalCategoryPathDiagram.edge CategoricalOperational.graph world
      NamePassingCategoricalOperational.Controls.fetchReceipt) := by
  unfold decodedFetch
  rw [generated_function]
  change some (((CategoricalOperationalContinuations.edgeComparison.inv.app world
    ((nativeReceipt .fetch).app world fetchSupplied)).app world (𝟙 world)) result) = _
  rw [fetch_future,fetch_input]
  rw [NamePassingCategoricalOperational.fetch_future,Functor.map_id_apply]
  rfl

theorem generated_beta_complete_target : decodedBeta.map InternalCategoryDiagram.Arrow.target =
    some NamePassingCategoricalOperational.Controls.expected := by
  rw [generated_beta_exact_receipt]
  change some (CategoricalOperational.target.app world NamePassingCategoricalOperational.Controls.firing) = _
  rw [NamePassingCategoricalOperational.Controls.beta_complete_target]

theorem generated_fetch_complete_target : decodedFetch.map InternalCategoryDiagram.Arrow.target =
    some NamePassingCategoricalOperational.Controls.expected := by
  rw [generated_fetch_exact_receipt]
  change some (CategoricalOperational.target.app world NamePassingCategoricalOperational.Controls.fetchReceipt) = _
  rw [NamePassingCategoricalOperational.Controls.fetch_complete_target]

theorem generated_beta_retains_scope_origin :
    decodedBeta.map (fun path => (NamePassingCategoricalOperationalCategory.Controls.inventory
      world path).map (fun event => (NamePassingCategoricalOperational.Controls.origin world event).index.val)) =
        some [4] := by
  rw [generated_beta_exact_receipt]
  simp only [Option.map_some,NamePassingCategoricalOperationalCategory.Controls.one_edge_inventory,
    List.map_cons,List.map_nil,NamePassingCategoricalOperational.Controls.beta_retains_private_scope_occurrence]

theorem generated_fetch_retains_unary_origin :
    decodedFetch.map (fun path => (NamePassingCategoricalOperationalCategory.Controls.inventory
      world path).map (fun event => (NamePassingCategoricalOperational.Controls.origin world event).index.val)) =
        some [0] := by
  rw [generated_fetch_exact_receipt]
  simp only [Option.map_some,NamePassingCategoricalOperationalCategory.Controls.one_edge_inventory,
    List.map_cons,List.map_nil,NamePassingCategoricalOperational.Controls.fetch_retains_unary_occurrence]

def capturedFutureTarget : Option (operations.processes.obj world) :=
  (readFire .beta).map (fun arrow => InternalCategoryDiagram.Arrow.target
    (((CategoricalOperationalContinuations.edgeComparison.inv.app world
      (arrow.app world capturedSupplied)).app world
        (rawChange NamePassingCategoricalOperational.Controls.swap))
          NamePassingCategoricalOperational.Controls.argument))

theorem actual_changed_future_target : capturedFutureTarget = some
    (rawPoint
      (out1 (.var (.succ .zero)) (.var .zero) : Proc NamePassingCategoricalOperational.Controls.context)) := by
  unfold capturedFutureTarget
  rw [generated_function]
  change some (InternalCategoryDiagram.Arrow.target
    (((CategoricalOperationalContinuations.edgeComparison.inv.app world
      ((nativeReceipt .beta).app world capturedSupplied)).app world
        (rawChange NamePassingCategoricalOperational.Controls.swap))
          NamePassingCategoricalOperational.Controls.argument)) = _
  rw [beta_future,captured_input]
  change some (CategoricalOperational.target.app world
    (((NamePassingCategoricalOperational.beta.app world
      (NamePassingCategoricalOperational.Controls.capturedFunction,
        NamePassingCategoricalOperational.Controls.result)).app world
          (rawChange NamePassingCategoricalOperational.Controls.swap))
            NamePassingCategoricalOperational.Controls.argument)) = _
  rw [NamePassingCategoricalOperational.Controls.captured_future_target]

theorem generated_beta_excludes_exchanged_positions :
    decodedBeta.map InternalCategoryDiagram.Arrow.target ≠
      some NamePassingCategoricalOperational.Controls.exchanged := by
  rw [generated_beta_complete_target]
  exact fun same => NamePassingCategoricalOperational.Controls.exchanged_bound_coordinates_change_target
    (Option.some.inj same)

theorem generated_beta_is_one_retained_firing :
    (readFire .beta).map (fun arrow => NamePassingCategoricalOperationalCategory.Controls.length
      world (arrow.app world betaSupplied)) = some 1 := by
  rw [generated_function]
  change some (NamePassingCategoricalOperationalCategory.Controls.length world
    (CategoricalOperationalContinuations.eventInclusion.app world
      (NamePassingCategoricalOperational.beta.app world (betaInput.app world betaSupplied)))) = _
  rw [CategoricalOperationalContinuations.eventInclusion_readout]
  rfl

theorem generated_beta_is_not_identity (program : operations.termObject.obj world) :
    (readFire .beta).map (fun arrow => arrow.app world betaSupplied) ≠
      some (CategoricalOperationalContinuations.category.unit.app world program) := by
  intro same
  have counts := congrArg (Option.map (NamePassingCategoricalOperationalCategory.Controls.length world)) same
  rw [Option.map_map] at counts
  change (readFire .beta).map (fun arrow => NamePassingCategoricalOperationalCategory.Controls.length
    world (arrow.app world betaSupplied)) = some 0 at counts
  rw [generated_beta_is_one_retained_firing] at counts
  change some (1 : Nat) = some 0 at counts
  cases Option.some.inj counts

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalInterpretation.Controls
