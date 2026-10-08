import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperationalCategory
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperationalControls

/-!
# Complete native path composition and receipt controls

Two actual fetch firings compose because the first supplied stored function
is the independently formed source of the second firing. Their path retains
both occurrences. Native identity paths have no occurrences. A separately
constructed constant-return receipt embeds the earlier distinct metadata
supplies; whole endpoint functions do not recover those retained origins.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperationalCategory.Controls

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.CategoryTheory
open Mettapedia.OSLF.Binding
open NamePassingCategoricalCompiler NamePassingCategoricalOperational

abbrev category := CategoricalOperationalContinuations.category

/-- Prepare a first genuine fetch whose answer is the whole second fetch source. -/
def prepared : fetchDomain ⟶ fetchDomain :=
  lift (fst operations.names operations.termObject) fetchSource

def firstPath : fetchDomain ⟶ category.edge := prepared ≫ fetchPath

theorem matching : firstPath ≫ category.target = fetchPath ≫ category.source := by
  rw [firstPath, Category.assoc, fetchPath_target, fetchPath_source]
  exact lift_snd _ _

def sequence : fetchDomain ⟶ category.edge :=
  category.compose firstPath fetchPath matching

@[reassoc] theorem sequence_source : sequence ≫ category.source = prepared ≫ fetchSource := by
  rw [sequence, category.compose_source, firstPath, Category.assoc, fetchPath_source]

@[reassoc] theorem sequence_target : sequence ≫ category.target =
    snd operations.names operations.termObject := by
  rw [sequence, category.compose_target, fetchPath_target]

def length (world : Base) (path : category.edge.obj world) : Nat := path.2.2.length

private theorem compose_length (world : Base)
    (first second : category.edge.obj world)
    (supplied : InternalCategoryDiagram.Arrow.target first =
      InternalCategoryDiagram.Arrow.source second) :
    length world (InternalCategoryDiagram.Arrow.compose first second supplied) =
      length world first + length world second := by
  rcases first with ⟨firstSource,firstTarget,firstArrow⟩
  rcases second with ⟨secondSource,secondTarget,secondArrow⟩
  change firstTarget = secondSource at supplied
  subst secondSource
  dsimp only [length,InternalCategoryDiagram.Arrow.compose]
  simp only [eqToHom_refl,Category.id_comp]
  exact Quiver.Path.length_comp firstArrow secondArrow

theorem fetchPath_length (world : Base) (supplied : fetchDomain.obj world) :
    length world (fetchPath.app world supplied) = 1 := by
  change length world
    (CategoricalOperationalContinuations.eventInclusion.app world (fetch.app world supplied)) = 1
  rw [CategoricalOperationalContinuations.eventInclusion_readout]
  rfl

theorem firstPath_length (world : Base) (supplied : fetchDomain.obj world) :
    length world (firstPath.app world supplied) = 1 :=
  fetchPath_length world (prepared.app world supplied)

theorem sequence_length (world : Base) (supplied : fetchDomain.obj world) :
    length world (sequence.app world supplied) = 2 := by
  change length world ((category.compose firstPath fetchPath matching).app world supplied) = 2
  rw [CategoricalOperationalContinuations.compose_readout,compose_length,
    firstPath_length,fetchPath_length]

theorem identity_length (world : Base) (term : category.vertex.obj world) :
    length world (category.unit.app world term) = 0 := rfl

theorem sequence_is_not_identity (world : Base) (supplied : fetchDomain.obj world)
    (term : category.vertex.obj world) :
    sequence.app world supplied ≠ category.unit.app world term := by
  intro same
  have counts := congrArg (length world) same
  rw [sequence_length,identity_length] at counts
  cases counts

/-- The actual first fetch retains the independently prepared complete body. -/
theorem firstPath_future (world future : Base) (change : world ⟶ future)
    (supplied : fetchDomain.obj world) (result : operations.names.obj future) :
    ((CategoricalOperationalContinuations.edgeComparison.inv.app world
      (firstPath.app world supplied)).app future change result) =
      InternalCategoryPathDiagram.edge CategoricalOperational.graph future
        ((fetch.app world (prepared.app world supplied)).app future change result) :=
  fetchPath_future world future change (prepared.app world supplied) result

theorem sequence_substitution {world future : Base} (change : world ⟶ future)
    (supplied : fetchDomain.obj world) :
    category.edge.map change (sequence.app world supplied) =
      sequence.app future (fetchDomain.map change supplied) :=
  receipt_substitution sequence change supplied

def constantReceipt : events ⟶ operations.names.functorHom events :=
  Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
    (fst events operations.names)

def constantPath : events ⟶ category.edge := includeReceipt constantReceipt

def constantProgram : operations.processes ⟶ operations.termObject :=
  Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
    (fst operations.processes operations.names)

private theorem constant_endpoint (endpoint : events ⟶ operations.processes) :
    constantReceipt ≫ (FunctorToTypes.rightAdj operations.names).map endpoint =
      endpoint ≫ constantProgram := by
  apply complete_abstraction_endpoint (fst events operations.names) endpoint
    (endpoint ≫ constantProgram)
  intro world event result
  change endpoint.app world event =
    (constantProgram.app world (endpoint.app world event)).app world (𝟙 world) result
  exact (NamePassingCategoricalCompiler.abstraction_current
    (fst operations.processes operations.names) world (endpoint.app world event) result).symm

@[reassoc] theorem constantPath_source :
    constantPath ≫ category.source = source ≫ constantProgram :=
  (includeReceipt_source constantReceipt).trans (constant_endpoint source)

@[reassoc] theorem constantPath_target :
    constantPath ≫ category.target = target ≫ constantProgram :=
  (includeReceipt_target constantReceipt).trans (constant_endpoint target)

private def occurrences (world : Base)
    {first last : InternalCategoryPathDiagram.Vertex CategoricalOperational.graph world}
    (path : InternalCategoryPathDiagram.Path CategoricalOperational.graph world first last) :
    List (events.obj world) :=
  match path with
  | .nil => []
  | .cons before event => List.append (α := events.obj world)
      (occurrences world before) (List.cons event.1 [])

def inventory (world : Base) (path : CategoricalOperationalContinuations.pathEdges.obj world) :
    List (events.obj world) := occurrences world path.2.2

theorem one_edge_inventory (world : Base) (event : events.obj world) :
    inventory world (InternalCategoryPathDiagram.edge CategoricalOperational.graph world event) =
      [event] := rfl

/-- The decoded whole path retains the original metadata occurrence. -/
theorem constantPath_readout (world : Base) (event : events.obj world)
    (result : operations.names.obj world) :
    inventory world
      ((CategoricalOperationalContinuations.edgeComparison.inv.app world
        (constantPath.app world event)).app world (𝟙 world) result) = [event] := by
  have read := includeReceipt_future constantReceipt world world (𝟙 world) event result
  have current : (constantReceipt.app world event).app world (𝟙 world) result = event :=
    NamePassingCategoricalCompiler.abstraction_current (fst events operations.names)
      world event result
  exact (congrArg (inventory world) read).trans
    ((congrArg (fun supplied : events.obj world => inventory world
      (InternalCategoryPathDiagram.edge CategoricalOperational.graph world supplied)) current).trans
        (one_edge_inventory world event))

theorem constantPath_injective (world : Base) (result : operations.names.obj world) :
    Function.Injective (constantPath.app world) := by
  intro first second same
  have inventories := congrArg
    (fun path : category.edge.obj world => inventory world
      ((CategoricalOperationalContinuations.edgeComparison.inv.app world path).app world
        (𝟙 world) result)) same
  rw [constantPath_readout,constantPath_readout] at inventories
  exact List.singleton_injective inventories

def originalFirst : events.obj NamePassingCategoricalOperational.Controls.world :=
  NamePassingCategoricalOperational.Controls.alternativeReceipt
    NamePassingCategoricalOperational.Controls.unusedEmpty

def originalSecond : events.obj NamePassingCategoricalOperational.Controls.world :=
  NamePassingCategoricalOperational.Controls.alternativeReceipt
    NamePassingCategoricalOperational.Controls.unusedOffer

private theorem same_constant_endpoints (world : Base) (first second : events.obj world)
    (sourceRead : source.app world first = source.app world second)
    (targetRead : target.app world first = target.app world second) :
    category.source.app world (constantPath.app world first) =
        category.source.app world (constantPath.app world second) ∧
      category.target.app world (constantPath.app world first) =
        category.target.app world (constantPath.app world second) := by
  have readSource (supplied : events.obj world) := congrArg
    (fun map : events ⟶ category.vertex => map.app world supplied) constantPath_source
  have readTarget (supplied : events.obj world) := congrArg
    (fun map : events ⟶ category.vertex => map.app world supplied) constantPath_target
  constructor
  · exact (readSource first).trans
      ((congrArg (constantProgram.app world) sourceRead).trans (readSource second).symm)
  · exact (readTarget first).trans
      ((congrArg (constantProgram.app world) targetRead).trans (readTarget second).symm)

theorem metadata_paths_have_same_whole_endpoints :
    category.source.app NamePassingCategoricalOperational.Controls.world
        (constantPath.app NamePassingCategoricalOperational.Controls.world originalFirst) =
      category.source.app NamePassingCategoricalOperational.Controls.world
        (constantPath.app NamePassingCategoricalOperational.Controls.world originalSecond) ∧
    category.target.app NamePassingCategoricalOperational.Controls.world
        (constantPath.app NamePassingCategoricalOperational.Controls.world originalFirst) =
      category.target.app NamePassingCategoricalOperational.Controls.world
        (constantPath.app NamePassingCategoricalOperational.Controls.world originalSecond) :=
  same_constant_endpoints NamePassingCategoricalOperational.Controls.world originalFirst originalSecond
    NamePassingCategoricalOperational.Controls.unused_metadata_does_not_change_endpoints.1
    NamePassingCategoricalOperational.Controls.unused_metadata_does_not_change_endpoints.2

theorem metadata_paths_are_distinct :
    constantPath.app NamePassingCategoricalOperational.Controls.world originalFirst ≠
      constantPath.app NamePassingCategoricalOperational.Controls.world originalSecond := by
  intro same
  exact NamePassingCategoricalOperational.Controls.unused_metadata_remains_in_complete_receipt
    (constantPath_injective NamePassingCategoricalOperational.Controls.world
      NamePassingCategoricalOperational.Controls.argument same)

theorem no_continuation_endpoint_path_decoder :
    ¬ ∃ decode :
      category.vertex.obj NamePassingCategoricalOperational.Controls.world ×
        category.vertex.obj NamePassingCategoricalOperational.Controls.world →
          category.edge.obj NamePassingCategoricalOperational.Controls.world,
      ∀ path, decode (category.source.app _ path,category.target.app _ path) = path := by
  rintro ⟨decode,correct⟩
  have pairs :
      (category.source.app _ (constantPath.app _ originalFirst),
        category.target.app _ (constantPath.app _ originalFirst)) =
      (category.source.app _ (constantPath.app _ originalSecond),
        category.target.app _ (constantPath.app _ originalSecond)) :=
    Prod.ext metadata_paths_have_same_whole_endpoints.1
      metadata_paths_have_same_whole_endpoints.2
  exact metadata_paths_are_distinct
    ((correct _).symm.trans ((congrArg decode pairs).trans (correct _)))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperationalCategory.Controls
