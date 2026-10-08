import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalCategory
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperationalCategoryControls

/-!
# Generated native category readings on retained communication paths

The independently generated composition is read at a genuine pair of fetch
paths. It retains both firings, every substitution and the final whole stored
function. Generated endpoint decoders also read the actual beta path. Distinct
metadata paths remain distinct despite equality of both generated endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalCategory.Controls

open _root_.CategoryTheory _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.CategoryTheory
open RelativeClosedSyntax GeneratedCategory Interpretation
open NamePassingCategoricalCompiler NamePassingCategoricalOperational
open NamePassingCategoricalOperationalCategory

def nativeValue {first second : Object (RelativeClosedInternalCategory.Presentation.signature vertex)}
    (code : RawHom first second) : ArrowValue Ambient :=
  ⟨((RelativeClosedInternalCategory.Presentation.nativeInclusion vertex).functor ⋙
      nativeInterpretation.functor).obj first,
    ((RelativeClosedInternalCategory.Presentation.nativeInclusion vertex).functor ⋙
      nativeInterpretation.functor).obj second,
    ((RelativeClosedInternalCategory.Presentation.nativeInclusion vertex).functor ⋙
      nativeInterpretation.functor).map (classOf code)⟩

theorem source_decoder : ArrowValue.readAt (some (nativeValue sourceCode))
    actualCategory.edge (base.obj vertex) = some evidenceOperations.source := by
  change ArrowValue.readAt (some (nativeValue sourceCode)) actualCategory.edge (base.obj vertex) =
    some (actualCategory.source ≫ programComparison.inv)
  unfold nativeValue
  rw [native_value_readout,source_readout,ArrowValue.readAt_supplied]

theorem target_decoder : ArrowValue.readAt (some (nativeValue targetCode))
    actualCategory.edge (base.obj vertex) = some evidenceOperations.target := by
  change ArrowValue.readAt (some (nativeValue targetCode)) actualCategory.edge (base.obj vertex) =
    some (actualCategory.target ≫ programComparison.inv)
  unfold nativeValue
  rw [native_value_readout,target_readout,ArrowValue.readAt_supplied]

theorem unit_decoder : ArrowValue.readAt (some (nativeValue unitCode))
    (base.obj vertex) actualCategory.edge = some evidenceOperations.unit := by
  change ArrowValue.readAt (some (nativeValue unitCode)) (base.obj vertex) actualCategory.edge =
    some (programComparison.hom ≫ actualCategory.unit)
  unfold nativeValue
  rw [native_value_readout,unit_readout,ArrowValue.readAt_supplied]

theorem composition_decoder : ArrowValue.readAt (some (nativeValue compositionCode))
    evidenceOperations.toGraph.composable actualCategory.edge =
      some evidenceOperations.composition := by
  change ArrowValue.readAt (some (nativeValue compositionCode))
    evidenceOperations.toGraph.composable evidenceOperations.edge = some evidenceOperations.composition
  unfold nativeValue
  rw [native_value_readout,composition_readout]
  change ArrowValue.readAt
    (some (⟨evidenceOperations.toGraph.composable,evidenceOperations.edge,evidenceOperations.composition⟩ :
      ArrowValue Ambient)) evidenceOperations.toGraph.composable evidenceOperations.edge =
        some evidenceOperations.composition
  exact ArrowValue.readAt_supplied evidenceOperations.composition

theorem actual_fetch_paths_match :
    NamePassingCategoricalOperationalCategory.Controls.firstPath ≫ evidenceOperations.target =
      fetchPath ≫ evidenceOperations.source := by
  change NamePassingCategoricalOperationalCategory.Controls.firstPath ≫
      (actualCategory.target ≫ programComparison.inv) =
    fetchPath ≫ (actualCategory.source ≫ programComparison.inv)
  rw [← Category.assoc,← Category.assoc,NamePassingCategoricalOperationalCategory.Controls.matching]

/-- Composition formed through the actual generated parser's chosen matching object. -/
def generatedSequence := InternalCategoryPresentedDiagrams.compose evidenceEndpoints
  NamePassingCategoricalOperationalCategory.Controls.firstPath fetchPath actual_fetch_paths_match

theorem generated_sequence_readout : generatedSequence =
    NamePassingCategoricalOperationalCategory.Controls.sequence :=
  complete_composition NamePassingCategoricalOperationalCategory.Controls.firstPath fetchPath
    actual_fetch_paths_match

theorem generated_sequence_retains_two_firings (world : Base) (supplied : fetchDomain.obj world) :
    NamePassingCategoricalOperationalCategory.Controls.length world
      (generatedSequence.app world supplied) = 2 := by
  rw [generated_sequence_readout]
  exact NamePassingCategoricalOperationalCategory.Controls.sequence_length world supplied

theorem generated_sequence_complete_target :
    generatedSequence ≫ actualCategory.target =
      snd operations.names operations.termObject := by
  rw [generated_sequence_readout]
  exact NamePassingCategoricalOperationalCategory.Controls.sequence_target

theorem generated_sequence_substitution {world future : Base} (change : world ⟶ future)
    (supplied : fetchDomain.obj world) :
    actualCategory.edge.map change (generatedSequence.app world supplied) =
      generatedSequence.app future (fetchDomain.map change supplied) :=
  receipt_substitution generatedSequence change supplied

/-- The generated target reads the complete beta function, including every return name. -/
theorem generated_beta_target (world : Base) (supplied : betaDomain.obj world) :
    evidenceOperations.target.app world (betaPath.app world supplied) =
      programComparison.inv.app world (betaTarget.app world supplied) := by
  have whole := congrArg
    (fun map : betaDomain ⟶ actualCategory.vertex => map.app world supplied) betaPath_target
  exact congrArg (programComparison.inv.app world) whole

private theorem generated_endpoint_equality (world : Base)
    (first second : actualCategory.edge.obj world)
    (sourceRead : actualCategory.source.app world first = actualCategory.source.app world second)
    (targetRead : actualCategory.target.app world first = actualCategory.target.app world second) :
    evidenceOperations.source.app world first = evidenceOperations.source.app world second ∧
      evidenceOperations.target.app world first = evidenceOperations.target.app world second :=
  ⟨congrArg (programComparison.inv.app world) sourceRead,
    congrArg (programComparison.inv.app world) targetRead⟩

theorem metadata_paths_have_same_generated_endpoints :
    evidenceOperations.source.app NamePassingCategoricalOperational.Controls.world
        (NamePassingCategoricalOperationalCategory.Controls.constantPath.app _
          NamePassingCategoricalOperationalCategory.Controls.originalFirst) =
      evidenceOperations.source.app NamePassingCategoricalOperational.Controls.world
        (NamePassingCategoricalOperationalCategory.Controls.constantPath.app _
          NamePassingCategoricalOperationalCategory.Controls.originalSecond) ∧
    evidenceOperations.target.app NamePassingCategoricalOperational.Controls.world
        (NamePassingCategoricalOperationalCategory.Controls.constantPath.app _
          NamePassingCategoricalOperationalCategory.Controls.originalFirst) =
      evidenceOperations.target.app NamePassingCategoricalOperational.Controls.world
        (NamePassingCategoricalOperationalCategory.Controls.constantPath.app _
          NamePassingCategoricalOperationalCategory.Controls.originalSecond) :=
  generated_endpoint_equality NamePassingCategoricalOperational.Controls.world _ _
    NamePassingCategoricalOperationalCategory.Controls.metadata_paths_have_same_whole_endpoints.1
    NamePassingCategoricalOperationalCategory.Controls.metadata_paths_have_same_whole_endpoints.2

theorem no_generated_endpoint_path_decoder :
    ¬ ∃ decode :
      (base.obj vertex).obj NamePassingCategoricalOperational.Controls.world ×
        (base.obj vertex).obj NamePassingCategoricalOperational.Controls.world →
          actualCategory.edge.obj NamePassingCategoricalOperational.Controls.world,
      ∀ path, decode (evidenceOperations.source.app _ path,evidenceOperations.target.app _ path) = path := by
  rintro ⟨decode,correct⟩
  have pairs :
      (evidenceOperations.source.app _ (NamePassingCategoricalOperationalCategory.Controls.constantPath.app _
          NamePassingCategoricalOperationalCategory.Controls.originalFirst),
        evidenceOperations.target.app _ (NamePassingCategoricalOperationalCategory.Controls.constantPath.app _
          NamePassingCategoricalOperationalCategory.Controls.originalFirst)) =
      (evidenceOperations.source.app _ (NamePassingCategoricalOperationalCategory.Controls.constantPath.app _
          NamePassingCategoricalOperationalCategory.Controls.originalSecond),
        evidenceOperations.target.app _ (NamePassingCategoricalOperationalCategory.Controls.constantPath.app _
          NamePassingCategoricalOperationalCategory.Controls.originalSecond)) :=
    Prod.ext metadata_paths_have_same_generated_endpoints.1 metadata_paths_have_same_generated_endpoints.2
  exact NamePassingCategoricalOperationalCategory.Controls.metadata_paths_are_distinct
    ((correct _).symm.trans ((congrArg decode pairs).trans (correct _)))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalCategory.Controls
