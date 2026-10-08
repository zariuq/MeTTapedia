import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedClassifyingContract
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedLogicalControls
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentEvidenceControls

/-!
# Classifying generated specifications on real compiler receipts

The source certificate has two dependent variables: a native function and
an independently supplied witness. Its actual classifying image agrees with
the checked finite-value branch. That image passes through the universal
compiler receipt and accompanies a supplied publicly returning rho execution.
The actual source scope retains both positions. A separate origin control
shows that observing the complete semantic value cannot recover a deliberately
forgotten caller origin, even though the two receipts preserve those origins.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedClassifyingControls

open _root_.CategoryTheory
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open Calculi.NativeDependent ExternalPresheafCertificates
open NamePassingDependentEvidence NamePassingDependentRuntimeEvidence
open NamePassingGeneratedLogicalContract NamePassingGeneratedClassifyingContract
open NamePassingGeneratedLogicalControls NamePassingExternalGeneratedControls
open NamePassingEnvironmentControls NamePassingSpineControls
open NamePassingCompilerReadback.Controls
open NamePassingDependentRuntimeControls (startPoint)

noncomputable section

abbrev headers := External.Controls.headers

/-- The finite source telescope is built from this exact supplied tree,
and selection leaves its authored subject and dependent annotation intact. -/
theorem actual_source_scope :
    (External.Contextual.ClassifyingEvidence.sourceContext tree).arity = 2 ∧
      (External.Contextual.ClassifyingEvidence.chosenTerm tree).code = External.Controls.fullBranch 0 ∧
      (External.Contextual.ClassifyingEvidence.chosenType tree).code =
        External.Controls.signature.termResult .fullBranch :=
  ⟨rfl,External.Contextual.ClassifyingEvidence.chosenTerm_code tree,
    External.Contextual.ClassifyingEvidence.chosenType_code tree⟩

theorem actual_source_scope_readout :
    (External.Contextual.SyntacticModel.data headers).evaluateContext
      (External.Contextual.ClassifyingEvidence.sourceScope tree).raw =
        some (External.Contextual.ClassifyingEvidence.sourceScope tree).semantic :=
  External.Contextual.SyntacticModel.scope_context_read headers _

/-- This complete section was constructed from the actual classifying
model map, independently of the supplied semantic branch. -/
theorem classifying_image_is_supplied_branch (input : Nat) :
    (targetInterpretation input).classifyingSection headers tree = pulledBranch :=
  ((targetInterpretation input).classifyingSection_eq_nativeSection headers tree).trans
    (generated_target_section input)

theorem classifying_value_retains_witness (input : Nat) (point : compiledPrograms.Elements) :
    HEq (((targetInterpretation input).classifyingValueSection headers tree).val point)
      (branch.val ((targetInterface input).mapElements.obj point)) := by
  rw [(targetInterpretation input).classifyingValueSection_eq_valueSection]
  exact target_value_is_the_checked_branch input point

/-- The actual universal receipt and the classifying source image retain
the independently supplied witness in its genuinely dependent Fin fibre. -/
theorem universal_image_recovers_witness (input : Nat) (point : sourcePrograms.Elements) :
    (valueReadout (targetInterpretation input)).app (compilerMap.mapElements.obj point)
      ((carry (source (targetInterpretation input)).certificates).app point
        (((source (targetInterpretation input)).certificateSection tree).val point)) =
      ((targetInterpretation input).classifyingSection headers tree).val
        ((targetInterface input).mapElements.obj (compilerMap.mapElements.obj point)) :=
  universal_classifying_value headers (targetInterpretation input) point tree

theorem full_image_has_different_dependent_fibres (point : compiledPrograms.Elements) :
    tupleMotive.decoded.obj ((targetInterface 0).mapElements.obj point) = Fin 1 ∧
      tupleMotive.decoded.obj ((targetInterface 1).mapElements.obj point) = Fin 2 ∧
        (branch.val ((targetInterface 1).mapElements.obj point)).val ≠
          (branch.val ((targetInterface 0).mapElements.obj point)).val :=
  ⟨(target_specification_retains_both_fibres point).1,
    (target_specification_retains_both_fibres point).2,
    erasing_target_witness_changes_the_answer point⟩

/-- One actual environment-fetch/call returns publicly with the source tree,
its origin, the complete classifying image and the Fin witness all retained. -/
theorem actual_return_retains_classifying_image (input : Nat) :
    ∃ final, ∃ actual : ExecutionPath RhoUnaryReadback.Target (process start) final,
      ∃ receipt : RuntimeReceipt (targetInterpretation input) startPoint tree
        (world names) (code start) actual,
      receipt.history.2.tree = tree ∧ receipt.nativeCertificate.val.1 = startPoint.2 ∧
        receipt.specification = ((targetInterpretation input).classifyingSection headers tree).val
          ((targetInterface input).mapElements.obj (compilerMap.mapElements.obj startPoint)) ∧
        HEq receipt.specification
          (branch.val ((targetInterface input).mapElements.obj (compilerMap.mapElements.obj startPoint))) ∧
        (NamePassingValueNative.sourcePredicate names).1 receipt.execution.after ∧
        (RhoUnaryInputObservation.targetPredicate (world names) .zero).1 final := by
  obtain ⟨final,⟨actual⟩,observed⟩ := fetched_function_returns_in_rho
  obtain ⟨receipt,retainedTree,retainedOrigin,image⟩ :=
    retain_classifying_runtime_prefix headers (targetInterpretation input) startPoint tree
      (world names) (code start) (supplied start) actual
  have witness : HEq receipt.specification
      (branch.val ((targetInterface input).mapElements.obj (compilerMap.mapElements.obj startPoint))) := by
    rw [receipt.computed]
    exact target_value_is_the_checked_branch input (compilerMap.mapElements.obj startPoint)
  exact ⟨final,actual,receipt,retainedTree,retainedOrigin,image,witness,
    receipt.public_return_reflected observed,observed⟩

open NamePassingDependentEvidenceControls

/-- This observer intentionally reads the generated native value, omitting
the separate caller-origin coordinate retained by the receipt. -/
def originValueObservation (input : Nat) : insertionFamily.obj sourcePoint →
    (targetInterpretation input).valueFamily.obj (compilerMap.mapElements.obj sourcePoint) :=
  fun _ => ((targetInterpretation input).classifyingValueSection headers tree).val
    (compilerMap.mapElements.obj sourcePoint)

theorem equal_classifying_value_distinct_origins (input : Nat) :
    originValueObservation input immediateOrigin = originValueObservation input renamedOrigin ∧
      (carry insertionFamily).app sourcePoint immediateOrigin ≠
        (carry insertionFamily).app sourcePoint renamedOrigin :=
  ⟨rfl,compiled_certificates_distinct⟩

/-- The exact classifying section supplies no inverse that reconstructs an
origin coordinate deliberately omitted by the semantic-value observer. -/
theorem native_value_cannot_recover_origin (input : Nat) :
    ¬ ∃ recover : (targetInterpretation input).valueFamily.obj (compilerMap.mapElements.obj sourcePoint) →
        (compiledFamily insertionFamily).obj (compilerMap.mapElements.obj sourcePoint),
      recover (originValueObservation input immediateOrigin) =
          (carry insertionFamily).app sourcePoint immediateOrigin ∧
        recover (originValueObservation input renamedOrigin) =
          (carry insertionFamily).app sourcePoint renamedOrigin := by
  rintro ⟨recover,first,second⟩
  exact compiled_certificates_distinct (first.symm.trans second)

end

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedClassifyingControls
