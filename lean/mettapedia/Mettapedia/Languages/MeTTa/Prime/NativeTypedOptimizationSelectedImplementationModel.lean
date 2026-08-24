import Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationCapabilityNIKSelection
import Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationImplementationModel

/-!
# Selected typed optimizations as Prime implementation models

Typed optimization has two independently useful interfaces:

* request-local maximal-native selection chooses an admitted execution face;
* the abstract Prime implementation model retains exact raw fallback and an
  exact runtime receipt around an admitted observed execution cell.

This file proves that the compiled-artifact selection and the implementation
model are coherent views of the same optimization.  Their hot paths emit the
same artifact, their observations agree with the same source occurrence, and
the complete optimization key is the currentness boundary for both.  The
bridge adds no checker, recognizer replay, or second authority.
-/

namespace Mettapedia.Languages.MeTTa.Prime
namespace NativeTypedOptimizationSelectedImplementationModel

open Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
open NativeTypedOptimizationAdmission
open NativeTypedOptimizationNIKBridge
open NativeTypedOptimizationCapabilityNIKSelection
open PrimeAbstractImplementationModel

/-! ## One selected operation and one implementation model -/

/-- Store the unique strongest compiled-artifact realization at the complete
optimization key. -/
def selectedAdmission {Source : Type} (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec) (eligible : Eligibility spec candidate) :=
  admitStrongestAt (family spec candidate eligible)
    (compiledRequest eligible) (compiledSelection eligible)
    (keyDependencies Source) candidate.key

/-- Current activation executes the selected operation directly. -/
def selectedActive {Source : Type} (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec) (eligible : Eligibility spec candidate) :
    (selectedAdmission spec candidate eligible).Active candidate.key :=
  (selectedAdmission spec candidate eligible).activate
    ((keyDependencies Source).sameDependencies_refl candidate.key)

/-- The same eligibility evidence constructs the already-defined abstract
Prime implementation model. -/
def executionModel {Source : Type} (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec) (eligible : Eligibility spec candidate) :=
  NativeTypedOptimizationImplementationModel.model spec candidate
    eligible.authority eligible.shape

/-- The abstract implementation model activates at the identical complete
optimization key. -/
def executionActive {Source : Type} (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec) (eligible : Eligibility spec candidate) :
    (executionModel spec candidate eligible).admission.Active candidate.key :=
  NativeTypedOptimizationImplementationModel.active spec candidate
    eligible.authority eligible.shape

/-- The exact reflexive trace represented by one keyed source occurrence. -/
def sourceTrace {Source : Type} {spec : OptimizationSpec Source}
    {candidate : KeyedCandidate spec} (occurrence : ExactOccurrence candidate) :
    ExecutionTrace
      (NativeTypedOptimizationImplementationModel.indexedSource spec candidate).operational :=
  ⟨occurrence, occurrence, .refl occurrence⟩

/-- The abstract model's emitted receipt is its exact compiled artifact. -/
def implementationReceipt {Source : Type} (spec : OptimizationSpec Source)
    (candidate : KeyedCandidate spec) (eligible : Eligibility spec candidate)
    (occurrence : ExactOccurrence candidate) :
    (executionModel spec candidate eligible).receiptCodec.Representation :=
  let model := executionModel spec candidate eligible
  model.emitReceipt (executionActive spec candidate eligible)
    (model.prepare (sourceTrace occurrence))

/-! ## Cross-interface coherence -/

/-- The selected hot operation and the abstract implementation model emit the
same compiled artifact.  The selected interface merely retains the face tag
around the model's exact receipt. -/
theorem selected_run_eq_model_receipt {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec)
    (eligible : Eligibility spec candidate)
    (occurrence : ExactOccurrence candidate) :
    (selectedActive spec candidate eligible).run occurrence =
      Receipt.compiled (implementationReceipt spec candidate eligible occurrence) := by
  rfl

/-- Both views expose the same target observation, and independent adequacy
identifies that observation with the exact source observation. -/
theorem selected_model_observation_triangle {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec)
    (eligible : Eligibility spec candidate)
    (occurrence : ExactOccurrence candidate) :
    ((selectedActive spec candidate eligible).run occurrence).observe =
        spec.observeArtifact candidate.source
          (implementationReceipt spec candidate eligible occurrence) ∧
      spec.observeArtifact candidate.source
          (implementationReceipt spec candidate eligible occurrence) =
        spec.observeSource candidate.source := by
  constructor
  · rfl
  · exact spec.adequate candidate.source eligible.shape

/-- Compiled selection inherits the source meaning directly from its retained
admitted operation; the implementation bridge introduces no new premise. -/
theorem selected_run_meaning {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec)
    (eligible : Eligibility spec candidate)
    (occurrence : ExactOccurrence candidate) :
    (targetObject spec candidate).Meaning
      ((selectedActive spec candidate eligible).run occurrence) := by
  exact activateStrongest_preserves
    (family spec candidate eligible) (compiledRequest eligible)
    (compiledSelection eligible) (keyDependencies Source)
    candidate.key candidate.key
    ((keyDependencies Source).sameDependencies_refl candidate.key)
    occurrence occurrence.property

/-- Changing any coordinate of the complete optimization key disables both
the selected operation and the abstract model.  The model's exact raw trace
remains available for deoptimization. -/
theorem changed_key_disables_both_and_preserves_fallback {Source : Type}
    (spec : OptimizationSpec Source) (candidate : KeyedCandidate spec)
    (eligible : Eligibility spec candidate)
    (occurrence : ExactOccurrence candidate)
    (currentKey : OptimizationKey Source) (changed : candidate.key ≠ currentKey) :
    (¬ (selectedAdmission spec candidate eligible).Active currentKey) ∧
      (¬ (executionModel spec candidate eligible).admission.Active currentKey) ∧
      (executionModel spec candidate eligible).rawCodec.decode
          ((executionModel spec candidate eligible).prepare
            (sourceTrace occurrence)).fallback =
        sourceTrace occurrence := by
  constructor
  · intro active
    exact changed (active.current ())
  · exact
      NativeTypedOptimizationImplementationModel.changed_key_prevents_activation_and_preserves_fallback
        spec candidate eligible.authority eligible.shape currentKey changed
        ((executionModel spec candidate eligible).prepare (sourceTrace occurrence))

/-! ## Concrete positive and refusing controls -/

namespace MetamathCanary

open NativeTypedOptimizationInstances.MetamathOperationRecordFusion

abbrev eligible :=
  NativeTypedOptimizationCapabilityNIKSelection.MetamathCanary.eligible

/-- Current Metamath record fusion emits exactly the abstract model's compiled
receipt through the request-selected NIK operation. -/
theorem current_selected_receipt_is_model_receipt :
    (selectedActive spec candidate eligible).run
        NativeTypedOptimizationCapabilityNIKSelection.MetamathCanary.input =
      Receipt.compiled
        (implementationReceipt spec candidate eligible
          NativeTypedOptimizationCapabilityNIKSelection.MetamathCanary.input) :=
  selected_run_eq_model_receipt spec candidate eligible
    NativeTypedOptimizationCapabilityNIKSelection.MetamathCanary.input

/-- The known revision change disables both views and preserves the exact
source trace used by raw fallback. -/
theorem changed_revision_disables_both_and_preserves_fallback :
    let input :=
      NativeTypedOptimizationCapabilityNIKSelection.MetamathCanary.input
    let nextKey :=
      NativeTypedOptimizationCapabilityNIKSelection.MetamathCanary.nextKey
    (¬ (selectedAdmission spec candidate eligible).Active nextKey) ∧
      (¬ (executionModel spec candidate eligible).admission.Active nextKey) ∧
      (executionModel spec candidate eligible).rawCodec.decode
          ((executionModel spec candidate eligible).prepare
            (sourceTrace input)).fallback =
        sourceTrace input := by
  exact changed_key_disables_both_and_preserves_fallback
    spec candidate eligible
    NativeTypedOptimizationCapabilityNIKSelection.MetamathCanary.input
    NativeTypedOptimizationCapabilityNIKSelection.MetamathCanary.nextKey
    (by
      intro equal
      have revisionEqual := congrArg
        (fun key => key.revision) equal
      simp [NativeTypedOptimizationCapabilityNIKSelection.MetamathCanary.nextKey,
        candidate, KeyedCandidate.ofAuthority, nativeAuthority, nativeKey]
        at revisionEqual)

end MetamathCanary

namespace StorageCanary

open NativeTypedOptimizationInstances.StorageReuse

/-- A native retained-reference classification still cannot enter the selected
implementation path because its recognizer supplies no non-escaping shape. -/
theorem retained_reference_has_no_selected_implementation :
    ¬ Nonempty (Eligibility spec retainedCandidate) := by
  rintro ⟨eligible⟩
  have recognized := eligible.recognized
  change
    NonEscapingStorage.recognize retainedSource =
      some eligible.shape at recognized
  rw [NativeTypedOptimizationAdmission.Examples.Storage.retained_reference_rejected]
    at recognized
  cases recognized

end StorageCanary

/-! ## Axiom audit -/

#print axioms selected_run_eq_model_receipt
#print axioms selected_model_observation_triangle
#print axioms selected_run_meaning
#print axioms changed_key_disables_both_and_preserves_fallback
#print axioms MetamathCanary.current_selected_receipt_is_model_receipt
#print axioms MetamathCanary.changed_revision_disables_both_and_preserves_fallback
#print axioms StorageCanary.retained_reference_has_no_selected_implementation

end NativeTypedOptimizationSelectedImplementationModel
end Mettapedia.Languages.MeTTa.Prime
