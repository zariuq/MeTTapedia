import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedRuntime
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeControls

/-!
# Returning compiled prefixes with generated origin certificates

The actual environment-fetch-and-call execution supplies an exact runtime
prefix and public endpoint. Its generated certificate and specification
decode to the retained initial origin. Distinct source histories still
share that initial generated value; current-state certificate transport
is not inferred from the equality of initial values.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedRuntimeControls

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafRepresentableEvidence
open NamePassingLambda NamePassingEnvironmentEquationsNative NamePassingObserverFunctor
open NamePassingDependentEvidence NamePassingDependentRuntimeEvidence NamePassingDependentRuntimeControls
open NamePassingCompilerReadback.Controls NamePassingEnvironmentControls NamePassingSpineControls
open NamePassingGeneratedIndexedEvidence NamePassingGeneratedIndexedRuntime

noncomputable section

theorem fetched_execution_has_complete_generated_origin :
    ∃ final, ∃ actual : ExecutionPath RhoUnaryReadback.Target (process start) final,
      ∃ receipt : Receipt (origins startPoint) (origins (compilerMap.mapElements.obj startPoint))
        (originMap compilerMap startPoint) startPoint (𝟙 startPoint)
        (world names) (code start) actual,
      receiptEquiv (origins startPoint) (compilerMap.mapElements.obj startPoint)
          (generatedCertificate receipt) = (carry (origins startPoint)).app startPoint (𝟙 startPoint) ∧
        NamePassingGeneratedIndexedSpecifications.specificationEquiv
          (origins (compilerMap.mapElements.obj startPoint)) (compilerMap.mapElements.obj startPoint)
          (generatedSpecification receipt) = compilerMap.mapElements.map (𝟙 startPoint) ∧
        (NamePassingValueNative.sourcePredicate names).1 receipt.execution.after ∧
        (RhoUnaryInputObservation.targetPredicate (world names) .zero).1 final := by
  obtain ⟨final, actual, receipt, computed, returned, observed⟩ := fetched_execution_keeps_native_origin
  exact ⟨final, actual, receipt, (generated_certificate_read receipt).trans receipt.carried,
    (generated_specification_read receipt).trans computed, returned, observed⟩

def loopCertificate : NativeReceipt (origins loopPoint) (compilerMap.mapElements.obj loopPoint) :=
  suppliedReceipt (origins loopPoint) loopPoint (𝟙 loopPoint)

theorem repeated_source_history_does_not_change_the_initial_generated_origin :
    noHistory ≠ repeatedHistory ∧
      suppliedReceipt (origins loopPoint) loopPoint noHistory.2 = loopCertificate ∧
      suppliedReceipt (origins loopPoint) loopPoint repeatedHistory.2 = loopCertificate :=
  ⟨histories_distinct_same_witness.1, rfl, rfl⟩

theorem equal_initial_generated_values_do_not_identify_source_histories :
    ¬ ∃ recover : NativeReceipt (origins loopPoint) (compilerMap.mapElements.obj loopPoint) →
        (OperationalReadbackEvidence.historyAndWitness (sourceTheory []) loopingDefinition
          ((origins loopPoint).obj loopPoint)).obj loopingDefinition,
      recover loopCertificate = noHistory ∧ recover loopCertificate = repeatedHistory := by
  rintro ⟨_, first, second⟩
  exact histories_distinct_same_witness.1 (first.symm.trans second)

end

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedRuntimeControls
