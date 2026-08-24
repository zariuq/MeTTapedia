import Mettapedia.Languages.MeTTa.Prime.PrimeImplementationPolicyTransport
import Mettapedia.Languages.MeTTa.Prime.NativeTypedMetamathPolicyNIKSelection

/-!
# Implementation-policy transport for native Metamath assertion lookup

The prepared Metamath assertion path already has two independently checked
descriptions:

* an abstract Prime implementation model compiles one exact authored source
  occurrence to an immutable assertion index; and
* a maximal-native policy request selects prepared lookup while retaining
  exact ordered observations and occurrence counts.

This module proves that the descriptions commute.  The compiled artifact trace
maps to exactly the receipt returned by the strongest selected lookup, and the
selected policy family pulls back through the implementation model at the same
complete optimization key.  Current execution reuses the retained policy
runner; staleness leaves exact raw fallback.

The negative controls keep recognition honest.  Duplicate source labels cannot
construct the transported selection.  Conversely, every artifact trace has a
prepared face, so a fresh image-specific recognizer could expose that constant
policy; ordinary transport deliberately does not mint the capability.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.NativeTypedMetamathImplementationPolicyTransport

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCapabilitySelection
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCurrentSelection
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyTransport
open Mettapedia.Languages.MeTTa.Prime.NativeTypedMetamathAssertionOptimization
open Mettapedia.Languages.MeTTa.Prime.NativeTypedMetamathPolicyNIKSelection
open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationImplementationModel
open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationNIKBridge
open Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferencePreparedAssertionCompilation

private theorem lookupReceipt_eq_of_fields
    (first second : LookupReceipt)
    (queries_eq : first.queries = second.queries)
    (observations_eq : first.observations = second.observations)
    (face_eq : first.face = second.face) :
    first = second := by
  cases first
  cases second
  simp_all

/-! ## The compiled artifact as a policy state -/

/-- Forget only the physical assertion-index representation.  Query
occurrences, their ordered observations, and the fact that this state came
from the prepared implementation remain explicit. -/
def artifactTraceReceipt
    (projection : PrefixProjection) (queries : List String) (revision : Nat) :
    ExecutionTrace
        (indexedTarget spec (candidate projection queries revision)).operational →
      LookupReceipt :=
  fun trace =>
    { queries := trace.1.queries
      observations := runArtifact trace.1
      face := .preparedIndex }

/-- The existing result-only policy catalog viewed on complete compiled
artifact traces.  Its declared support and executable runners are retained
unchanged. -/
def artifactCatalog
    (projection : PrefixProjection) (queries : List String) (revision : Nat) :=
  PolicyReadoutCatalog.pullbackState
    (artifactTraceReceipt projection queries revision) resultOnlyCatalog

/-- The existing exact native-plus-policy request on the compiled artifact
state.  Candidate membership and the native capability order are unchanged. -/
def artifactPolicyRequest
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :=
  PolicyCapabilityRequest.pullbackState
    (artifactTraceReceipt projection queries revision)
    (policyRequest projection valid)

/-- Prepared lookup remains genuinely strongest after moving policy state to
the compiled-artifact trace. -/
def artifactStrongestPolicyLookup
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :
    (artifactPolicyRequest projection queries revision valid)
      |>.toCapabilityRequest.StrongestNativeCalculusPrinciple :=
  PolicyCapabilityRequest.pullbackStrongestSelection
    (artifactTraceReceipt projection queries revision)
    (policyRequest projection valid) (strongestPolicyLookup projection valid)

@[simp] theorem artifactStrongestPolicyLookup_is_prepared
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :
    (artifactStrongestPolicyLookup projection queries revision valid).1 =
      preparedIndex :=
  rfl

/-! ## Pull the strongest request through the implementation model -/

/-- The exact strongest request as seen from authored source traces. -/
def sourcePolicyRequest
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :=
  Mettapedia.Languages.MeTTa.Prime.PrimeImplementationPolicyTransport.AdmittedExecutionModel.pullbackPolicyRequest
    (implementationModel projection queries revision valid)
    (artifactPolicyRequest projection queries revision valid)

/-- The strongest selected native calculus transports without rerunning the
selector or changing the exact candidate fibre. -/
def sourceStrongestPolicyLookup
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :
    (sourcePolicyRequest projection queries revision valid)
      |>.toCapabilityRequest.StrongestNativeCalculusPrinciple :=
  Mettapedia.Languages.MeTTa.Prime.PrimeImplementationPolicyTransport.AdmittedExecutionModel.pullbackStrongestPolicySelection
    (implementationModel projection queries revision valid)
    (artifactPolicyRequest projection queries revision valid)
    (artifactStrongestPolicyLookup projection queries revision valid)

@[simp] theorem sourceStrongestPolicyLookup_is_prepared
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :
    (sourceStrongestPolicyLookup projection queries revision valid).1 =
      preparedIndex :=
  rfl

/-- The transported strongest selection retains exactly the original artifact
policy runner; implementation transport inserts no checking or dispatch. -/
@[simp] theorem sourceStrongestPolicyLookup_run
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true)
    (policy : (sourcePolicyRequest projection queries revision valid)
      |>.requestedFamily.Policy)
    (encoded : List (Option AssertionView)) :
    ((sourcePolicyRequest projection queries revision valid).strongestRealization
      (sourceStrongestPolicyLookup projection queries revision valid)).run
        policy encoded =
      ((artifactPolicyRequest projection queries revision valid)
        |>.strongestRealization
          (artifactStrongestPolicyLookup projection queries revision valid)).run
        policy encoded :=
  rfl

/-- Retain the strongest artifact policy realization at the same complete
optimization key used by the implementation model. -/
def artifactSelectedAt
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :
    SelectedPolicyAdmissionAt
      (artifactPolicyRequest projection queries revision valid)
      (keyDependencies (SourceProgram String AssertionView))
      (candidate projection queries revision).key :=
  SelectedPolicyAdmissionAt.ofStrongest
    (artifactPolicyRequest projection queries revision valid)
    (artifactStrongestPolicyLookup projection queries revision valid)
    (keyDependencies (SourceProgram String AssertionView))
    (candidate projection queries revision).key

/-- Pull the selected policy admission through the implementation model.
The complete key and retained keyed functions are unchanged. -/
def sourcePolicyAdmission
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :=
  Mettapedia.Languages.MeTTa.Prime.PrimeImplementationPolicyTransport.AdmittedExecutionModel.pullbackPolicyAdmission
    (implementationModel projection queries revision valid)
    (artifactSelectedAt projection queries revision valid).policyAdmission

/-- One implementation-current witness activates the pulled policy family. -/
def sourcePolicyActive
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :=
  Mettapedia.Languages.MeTTa.Prime.PrimeImplementationPolicyTransport.AdmittedExecutionModel.pullbackPolicyActive
    (implementationModel projection queries revision valid)
    (artifactSelectedAt projection queries revision valid).policyAdmission
    (NativeTypedOptimizationImplementationModel.active spec
      (candidate projection queries revision)
      (authority projection queries revision)
      (evidence projection queries valid))

def exactObservationsPolicy
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :
    (artifactPolicyRequest projection queries revision valid)
      |>.requestedFamily.Policy :=
  ⟨.exactObservations, Or.inl rfl⟩

def occurrenceCountPolicy
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :
    (artifactPolicyRequest projection queries revision valid)
      |>.requestedFamily.Policy :=
  ⟨.occurrenceCount, Or.inr rfl⟩

/-- The same policy coordinate, stated in the exact pulled-back family used by
the implementation-level admission. -/
def sourceExactObservationsPolicy
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :
    (PolicyFamily.pullback
      (Mettapedia.Languages.MeTTa.Prime.PrimeImplementationPolicyTransport.AdmittedExecutionModel.traceMap
        (implementationModel projection queries revision valid))
      (artifactPolicyRequest projection queries revision valid).requestedFamily).Policy :=
  ⟨.exactObservations, Or.inl rfl⟩

/-- Occurrence count in the exact pulled-back family. -/
def sourceOccurrenceCountPolicy
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :
    (PolicyFamily.pullback
      (Mettapedia.Languages.MeTTa.Prime.PrimeImplementationPolicyTransport.AdmittedExecutionModel.traceMap
        (implementationModel projection queries revision valid))
      (artifactPolicyRequest projection queries revision valid).requestedFamily).Policy :=
  ⟨.occurrenceCount, Or.inr rfl⟩

private theorem compiledArtifact_observations_eq_source
    (projection : PrefixProjection) (queries : List String)
    (valid : prefixProjectionValid projection = true) :
    runArtifact
        (spec.compile (source projection queries)
          (evidence projection queries valid)) =
      runSource (source projection queries) := by
  have exactness := admitted_records_observe_source projection queries valid
  change
    runArtifact
        (spec.compile (source projection queries)
          (evidence projection queries valid)) =
      runSource (source projection queries) at exactness
  exact exactness

private theorem compiledTrace_observations_eq_source
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :
    runArtifact
        (((implementationModel projection queries revision valid).compileTrace
          (NativeTypedOptimizationImplementationModel.active spec
            (candidate projection queries revision)
            (authority projection queries revision)
            (evidence projection queries valid))
          (preparedSourceTrace projection queries revision valid).sourceTrace).1) =
      runSource (source projection queries) := by
  have compiled :=
    implementation_compiles_prepared_records projection queries revision valid
  have observations := congrArg (fun trace => runArtifact trace.1) compiled
  exact observations.trans
    (compiledArtifact_observations_eq_source projection queries valid)

/-! ## The concrete commuting square -/

/-- The implementation artifact and the maximal-native selected lookup yield
the same complete lookup receipt: query occurrences, ordered observations, and
prepared execution face all agree. -/
theorem compiled_trace_receipt_eq_selected_lookup
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :
    artifactTraceReceipt projection queries revision
        ((implementationModel projection queries revision valid).compileTrace
          (NativeTypedOptimizationImplementationModel.active spec
            (candidate projection queries revision)
            (authority projection queries revision)
            (evidence projection queries valid))
          (preparedSourceTrace projection queries revision valid).sourceTrace) =
      (activeAt projection valid revision).run queries := by
  change
    artifactTraceReceipt projection queries revision
        ((implementationModel projection queries revision valid).compileTrace
          (NativeTypedOptimizationImplementationModel.active spec
            (candidate projection queries revision)
            (authority projection queries revision)
            (evidence projection queries valid))
          ⟨sourceOccurrence projection queries revision,
            sourceOccurrence projection queries revision,
            .refl (sourceOccurrence projection queries revision)⟩) =
      (activeAt projection valid revision).run queries
  rw [implementation_compiles_prepared_records projection queries revision valid]
  apply lookupReceipt_eq_of_fields
  · rfl
  · rw [(current_lookup_is_prepared_and_exact projection valid revision
      queries).2]
    exact compiledArtifact_observations_eq_source projection queries valid
  · rfl

/-- Current exact-observation policy execution after compilation returns the
authored source scan's complete ordered optional-record bag. -/
theorem current_exact_policy_runs_compiled_artifact
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :
    (sourcePolicyActive projection queries revision valid).runKey
        (sourceExactObservationsPolicy projection queries revision valid)
        ((artifactCatalog projection queries revision).readout
          (artifactSelectedAt projection queries revision valid).candidate
          ((implementationModel projection queries revision valid).compileTrace
            (NativeTypedOptimizationImplementationModel.active spec
              (candidate projection queries revision)
              (authority projection queries revision)
              (evidence projection queries valid))
            (preparedSourceTrace projection queries revision valid).sourceTrace)) =
      runSource (source projection queries) := by
  change
    runArtifact
        (((implementationModel projection queries revision valid).compileTrace
          (NativeTypedOptimizationImplementationModel.active spec
            (candidate projection queries revision)
            (authority projection queries revision)
            (evidence projection queries valid))
          (preparedSourceTrace projection queries revision valid).sourceTrace).1) =
      runSource (source projection queries)
  exact compiledTrace_observations_eq_source projection queries revision valid

/-- Occurrence-count policy execution observes every authored query
occurrence, including repetitions and absent labels. -/
theorem current_count_policy_preserves_query_multiplicity
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :
    (sourcePolicyActive projection queries revision valid).runKey
        (sourceOccurrenceCountPolicy projection queries revision valid)
        ((artifactCatalog projection queries revision).readout
          (artifactSelectedAt projection queries revision valid).candidate
          ((implementationModel projection queries revision valid).compileTrace
            (NativeTypedOptimizationImplementationModel.active spec
              (candidate projection queries revision)
              (authority projection queries revision)
              (evidence projection queries valid))
            (preparedSourceTrace projection queries revision valid).sourceTrace)) =
      queries.length := by
  change
    (runArtifact
        (((implementationModel projection queries revision valid).compileTrace
          (NativeTypedOptimizationImplementationModel.active spec
            (candidate projection queries revision)
            (authority projection queries revision)
            (evidence projection queries valid))
          (preparedSourceTrace projection queries revision valid).sourceTrace).1)).length =
      queries.length
  rw [compiledTrace_observations_eq_source projection queries revision valid]
  simp [source, assertionRecordSource, runSource]

/-! ## Staleness and recognition boundaries -/

/-- A changed complete optimization key disables the transported policy and
preserves the exact authored trace for ordinary fallback. -/
theorem changed_revision_refuses_transported_policy_and_preserves_fallback
    (projection : PrefixProjection) (queries : List String) (revision : Nat)
    (valid : prefixProjectionValid projection = true) :
    (¬ (sourcePolicyAdmission projection queries revision valid).Active
        (nextRevisionKey projection queries revision)) ∧
      (implementationModel projection queries revision valid).rawCodec.decode
          (preparedSourceTrace projection queries revision valid).fallback =
        (preparedSourceTrace projection queries revision valid).sourceTrace := by
  have stale :
      (implementationModel projection queries revision valid).StaleAt
        (nextRevisionKey projection queries revision) := by
    intro same
    exact candidate_key_ne_nextRevisionKey projection queries revision
      ((sameDependencies_iff_key_eq
        (candidate projection queries revision).key
        (nextRevisionKey projection queries revision)).1 same)
  exact
    Mettapedia.Languages.MeTTa.Prime.PrimeImplementationPolicyTransport.AdmittedExecutionModel.stale_prevents_pulled_policy_and_preserves_fallback
      (implementationModel projection queries revision valid)
      (artifactSelectedAt projection queries revision valid).policyAdmission
      stale (preparedSourceTrace projection queries revision valid)

/-- On the compiled-artifact image the execution face is constant, so a fresh
image-specific realization can answer the full receipt-policy family from the
same result-only readout. -/
def artifactImageFullPolicyRealization
    (projection : PrefixProjection) (queries : List String) (revision : Nat) :
    (receiptPolicies.pullback
      (artifactTraceReceipt projection queries revision)).ReadoutRealization
        (LookupReceipt.observations ∘
          artifactTraceReceipt projection queries revision) where
  run := fun policy =>
    match policy with
    | .exactObservations => id
    | .occurrenceCount => List.length
    | .executionFace => fun _ => .preparedIndex
  agrees := by
    intro policy trace
    cases policy <;> rfl

/-- The image-specific capability is real, but the transported catalog does
not silently claim it.  Fresh recognition is required to extend the catalog. -/
theorem artifact_image_supports_face_but_transport_does_not_mint_it
    (projection : PrefixProjection) (queries : List String) (revision : Nat) :
    (receiptPolicies.pullback
        (artifactTraceReceipt projection queries revision)).SupportsReadout
          (LookupReceipt.observations ∘
            artifactTraceReceipt projection queries revision) ∧
      ¬ (artifactCatalog projection queries revision).Supports
        preparedIndex .executionFace := by
  constructor
  · exact ⟨artifactImageFullPolicyRealization projection queries revision⟩
  · intro support
    exact support

namespace Examples

open Mettapedia.Languages.Metamath.InferencePreparedAssertionCompilation.Examples

/-- An ambiguous source table cannot construct even the transported strongest
request: implementation transport does not bypass source recognition. -/
theorem duplicate_projection_never_constructs_transported_selection
    (queries : List String) (revision : Nat) :
    ¬ Exists fun valid : prefixProjectionValid duplicateProjection = true =>
      Nonempty
        ((sourcePolicyRequest duplicateProjection queries revision valid)
          |>.toCapabilityRequest.StrongestNativeCalculusPrinciple) := by
  rintro ⟨valid, _selection⟩
  rw [duplicate_projection_refused] at valid
  contradiction

end Examples

#print axioms compiled_trace_receipt_eq_selected_lookup
#print axioms sourceStrongestPolicyLookup_run
#print axioms current_exact_policy_runs_compiled_artifact
#print axioms current_count_policy_preserves_query_multiplicity
#print axioms changed_revision_refuses_transported_policy_and_preserves_fallback
#print axioms artifact_image_supports_face_but_transport_does_not_mint_it
#print axioms Examples.duplicate_projection_never_constructs_transported_selection

end Mettapedia.Languages.MeTTa.Prime.NativeTypedMetamathImplementationPolicyTransport
