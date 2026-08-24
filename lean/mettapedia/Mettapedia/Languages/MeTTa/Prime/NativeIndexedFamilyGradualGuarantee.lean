import Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentGuarantee
import Mettapedia.Languages.MeTTa.Prime.NativeIndexedFamilyConstructionNIKSelection

/-!
# The gradual-dependent instance for constructional indexed families

Constructional indexed-family evidence is displayed over the unchanged raw
source request.  Exact evidence retains the judgment index, both typed states,
the proof-relevant constructed step, and an equality identifying its erasure
with that raw request.  Suspension and local refutation therefore need no
second operational semantics: both return the same request to the ordinary
fallback branch.

The existing constructional NIK operation realizes exact states without a
checker or certificate.  Revision invalidation forgets only the optional
construction witness, after which the retained raw request falls back.  This
is the indexed-family instance of Prime's generic lazy gradual-dependent law;
it neither assumes uniform preservation of arbitrary raw equations nor creates
a new plan hierarchy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime
namespace NativeIndexedFamilyGradualGuarantee

open Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability
open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State
open Mettapedia.Languages.MeTTa.Prime.NativeIndexedFamilyConstructionNIKSelection
open Mettapedia.Languages.MeTTa.PureKernel.Universe
open Mettapedia.Languages.MeTTa.PureKernel.Universe.AuthoredIndexedFamilyNativeKernel
open Mettapedia.Languages.MeTTa.PureKernel.Universe.AuthoredIndexedFamilyPresentation
open Mettapedia.Languages.MeTTa.PureKernel.Universe.AuthoredIndexedFamilyTypedConversion
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.Declaration
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.Declaration.ComputationAuthority

noncomputable section

/-! ## Construction evidence displayed over raw requests -/

/-- A constructional witness whose erasure is one exact raw source request.
The equality is part of the evidence so occurrence identity, context, type,
and authored provenance cannot drift when the optional capability is cached. -/
structure ConstructedEvidence {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented)
    (request : RawSourceRequest presented) where
  index : TypingIndex Tower.Head
  source : NativeIndexedState presented index
  target : NativeIndexedState presented index
  step : TypedNativePresentation.ConstructedStep typed source target
  request_eq : RawSourceRequest.ofConstructed step = request

namespace ConstructedEvidence

/-- Every intrinsically constructed step supplies exact evidence over its own
raw erasure. -/
def ofStep {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {index : TypingIndex Tower.Head}
    {source target : NativeIndexedState presented index}
    (step : TypedNativePresentation.ConstructedStep typed source target) :
    ConstructedEvidence typed (RawSourceRequest.ofConstructed step) where
  index := index
  source := source
  target := target
  step := step
  request_eq := rfl

/-- Exact evidence enters the existing constructional input face directly. -/
def input {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {request : RawSourceRequest presented}
    (evidence : ConstructedEvidence typed request) : Input typed :=
  .constructed evidence.step

@[simp] theorem input_request {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {request : RawSourceRequest presented}
    (evidence : ConstructedEvidence typed request) :
    evidence.input.request = request :=
  evidence.request_eq

end ConstructedEvidence

/-- Prime's generic gradual fibre specialized to constructional indexed-family
steps.  Raw semantics is the complete source request; exactness is precisely a
construction witness erasing to that request. -/
def constructionFibre {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented) : Fibre where
  Raw := RawSourceRequest presented
  Exact := ConstructedEvidence typed

/-- Interpret a gradual state in the existing shared request language.  Only
exact evidence selects the constructed face.  Suspension or local refutation
retains the raw request for fallback; refutation is not semantic rejection. -/
def inputOfState {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {request : RawSourceRequest presented} :
    State (constructionFibre typed) request → Input typed
  | .suspended => .raw request
  | .exact evidence => evidence.input
  | .refuted _ => .raw request

/-- Every gradual state has exactly the same raw request after interpretation.
Adding or invalidating construction evidence cannot change the source term,
context, type, or authored occurrence. -/
theorem inputOfState_request {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {request : RawSourceRequest presented}
    (state : State (constructionFibre typed) request) :
    (inputOfState state).request = request := by
  cases state with
  | suspended => rfl
  | exact evidence => exact evidence.input_request
  | refuted blame => rfl

/-- Run a gradual family state through the already-proved constructional NIK
operation.  This is an adapter, not a second evaluator. -/
def runState {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented)
    {request : RawSourceRequest presented}
    (state : State (constructionFibre typed) request) : Receipt typed :=
  (constructionalOperation typed).run (inputOfState state)

@[simp] theorem runState_source_request {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {request : RawSourceRequest presented}
    (state : State (constructionFibre typed) request) :
    (runState typed state).source.request = request :=
  by
    cases state with
    | suspended => rfl
    | exact evidence => exact evidence.request_eq
    | refuted blame => rfl

theorem runState_valid {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {request : RawSourceRequest presented}
    (state : State (constructionFibre typed) request) :
    (runState typed state).Valid :=
  (runState typed state).valid

/-! ## The exact gradual law -/

/-- Exact construction evidence selects the native no-replay result. -/
theorem run_exact_is_realized {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {request : RawSourceRequest presented}
    (evidence : ConstructedEvidence typed request) :
    Outcome.IsRealized
      (runState typed
        (.exact evidence : State (constructionFibre typed) request)).outcome := by
  change Outcome.IsRealized
    ((constructionalOperation typed).run (.constructed evidence.step)).outcome
  exact constructional_constructed_is_realized evidence.step

/-- Suspension preserves the complete raw request and takes ordinary fallback. -/
theorem run_suspended_is_fallback {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    (request : RawSourceRequest presented) :
    Outcome.IsFallback
      (runState typed
        (.suspended : State (constructionFibre typed) request)).outcome := by
  change Outcome.IsFallback
    ((constructionalOperation typed).run (.raw request)).outcome
  exact constructional_raw_is_fallback request

/-- Local failure to establish the optional construction witness is not a
semantic rejection.  It safely returns the unchanged raw request. -/
theorem run_refuted_is_fallback {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {request : RawSourceRequest presented}
    (blame : Refutation (constructionFibre typed) request) :
    Outcome.IsFallback
      (runState typed
        (.refuted blame : State (constructionFibre typed) request)).outcome := by
  change Outcome.IsFallback
    ((constructionalOperation typed).run (.raw request)).outcome
  exact constructional_raw_is_fallback request

/-- Construction evidence is more precise than its suspended raw
request while sharing that request definitionally. -/
theorem exact_refines_suspended {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {request : RawSourceRequest presented}
    (evidence : ConstructedEvidence typed request) :
    Refines
      (.exact evidence : State (constructionFibre typed) request)
      (.suspended : State (constructionFibre typed) request) := by
  exact @Refines.exact_suspended (constructionFibre typed) request evidence

/-- Currentness leaves every family state unchanged. -/
@[simp] theorem activate_current {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {request : RawSourceRequest presented}
    {Revision : Type} [DecidableEq Revision]
    (revision : Revision)
    (state : State (constructionFibre typed) request) :
    state.activateAt revision revision = state :=
  activateAt_current revision state

/-- Staleness removes only optional construction evidence.  Running the
result necessarily reaches raw fallback. -/
theorem stale_state_runs_fallback {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented)
    {request : RawSourceRequest presented}
    {Revision : Type} [DecidableEq Revision]
    {cached current : Revision} (stale : cached ≠ current)
    (state : State (constructionFibre typed) request) :
    Outcome.IsFallback
      (runState typed (state.activateAt cached current)).outcome := by
  rw [activateAt_stale stale state]
  exact run_suspended_is_fallback request

/-! ## Revision-indexed NIK admission of the shared gradual operation -/

/-- Admit the already-proved constructional operation at one dependency
revision.  Unlike the stronger uniform-preservation family, this admission
requires only the typed constructional presentation. -/
def admitConstructionalAt {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented)
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    AdmittedAt dependencies revision
      (discreteOperationalObject (sourceObject typed))
      (discreteOperationalObject (targetObject typed)) where
  refinement := refinementOfAdmission (constructionalOperation typed)

/-- Current activation runs the same state adapter and retained constructional
operation.  No checker is introduced by graduality or admission. -/
@[simp] theorem active_run_state {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active :
      (admitConstructionalAt typed dependencies admittedRevision).Active
        currentRevision)
    {request : RawSourceRequest presented}
    (state : State (constructionFibre typed) request) :
    active.run (inputOfState state) = runState typed state :=
  rfl

theorem active_exact_is_realized {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active :
      (admitConstructionalAt typed dependencies admittedRevision).Active
        currentRevision)
    {request : RawSourceRequest presented}
    (evidence : ConstructedEvidence typed request) :
    Outcome.IsRealized
      (active.run (inputOfState
        (.exact evidence : State (constructionFibre typed) request))).outcome := by
  rw [active_run_state]
  exact run_exact_is_realized evidence

theorem active_suspended_is_fallback {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active :
      (admitConstructionalAt typed dependencies admittedRevision).Active
        currentRevision)
    (request : RawSourceRequest presented) :
    Outcome.IsFallback
      (active.run (inputOfState
        (.suspended : State (constructionFibre typed) request))).outcome := by
  rw [active_run_state]
  exact run_suspended_is_fallback request

/-! ## List controls -/

namespace Canary

open AuthoredIndexedFamilyNativeKernel.NativeList
open Mettapedia.Languages.MeTTa.PureKernel.Universe.NativeIndexedFamilySource

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision

noncomputable def listAdmission :=
  admitConstructionalAt typedNativePresentation dependencies false

noncomputable def activeList : listAdmission.Active false :=
  listAdmission.activate (dependencies.sameDependencies_refl false)

noncomputable def nilRequest : RawSourceRequest nativeListPresentedCandidate :=
  RawSourceRequest.ofConstructed canonicalNilConstructedStep

noncomputable def nilEvidence :
    ConstructedEvidence typedNativePresentation nilRequest :=
  by
    simpa [nilRequest] using
      (ConstructedEvidence.ofStep canonicalNilConstructedStep)

noncomputable def nilExactState :
    State (constructionFibre typedNativePresentation) nilRequest :=
  .exact nilEvidence

noncomputable def nilSuspendedState :
    State (constructionFibre typedNativePresentation) nilRequest :=
  .suspended

/-- Positive control: current exact List-nil construction reaches the direct
native result. -/
theorem current_nil_constructed_is_realized :
    Outcome.IsRealized
      (activeList.run (inputOfState nilExactState)).outcome :=
  active_exact_is_realized activeList nilEvidence

/-- Negative gradual control: the identical current raw request without its
construction witness falls back instead of being rejected or rechecked. -/
theorem current_nil_suspended_is_fallback :
    Outcome.IsFallback
      (activeList.run (inputOfState nilSuspendedState)).outcome :=
  active_suspended_is_fallback activeList nilRequest

/-- Exact and suspended states retain exactly the same structured raw
request despite selecting different operational faces. -/
theorem nil_request_conserved_across_precision :
    (inputOfState nilExactState).request = nilRequest ∧
      (inputOfState nilSuspendedState).request = nilRequest :=
  ⟨inputOfState_request nilExactState,
    inputOfState_request nilSuspendedState⟩

/-- A stale exact construction degrades to raw fallback, never semantic
rejection. -/
theorem stale_nil_exact_is_fallback :
    Outcome.IsFallback
      (runState typedNativePresentation
        (nilExactState.activateAt false true)).outcome :=
  stale_state_runs_fallback typedNativePresentation (by decide) nilExactState

/-- The NIK artifact itself cannot activate after the dependency changes. -/
theorem changed_revision_has_no_activation :
    ¬ Nonempty (listAdmission.Active true) := by
  rintro ⟨active⟩
  have changed := active.current ()
  simp [dependencies] at changed

end Canary

/-! ## Axiom audit -/

#print axioms ConstructedEvidence.ofStep
#print axioms inputOfState_request
#print axioms runState_valid
#print axioms run_exact_is_realized
#print axioms run_suspended_is_fallback
#print axioms run_refuted_is_fallback
#print axioms exact_refines_suspended
#print axioms stale_state_runs_fallback
#print axioms admitConstructionalAt
#print axioms active_run_state
#print axioms active_exact_is_realized
#print axioms active_suspended_is_fallback
#print axioms Canary.current_nil_constructed_is_realized
#print axioms Canary.current_nil_suspended_is_fallback
#print axioms Canary.nil_request_conserved_across_precision
#print axioms Canary.stale_nil_exact_is_fallback
#print axioms Canary.changed_revision_has_no_activation

end

end NativeIndexedFamilyGradualGuarantee
end Mettapedia.Languages.MeTTa.Prime
