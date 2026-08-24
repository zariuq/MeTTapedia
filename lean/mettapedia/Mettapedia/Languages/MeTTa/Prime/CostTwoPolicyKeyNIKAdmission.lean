import Mettapedia.Languages.MeTTa.Prime.CostTwoObservationKeyOrder

/-!
# Revision-current NIK admission for policy-sufficient receipt keys

The Cost² information order determines which receipt or cache representations
may serve which consumers.  This module connects that order to NIK's existing
revision-indexed execution admission without introducing a second semantic
authority.

`PolicySafe` is a proposition: it proves that a policy factors through a key.
Hot execution needs the stronger proof-carrying datum `PolicyRealization`,
which retains the keyed function together with its factorization law.  A
`PolicyKeyAdmission` stores one such realization for every requested policy
and, when requested, an exact decoder.  Current activation exposes only those
retained functions; no checker is an argument of the runner.

The canonical policy-vector key is least informative among all admitted keys
for a policy-only request.  Exact replay changes the request: every admitted
key is then information-equivalent to the identity key.  Concrete languages
may exhibit either refusal mode in separate annexes without changing this
generic admission boundary.
-/

namespace Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyKeyNIKAdmission

open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel
open Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary
open Mettapedia.Languages.MeTTa.Prime.CostTwoObservationKeyOrder
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

universe uState uPolicy uValue uKey uCoarse uOther uObservation

/-! ## Requests and retained native realizations -/

/-- A family of observations requested from one retained semantic state.
Values may depend on the policy index.  Exact replay is a separate capability,
not silently inferred from the policy family. -/
structure PolicyRequest (State : Type uState) where
  Policy : Type uPolicy
  Value : Policy → Type uValue
  observe : (policy : Policy) → State → Value policy
  requiresExactReplay : Prop

/-- The keyed function actually run after admission, paired with the theorem
that it implements the semantic policy. -/
structure PolicyRealization {State : Type uState} {Key : Type uKey}
    (key : State → Key) {Value : Type uValue} (policy : State → Value) where
  run : Key → Value
  agrees : policy = run ∘ key

namespace PolicyRealization

/-- Forget executable data to the policy-safety proposition. -/
theorem policySafe {State : Type uState} {Key : Type uKey}
    {key : State → Key} {Value : Type uValue} {policy : State → Value}
    (realization : PolicyRealization key policy) :
    PolicySafe key policy :=
  ⟨realization.run, realization.agrees⟩

@[simp] theorem run_encode {State : Type uState} {Key : Type uKey}
    {key : State → Key} {Value : Type uValue} {policy : State → Value}
    (realization : PolicyRealization key policy) (state : State) :
    realization.run (key state) = policy state := by
  exact (congrFun realization.agrees state).symm

end PolicyRealization

/-- An executable decoder paired with exact recovery.  Unlike
`ExactReplayKey`, this is retained data rather than mere existence. -/
structure ReplayRealization {State : Type uState} {Key : Type uKey}
    (key : State → Key) where
  decode : Key → State
  recovers : Function.LeftInverse decode key

namespace ReplayRealization

theorem exactReplayKey {State : Type uState} {Key : Type uKey}
    {key : State → Key} (replay : ReplayRealization key) :
    ExactReplayKey key :=
  ⟨replay.decode, replay.recovers⟩

end ReplayRealization

/-- A concrete forgetting map.  `KeyRefines` is its propositional shadow;
this data form is what can safely precompose an admitted hot runner. -/
structure KeyRefinement {State : Type uState} {Fine : Type uKey}
    {Coarse : Type uCoarse} (fine : State → Fine) (coarse : State → Coarse)
    where
  forget : Fine → Coarse
  commutes : coarse = forget ∘ fine

namespace KeyRefinement

theorem keyRefines {State : Type uState} {Fine : Type uKey}
    {Coarse : Type uCoarse} {fine : State → Fine} {coarse : State → Coarse}
    (refinement : KeyRefinement fine coarse) :
    KeyRefines fine coarse :=
  ⟨refinement.forget, refinement.commutes⟩

def refl {State : Type uState} {Key : Type uKey} (key : State → Key) :
    KeyRefinement key key where
  forget := id
  commutes := by funext state; rfl

def trans {State : Type uState} {Fine : Type uKey} {Middle : Type uCoarse}
    {Coarse : Type uOther}
    {fine : State → Fine} {middle : State → Middle}
    {coarse : State → Coarse}
    (fineMiddle : KeyRefinement fine middle)
    (middleCoarse : KeyRefinement middle coarse) :
    KeyRefinement fine coarse where
  forget := middleCoarse.forget ∘ fineMiddle.forget
  commutes := by
    funext state
    calc
      coarse state = middleCoarse.forget (middle state) :=
        congrFun middleCoarse.commutes state
      _ = middleCoarse.forget (fineMiddle.forget (fine state)) :=
        congrArg middleCoarse.forget (congrFun fineMiddle.commutes state)
      _ = ((middleCoarse.forget ∘ fineMiddle.forget) ∘ fine) state := rfl

end KeyRefinement

/-! ## Revision-indexed policy-key admission -/

/-- NIK admission of one receipt key at one dependency revision.  The key is
not a semantic authority: it is a displayed capability over semantic state.
Every runnable function is retained as data, and exact replay is present only
when the request explicitly requires it. -/
structure PolicyKeyAdmission
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    {State : Type uState} (request : PolicyRequest State)
    {Key : Type uKey} (key : State → Key) where
  realize : (policy : request.Policy) →
    PolicyRealization key (request.observe policy)
  replay : request.requiresExactReplay → ReplayRealization key

namespace PolicyKeyAdmission

variable {dependencies : DependencySystem}
variable {revision currentRevision : dependencies.Revision}
variable {State : Type uState} {request : PolicyRequest State}
variable {Key : Type uKey} {key : State → Key}

theorem supports (admission : PolicyKeyAdmission dependencies revision request key)
    (policy : request.Policy) :
    PolicySafe key (request.observe policy) :=
  (admission.realize policy).policySafe

theorem exactReplayKey
    (admission : PolicyKeyAdmission dependencies revision request key)
    (required : request.requiresExactReplay) :
    ExactReplayKey key :=
  (admission.replay required).exactReplayKey

/-- Currentness guards activation exactly as in NIK's execution admissions. -/
structure Active
    (_admission : PolicyKeyAdmission dependencies revision request key)
    (currentRevision : dependencies.Revision) : Prop where
  current : dependencies.SameDependencies revision currentRevision

def activate
    (admission : PolicyKeyAdmission dependencies revision request key)
    (current : dependencies.SameDependencies revision currentRevision) :
    admission.Active currentRevision :=
  ⟨current⟩

/-- Hot execution is the keyed function retained at admission. -/
def Active.runKey
    {admission : PolicyKeyAdmission dependencies revision request key}
    (_active : admission.Active currentRevision) (policy : request.Policy) :
    Key → request.Value policy :=
  (admission.realize policy).run

/-- Running an admitted keyed policy agrees with its semantic observation. -/
@[simp] theorem Active.runKey_encode
    {admission : PolicyKeyAdmission dependencies revision request key}
    (active : admission.Active currentRevision) (policy : request.Policy)
    (state : State) :
    active.runKey policy (key state) = request.observe policy state :=
  (admission.realize policy).run_encode state

/-- Preparation retains the semantic state independently of its potentially
lossy policy key, preserving deoptimization. -/
structure PreparedState
    (_admission : PolicyKeyAdmission dependencies revision request key) where
  state : State
  encoded : Key
  encoded_adequate : encoded = key state

def prepare
    (admission : PolicyKeyAdmission dependencies revision request key)
    (state : State) : admission.PreparedState where
  state := state
  encoded := key state
  encoded_adequate := rfl

def PreparedState.fallback
    {admission : PolicyKeyAdmission dependencies revision request key}
    (prepared : admission.PreparedState) : State :=
  prepared.state

@[simp] theorem PreparedState.fallback_eq
    {admission : PolicyKeyAdmission dependencies revision request key}
    (prepared : admission.PreparedState) :
    prepared.fallback = prepared.state :=
  rfl

def Active.runPrepared
    {admission : PolicyKeyAdmission dependencies revision request key}
    (active : admission.Active currentRevision)
    (prepared : admission.PreparedState) (policy : request.Policy) :
    request.Value policy :=
  active.runKey policy prepared.encoded

@[simp] theorem Active.runPrepared_eq
    {admission : PolicyKeyAdmission dependencies revision request key}
    (active : admission.Active currentRevision)
    (prepared : admission.PreparedState) (policy : request.Policy) :
    active.runPrepared prepared policy = request.observe policy prepared.state := by
  unfold Active.runPrepared Active.runKey
  rw [prepared.encoded_adequate]
  exact (admission.realize policy).run_encode prepared.state

def StaleAt
    (_admission : PolicyKeyAdmission dependencies revision request key)
    (candidateRevision : dependencies.Revision) : Prop :=
  ¬ dependencies.SameDependencies revision candidateRevision

theorem stale_prevents_activation
    (admission : PolicyKeyAdmission dependencies revision request key)
    {candidateRevision : dependencies.Revision}
    (stale : admission.StaleAt candidateRevision) :
    ¬ admission.Active candidateRevision := by
  rintro ⟨current⟩
  exact stale current

theorem stale_preserves_fallback
    (admission : PolicyKeyAdmission dependencies revision request key)
    {candidateRevision : dependencies.Revision}
    (_stale : admission.StaleAt candidateRevision)
    (prepared : admission.PreparedState) :
    prepared.fallback = prepared.state :=
  rfl

/-- Pull a coarse admitted representation back along a concrete information
refinement.  This is the executable form of policy-safety monotonicity. -/
def pullback
    {Coarse : Type uCoarse} {coarse : State → Coarse}
    (coarseAdmission :
      PolicyKeyAdmission dependencies revision request coarse)
    (refinement : KeyRefinement key coarse) :
    PolicyKeyAdmission dependencies revision request key where
  realize := fun policy =>
    { run := (coarseAdmission.realize policy).run ∘ refinement.forget
      agrees := by
        funext state
        change request.observe policy state =
          (coarseAdmission.realize policy).run
            (refinement.forget (key state))
        have coarseEq :
            coarse state = refinement.forget (key state) := by
          simpa only [Function.comp_apply] using
            congrFun refinement.commutes state
        rw [← coarseEq]
        simpa only [Function.comp_apply] using
          congrFun (coarseAdmission.realize policy).agrees state }
  replay := fun required =>
    { decode := (coarseAdmission.replay required).decode ∘ refinement.forget
      recovers := fun state => by
        change (coarseAdmission.replay required).decode
          (refinement.forget (key state)) = state
        have coarseEq :
            coarse state = refinement.forget (key state) := by
          simpa only [Function.comp_apply] using
            congrFun refinement.commutes state
        rw [← coarseEq]
        exact (coarseAdmission.replay required).recovers state }

end PolicyKeyAdmission

/-! ## Display over the existing NIK execution model -/

/-- A request-scoped receipt view is additional structure on one already
admitted semantic execution model.  It cannot mint or replace the model's
semantic refinement. -/
structure AdmittedReceiptView
    {Observation : Type uObservation} {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {source target : IndexedObservedOperationalObject.{uState, uObservation}
      Observation}
    (model : AdmittedExecutionModel dependencies revision source target)
    (request : PolicyRequest (ExecutionTrace target.operational))
    {Key : Type uKey} (key : ExecutionTrace target.operational → Key) where
  receiptAdmission : PolicyKeyAdmission dependencies revision request key

namespace AdmittedReceiptView

variable {Observation : Type uObservation} {dependencies : DependencySystem}
variable {revision currentRevision : dependencies.Revision}
variable {source target : IndexedObservedOperationalObject.{uState, uObservation}
  Observation}
variable {model : AdmittedExecutionModel dependencies revision source target}
variable {request : PolicyRequest (ExecutionTrace target.operational)}
variable {Key : Type uKey} {key : ExecutionTrace target.operational → Key}

/-- Emit only the request-scoped key after the already-admitted semantic
execution. -/
def emit
    (_view : AdmittedReceiptView model request key)
    (active : model.admission.Active currentRevision)
    (prepared : model.PreparedTrace) : Key :=
  key (model.compileTrace active prepared.sourceTrace)

/-- Evaluate a requested observation from the retained key runner. -/
def evaluate
    (view : AdmittedReceiptView model request key)
    (active : model.admission.Active currentRevision)
    (prepared : model.PreparedTrace) (policy : request.Policy) :
    request.Value policy :=
  (view.receiptAdmission.realize policy).run (view.emit active prepared)

/-- The scoped keyed observation agrees with the complete semantic target
trace produced by the existing NIK admission. -/
theorem evaluate_eq
    (view : AdmittedReceiptView model request key)
    (active : model.admission.Active currentRevision)
    (prepared : model.PreparedTrace) (policy : request.Policy) :
    view.evaluate active prepared policy =
      request.observe policy (model.compileTrace active prepared.sourceTrace) :=
  (view.receiptAdmission.realize policy).run_encode _

/-- Staleness of the underlying NIK model prevents the scoped receipt view
from running, while the model's independently retained raw fallback survives. -/
theorem stale_prevents_view_and_preserves_fallback
    (_view : AdmittedReceiptView model request key)
    {candidateRevision : dependencies.Revision}
    (stale : model.StaleAt candidateRevision)
    (prepared : model.PreparedTrace) :
    (¬ model.admission.Active candidateRevision) ∧
      model.rawCodec.decode prepared.fallback = prepared.sourceTrace :=
  ⟨model.stale_prevents_activation stale,
    model.stale_preserves_fallback stale prepared⟩

end AdmittedReceiptView

/-! ## Canonical least keys for policy-only requests -/

/-- The complete vector of requested policy values. -/
abbrev PolicyVector {State : Type uState} (request : PolicyRequest State) :=
  (policy : request.Policy) → request.Value policy

def policyVectorKey {State : Type uState} (request : PolicyRequest State) :
    State → PolicyVector request :=
  fun state policy => request.observe policy state

/-- For a policy-only request, the policy vector itself is an admitted key. -/
def policyVectorAdmission
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    {State : Type uState} (request : PolicyRequest State)
    (policyOnly : ¬ request.requiresExactReplay) :
    PolicyKeyAdmission dependencies revision request (policyVectorKey request) where
  realize := fun policy =>
    { run := fun values => values policy
      agrees := by funext state; rfl }
  replay := fun exact => False.elim (policyOnly exact)

/-- Every admitted key refines the policy-vector key.  Thus the vector is the
least informative representation sufficient for the declared policy family;
it retains no distinction not visible to some requested policy. -/
def admissionRefinesPolicyVector
    {dependencies : DependencySystem} {revision : dependencies.Revision}
    {State : Type uState} {request : PolicyRequest State}
    {Key : Type uKey} {key : State → Key}
    (admission : PolicyKeyAdmission dependencies revision request key) :
    KeyRefinement key (policyVectorKey request) where
  forget := fun encoded policy => (admission.realize policy).run encoded
  commutes := by
    funext state policy
    simpa only [policyVectorKey, Function.comp_apply] using
      ((admission.realize policy).run_encode state).symm

theorem every_admitted_key_refines_policyVector
    {dependencies : DependencySystem} {revision : dependencies.Revision}
    {State : Type uState} {request : PolicyRequest State}
    {Key : Type uKey} {key : State → Key}
    (admission : PolicyKeyAdmission dependencies revision request key) :
    KeyRefines key (policyVectorKey request) :=
  (admissionRefinesPolicyVector admission).keyRefines

/-- Retaining the full state always admits every policy and exact replay. -/
def identityKeyAdmission
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    {State : Type uState} (request : PolicyRequest State) :
    PolicyKeyAdmission dependencies revision request (id : State → State) where
  realize := fun policy =>
    { run := request.observe policy
      agrees := by funext state; rfl }
  replay := fun _ =>
    { decode := id
      recovers := fun _ => rfl }

/-- Under an exact-replay request, every admitted representation is
information-equivalent to retaining the full state. -/
theorem exactRequest_admittedKey_mutuallyRefines_identity
    {dependencies : DependencySystem} {revision : dependencies.Revision}
    {State : Type uState} {request : PolicyRequest State}
    {Key : Type uKey} {key : State → Key}
    (admission : PolicyKeyAdmission dependencies revision request key)
    (required : request.requiresExactReplay) :
    KeyRefines key (id : State → State) ∧
      KeyRefines (id : State → State) key := by
  exact exactReplayKeys_mutuallyRefine
    (admission.exactReplayKey required)
    (⟨id, fun _ => rfl⟩ : ExactReplayKey (id : State → State))

/-- A request for one policy, optionally with exact replay. -/
def singlePolicyRequest {State : Type uState} {Value : Type uValue}
    (policy : State → Value) (requiresExactReplay : Prop) :
    PolicyRequest State where
  Policy := Unit
  Value := fun _ => Value
  observe := fun _ => policy
  requiresExactReplay := requiresExactReplay

/-! ## Revision controls -/

namespace RevisionCanary

def dependencies : DependencySystem where
  Revision := Bool × Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision.1

def request : PolicyRequest Bool :=
  singlePolicyRequest (fun value => !value) False

def admission : PolicyKeyAdmission dependencies (false, false) request
    (id : Bool → Bool) :=
  identityKeyAdmission dependencies (false, false) request

def current : admission.Active (false, true) :=
  admission.activate (fun _ => rfl)

theorem irrelevant_change_runs_retained_policy :
    current.runKey () true = false :=
  rfl

def prepared : admission.PreparedState :=
  admission.prepare true

theorem irrelevant_change_runPrepared :
    current.runPrepared prepared () = false :=
  rfl

theorem relevant_change_is_stale : admission.StaleAt (true, false) := by
  intro same
  have impossible := same ()
  simp [dependencies] at impossible

theorem relevant_change_prevents_activation_and_preserves_fallback :
    (¬ admission.Active (true, false)) ∧ prepared.fallback = true :=
  ⟨admission.stale_prevents_activation relevant_change_is_stale, rfl⟩

end RevisionCanary

#print axioms PolicyRealization.run_encode
#print axioms KeyRefinement.trans
#print axioms PolicyKeyAdmission.Active.runPrepared_eq
#print axioms PolicyKeyAdmission.pullback
#print axioms AdmittedReceiptView.evaluate_eq
#print axioms AdmittedReceiptView.stale_prevents_view_and_preserves_fallback
#print axioms every_admitted_key_refines_policyVector
#print axioms exactRequest_admittedKey_mutuallyRefines_identity
#print axioms RevisionCanary.relevant_change_prevents_activation_and_preserves_fallback

end Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyKeyNIKAdmission
