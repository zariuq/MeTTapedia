import Mettapedia.CognitiveArchitecture.ForegroundBackgroundParallelWave
import Mettapedia.CognitiveArchitecture.ProtectedMindAgentWave

/-!
# Protected foreground/background articles through ordinary NIK

The core parallel article checks semantic backend admission, revision scope,
plan and delta identities, occurrence order, and execution mode.  Those laws
do not by themselves say that the physical input payloads encode the semantic
events or that the emitted payload encodes the semantic terminal observation.

This module adds two independently exact authority facets:

* semantic--physical binding of both authored inputs and emitted result;
* an observer-visible protected transition.

The facets compose with the existing replay checker by the generic checker
conjunction.  The resulting article enters the ordinary statusful NIK
frontend.  Positive and adversarial controls show that the old structural
article can accept forged payloads, that the binding facet rejects them, and
that a correctly bound, funded, serializable rewind remains available to the
ordinary authority while being refused by the protected authority.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.ProtectedForegroundBackgroundNIKArticle

open Mettapedia.CognitiveArchitecture.ForegroundBackgroundParallelWave
open Mettapedia.CognitiveArchitecture.ProtectedMindAgentWave
open Mettapedia.CognitiveArchitecture.ProtectedMindAgentWave.Canary
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Dynamics.CertifiedBatchParallelBridge
open Mettapedia.GSLT.Dynamics.EventValuation
open Mettapedia.GSLT.Dynamics.OperatorRealization
open Mettapedia.GSLT.Dynamics.ParallelExecutionAuthority
open Mettapedia.GSLT.Dynamics.QueryRevision
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKDefaultProfile

noncomputable section

/-! ## Exact semantic--physical input and result binding -/

abbrev WorkspaceTheory : Theory :=
  deterministicTheory workspaceStep observeWorkspace

abbrev Article :=
  Claim WorkspaceTheory Unit Nat PhysicalPayload Nat Nat

/-- Execute the semantic events in the canonical order named by the article. -/
def semanticTarget (claim : Article) : Workspace :=
  execute claim.event.source [claim.event.first, claim.event.second]

def semanticTerminalObservation (claim : Article) : WorkspaceView :=
  observeWorkspace (semanticTarget claim)

/-- Resolve exactly two authored physical occurrences as work payloads. -/
def authoredWorkPair? (claim : Article) : Option (Work × Work) :=
  match claim.plan.authoredOccurrences with
  | [firstId, secondId] =>
      match claim.snapshot.resolve firstId, claim.snapshot.resolve secondId with
      | some (.work first), some (.work second) => some (first, second)
      | _, _ => none
  | _ => none

/-- Decode exactly one emitted workspace observation. -/
def emittedWorkspaceObservation? (claim : Article) : Option WorkspaceView :=
  match claim.delta.entries with
  | [(_, .observed view)] => some view
  | _ => none

/-- The physical article names the same two semantic events, in order, and
emits the observation of their semantic terminal state. -/
def SemanticallyBound (claim : Article) : Prop :=
  authoredWorkPair? claim = some (claim.event.first, claim.event.second) /\
    emittedWorkspaceObservation? claim =
      some (semanticTerminalObservation claim)

def bindingCheck (claim : Article) : Bool :=
  decide (authoredWorkPair? claim =
    some (claim.event.first, claim.event.second)) &&
  decide (emittedWorkspaceObservation? claim =
    some (semanticTerminalObservation claim))

theorem bindingCheck_eq_true_iff (claim : Article) :
    bindingCheck claim = true <-> SemanticallyBound claim := by
  simp [bindingCheck, SemanticallyBound]

def bindingKernel : Checker.DecisionKernel Article SemanticallyBound where
  decide := bindingCheck
  correct := bindingCheck_eq_true_iff

def bindingChecker : Checker Article Unit := bindingKernel.toChecker

def bindingProjection : bindingChecker.AuthorityProjection
    SemanticallyBound SemanticallyBound :=
  bindingKernel.authority.toProjection

/-! ## Exact protected-transition facet -/

/-- The protected appraisal is read through the exact workspace observer
already named by the semantic theory. -/
def ProgressAllowed (claim : Article) : Prop :=
  Exists fun targetView =>
    emittedWorkspaceObservation? claim = some targetView /\
      (observeWorkspace claim.event.source).1 <= targetView.1

def progressCheck (claim : Article) : Bool :=
  match emittedWorkspaceObservation? claim with
  | none => false
  | some targetView =>
      decide ((observeWorkspace claim.event.source).1 <= targetView.1)

theorem progressCheck_eq_true_iff (claim : Article) :
    progressCheck claim = true <-> ProgressAllowed claim := by
  unfold progressCheck ProgressAllowed
  cases emitted : emittedWorkspaceObservation? claim with
  | none => simp
  | some targetView => simp

def progressKernel : Checker.DecisionKernel Article ProgressAllowed where
  decide := progressCheck
  correct := progressCheck_eq_true_iff

def progressChecker : Checker Article Unit := progressKernel.toChecker

def progressProjection : progressChecker.AuthorityProjection
    ProgressAllowed ProgressAllowed :=
  progressKernel.authority.toProjection

/-! ## Conjunction with one existing parallel backend authority -/

section Backend

variable {backend : ParallelBackend WorkspaceTheory}

def boundChecker
    (admission : AdmissionAuthority backend) :
    Checker Article (admission.Certificate × Unit) :=
  Checker.conjunction (replayChecker admission) bindingChecker

def BoundCertified
    (claim : Article) : Prop :=
  Certified (backend := backend) claim /\ SemanticallyBound claim

def BoundMeaning
    (claim : Article) : Prop :=
  Meaning (backend := backend) claim /\ SemanticallyBound claim

def boundProjection
    (admission : AdmissionAuthority backend) :
    (boundChecker admission).AuthorityProjection
      (BoundCertified (backend := backend))
      (BoundMeaning (backend := backend)) :=
  (authorityProjection admission).conjunction bindingProjection

def protectedChecker
    (admission : AdmissionAuthority backend) :
    Checker Article ((admission.Certificate × Unit) × Unit) :=
  Checker.conjunction (boundChecker admission) progressChecker

def ProtectedCertified
    (claim : Article) : Prop :=
  BoundCertified (backend := backend) claim /\ ProgressAllowed claim

def ProtectedMeaning
    (claim : Article) : Prop :=
  BoundMeaning (backend := backend) claim /\ ProgressAllowed claim

def protectedProjection
    (admission : AdmissionAuthority backend) :
    (protectedChecker admission).AuthorityProjection
      (ProtectedCertified (backend := backend))
      (ProtectedMeaning (backend := backend)) :=
  (boundProjection admission).conjunction progressProjection

/-- The refined article is one ordinary NIK authority fibre.  Its evidence is
the product of the independently replayed base, binding, and protection
certificates. -/
def protectedFamily
    (admission : AdmissionAuthority backend) : AuthorityFamily Unit where
  Claim := fun _ => Article
  Certificate := fun _ => (admission.Certificate × Unit) × Unit
  checker := fun _ => protectedChecker admission
  Certified := fun _ => ProtectedCertified (backend := backend)
  Meaning := fun _ => ProtectedMeaning (backend := backend)
  projection := fun _ => protectedProjection admission

def protectedFrontend
    (admission : AdmissionAuthority backend) :=
  Frontend.typed (protectedFamily admission)

def protectedSubmission
    (admission : AdmissionAuthority backend)
    (claim : Article)
    (certificate : (admission.Certificate × Unit) × Unit) :
    TypedSubmission (protectedFamily admission) :=
  ⟨(), claim, certificate⟩

end Backend

/-! ## The useful foreground/background article -/

theorem useful_binding_accepted :
    bindingChecker.check physicalClaim () = true := by
  change bindingCheck physicalClaim = true
  exact (bindingCheck_eq_true_iff physicalClaim).2 ⟨rfl, rfl⟩

theorem useful_progress_accepted :
    progressChecker.check physicalClaim () = true := by
  decide

theorem useful_protected_article_accepted :
    (protectedChecker replayableAdmission).check
      physicalClaim (((), ()), ()) = true := by
  simp [protectedChecker, boundChecker, Checker.conjunction,
    physical_article_accepted, useful_binding_accepted,
    useful_progress_accepted]

theorem useful_protected_article_meaning :
    ProtectedMeaning (backend := replayableParallelBackend) physicalClaim :=
  (protectedProjection replayableAdmission).sound
    physicalClaim (((), ()), ()) useful_protected_article_accepted

def usefulProtectedSubmission :=
  protectedSubmission replayableAdmission physicalClaim (((), ()), ())

/-- The protected article uses the ordinary statusful NIK frontend. -/
theorem useful_protected_article_defaultNIK_accepts :
    (protectedFrontend replayableAdmission).run
        ((protectedFrontend replayableAdmission).encode
          usefulProtectedSubmission) =
      SubmissionOutcome.accepted
        (TypedSubmission.claim usefulProtectedSubmission) := by
  simpa [usefulProtectedSubmission, protectedSubmission, protectedFrontend,
    protectedFamily, useful_protected_article_accepted] using
      (protectedFrontend replayableAdmission).run_encode
        usefulProtectedSubmission

/-- The NIK article and the independently proved wave share the exact semantic
source and target; protection is not inferred from NIK acceptance alone. -/
theorem useful_article_replays_exact_protected_wave :
    ProtectedMeaning (backend := replayableParallelBackend) physicalClaim /\
      semanticTarget physicalClaim = parallelTarget /\
      Nonempty
        (ProtectedBatch completeBagContract semantics initialWorkspace
          parallelTarget (fun work => (shortDemand work, longDemand work))
          (shortSource, longSource) parallelBatch progressConstraint) := by
  exact ⟨useful_protected_article_meaning, rfl, ⟨protectedUsefulWave⟩⟩

/-! ## Structural replay does not bind semantic payloads -/

def forgedInputSnapshot : PhysicalSnapshot where
  storeId := ()
  revision := 0
  entries :=
    [.work .refreshPremiseIndex, .work .foregroundBridge]

def forgedInputClaim : Article :=
  { physicalClaim with snapshot := forgedInputSnapshot }

/-- The original structural checker intentionally accepts the same scoped
occurrence IDs even when their payloads no longer encode the semantic event
order. -/
theorem forged_input_base_article_accepted :
    (replayChecker replayableAdmission).check forgedInputClaim () = true := by
  decide

theorem forged_input_binding_rejected :
    bindingChecker.check forgedInputClaim () = false := by
  decide

theorem forged_input_protected_article_rejected :
    (protectedChecker replayableAdmission).check
      forgedInputClaim (((), ()), ()) = false := by
  decide

def forgedOutputSnapshot : PhysicalSnapshot where
  storeId := ()
  revision := 1
  entries := [.observed (observeWorkspace initialWorkspace)]

def forgedOutputDelta :=
  { physicalDelta with entries := forgedOutputSnapshot.occurrences }

def forgedOutputReceipt :=
  { physicalReceipt with
    emittedOccurrences := forgedOutputDelta.entries.map Prod.fst }

def forgedOutputClaim : Article :=
  { physicalClaim with
    delta := forgedOutputDelta
    receipt := forgedOutputReceipt }

/-- Structural receipt coherence alone also accepts a correctly scoped but
semantically false emitted observation. -/
theorem forged_output_base_article_accepted :
    (replayChecker replayableAdmission).check forgedOutputClaim () = true := by
  decide

theorem forged_output_binding_rejected :
    bindingChecker.check forgedOutputClaim () = false := by
  decide

theorem forged_output_protected_article_rejected :
    (protectedChecker replayableAdmission).check
      forgedOutputClaim (((), ()), ()) = false := by
  decide

/-- Existing revision and multiplicity severance remain load-bearing after
adding the two new facets. -/
theorem stale_and_reordered_still_rejected :
    (protectedChecker replayableAdmission).check
        stalePhysicalClaim (((), ()), ()) = false /\
      (protectedChecker replayableAdmission).check
        reorderedPhysicalClaim (((), ()), ()) = false := by
  decide

/-! ## Correctly bound but protected-refused rewind -/

/-- Rewind and premise refresh commute at the workspace observer for every
source, even though the rewind may violate a separately authored concern. -/
theorem rewind_refresh_queryCoexecutible (source : Workspace) :
    WorkspaceTheory.QueryCoexecutible
      .intrusiveRewind .refreshPremiseIndex source := by
  rcases source with ⟨foreground, index⟩
  refine ⟨{
    afterFirst := workspaceStep (foreground, index) .intrusiveRewind
    afterSecond := workspaceStep (foreground, index) .refreshPremiseIndex
    firstThenSecond :=
      workspaceStep
        (workspaceStep (foreground, index) .intrusiveRewind)
        .refreshPremiseIndex
    secondThenFirst :=
      workspaceStep
        (workspaceStep (foreground, index) .refreshPremiseIndex)
        .intrusiveRewind
    firstFromSource := rfl
    secondFromSource := rfl
    secondAfterFirst := rfl
    firstAfterSecond := rfl
    observationAgrees := ?_ }⟩
  rfl

def CanonicalRewindPair (first second : Work) : Prop :=
  first = .intrusiveRewind /\ second = .refreshPremiseIndex

def rewindParallelBackend : ParallelBackend WorkspaceTheory where
  valuation := eventCount WorkspaceTheory
  Admits := fun first second _source => CanonicalRewindPair first second
  sound := by
    intro first second source admitted
    rcases admitted with ⟨rfl, rfl⟩
    exact ⟨rewind_refresh_queryCoexecutible source,
      additive_compatible
        (theory := WorkspaceTheory) (Grade := Nat)
        (fun _work : Work => 1) .intrusiveRewind .refreshPremiseIndex⟩

def rewindAdmissionDecision (claim : EventClaim WorkspaceTheory) : Bool :=
  decide (claim.first = Work.intrusiveRewind /\
    claim.second = Work.refreshPremiseIndex)

theorem rewindAdmissionDecision_reflects (claim : EventClaim WorkspaceTheory) :
    rewindAdmissionDecision claim = true <->
      Admitted rewindParallelBackend claim := by
  simp [rewindAdmissionDecision, Admitted, rewindParallelBackend,
    CanonicalRewindPair]
  exact Iff.rfl

def rewindAdmission : AdmissionAuthority rewindParallelBackend :=
  Mettapedia.GSLT.Dynamics.ReplayableParallelAdmission.ofBooleanDecision
    rewindAdmissionDecision rewindAdmissionDecision_reflects

def rewindEventClaim : EventClaim WorkspaceTheory where
  first := .intrusiveRewind
  second := .refreshPremiseIndex
  source := harmfulSource
  request := ()

def rewindPhysicalSnapshot : PhysicalSnapshot where
  storeId := ()
  revision := 40
  entries := [.work .intrusiveRewind, .work .refreshPremiseIndex]

def rewindOccurrence := rewindPhysicalSnapshot.occurrenceId 0
def rewindIndexerOccurrence := rewindPhysicalSnapshot.occurrenceId 1

def rewindPhysicalPlan : OperatorPlan Unit Nat Unit Nat where
  id := 41
  observer := ()
  sourceBackend := ()
  targetBackend := ()
  sourceRevision := 40
  authoredOccurrences := [rewindOccurrence, rewindIndexerOccurrence]

def rewindTargetSnapshot : PhysicalSnapshot where
  storeId := ()
  revision := 42
  entries := [.observed (observeWorkspace harmfulTarget)]

def rewindPhysicalDelta : Delta Unit Nat PhysicalPayload Nat where
  id := 43
  sourceBackend := ()
  targetBackend := ()
  sourceRevision := 40
  targetRevision := 42
  entries := rewindTargetSnapshot.occurrences

def rewindPhysicalReceipt : Receipt Unit Nat Unit Nat Nat where
  planId := rewindPhysicalPlan.id
  observer := ()
  sourceBackend := ()
  targetBackend := ()
  sourceRevision := 40
  targetRevision := 42
  deltaId := rewindPhysicalDelta.id
  mode := .parallel
  authoredOccurrences := rewindPhysicalPlan.authoredOccurrences
  emittedOccurrences := rewindPhysicalDelta.entries.map Prod.fst

def rewindPhysicalClaim : Article where
  event := rewindEventClaim
  snapshot := rewindPhysicalSnapshot
  plan := rewindPhysicalPlan
  delta := rewindPhysicalDelta
  receipt := rewindPhysicalReceipt

theorem rewind_semantic_target_is_harmfulTarget :
    semanticTarget rewindPhysicalClaim = harmfulTarget :=
  rfl

/-- The original replay authority accepts the correctly scoped rewind
article. -/
theorem rewind_base_article_accepted :
    (replayChecker rewindAdmission).check rewindPhysicalClaim () = true := by
  decide

theorem rewind_binding_accepted :
    bindingChecker.check rewindPhysicalClaim () = true := by
  change bindingCheck rewindPhysicalClaim = true
  exact (bindingCheck_eq_true_iff rewindPhysicalClaim).2 ⟨rfl, rfl⟩

/-- The rewind article is semantically admitted, physically coherent, and
bound in both directions. -/
theorem rewind_bound_article_accepted :
    (boundChecker rewindAdmission).check
      rewindPhysicalClaim ((), ()) = true := by
  simp [boundChecker, Checker.conjunction, rewind_base_article_accepted,
    rewind_binding_accepted]

/-- Its separately authored progress concern refuses the exact emitted
target.  This refusal is not a failure of semantic execution or replay. -/
theorem rewind_progress_rejected :
    progressChecker.check rewindPhysicalClaim () = false := by
  decide

theorem rewind_protected_article_rejected :
    (protectedChecker rewindAdmission).check
      rewindPhysicalClaim (((), ()), ()) = false := by
  simp [protectedChecker, Checker.conjunction,
    rewind_bound_article_accepted, rewind_progress_rejected]

theorem bound_execution_does_not_mint_protected_authority :
    (boundChecker rewindAdmission).check
        rewindPhysicalClaim ((), ()) = true /\
      (protectedChecker rewindAdmission).check
        rewindPhysicalClaim (((), ()), ()) = false :=
  ⟨rewind_bound_article_accepted, rewind_protected_article_rejected⟩

#print axioms progressCheck_eq_true_iff
#print axioms useful_protected_article_meaning
#print axioms useful_protected_article_defaultNIK_accepts
#print axioms useful_article_replays_exact_protected_wave
#print axioms forged_input_base_article_accepted
#print axioms forged_input_binding_rejected
#print axioms forged_output_base_article_accepted
#print axioms forged_output_binding_rejected
#print axioms rewind_refresh_queryCoexecutible
#print axioms rewind_base_article_accepted
#print axioms rewind_binding_accepted
#print axioms rewind_bound_article_accepted
#print axioms rewind_progress_rejected
#print axioms bound_execution_does_not_mint_protected_authority

end

end Mettapedia.CognitiveArchitecture.ProtectedForegroundBackgroundNIKArticle
