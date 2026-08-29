import Mettapedia.CognitiveArchitecture.ForegroundChainingActivationPolicy
import Mettapedia.CognitiveArchitecture.AttentionGuidedMindAgentWave
import Mettapedia.GSLT.Dynamics.CertifiedBatchParallelBridge
import Mettapedia.GSLT.Dynamics.ReplayableParallelAdmission

/-!
# A real foreground loop with a parallel background organizer

This module instantiates the generic mind-agent wave on the actual given-clause
continuation store.  The foreground occurrence performs the real
`Snapshot.tick`; the background occurrence refreshes the Chapter-13 premise
index in an independent workspace component.  The two operations commute on
every workspace state, so complete-bag observation and exact STI/LTI funding
license their parallel wave.

An intentionally intrusive background occurrence instead rewinds the
foreground continuation store.  It can receive a separate resource account,
but its two schedules disagree at the declared workspace observer.  It must
therefore be deferred or serialized rather than admitted as a parallel wave.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.ForegroundBackgroundParallelWave

noncomputable section

open Mettapedia.CognitiveArchitecture.AttentionEconomy
open Mettapedia.CognitiveArchitecture.AttentionEconomyResourceControl
open Mettapedia.CognitiveArchitecture.AttentionGuidedMindAgentWave
open Mettapedia.CognitiveArchitecture.ForegroundChainingActivationPolicy
open Mettapedia.CognitiveArchitecture.ForegroundChainingPremiseService
open Mettapedia.GSLT.Core.GivenClauseLoop
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Core.WeightedOccurrenceControl
open Mettapedia.GSLT.Dynamics.CertifiedBatchParallelBridge
open Mettapedia.GSLT.Dynamics.ContextualControlSurface
open Mettapedia.GSLT.Dynamics.EventValuation
open Mettapedia.GSLT.Dynamics.ParallelExecutionAuthority
open Mettapedia.GSLT.Dynamics.ReplayableParallelAdmission
open Mettapedia.GSLT.Dynamics.TypedValueGeometry

/-! ## Product workspace and its real operations -/

/-- Work occurrences retain operational identity even when two occurrences
would ultimately compute equal metadata. -/
inductive Work where
  | foregroundBridge
  | refreshPremiseIndex
  | intrusiveRewind
deriving DecidableEq, Repr

/-- The premise index is the actual finite result of the Chapter-13 selector. -/
abbrev PremiseIndex := Finset Bool

/-- Foreground continuations and background organizational metadata share one
logical workspace while remaining separately addressable components. -/
abbrev Workspace := ForegroundState × PremiseIndex

/-- The declared observer sees foreground progress and the current premise
index, but not the representation of the continuation store. -/
abbrev WorkspaceView := Nat × PremiseIndex

def observeWorkspace (workspace : Workspace) : WorkspaceView :=
  (workspace.1.processed.length, workspace.2)

/-- The positive run starts after the selected premise has been admitted but
before the foreground has consumed it or the background index has refreshed. -/
def initialWorkspace : Workspace :=
  (admittedSnapshot, ∅)

/-- Operational meaning of each exact work occurrence. -/
def applyWork : Work → Workspace → Workspace
  | .foregroundBridge, (foreground, index) =>
      (Snapshot.tick chainingSystem Snapshot.breadthOnly foreground, index)
  | .refreshPremiseIndex, (foreground, _index) =>
      (foreground, selectedPremises)
  | .intrusiveRewind, (_foreground, index) =>
      (admittedSnapshot, index)

def execute (source : Workspace) (batch : List Work) : Workspace :=
  batch.foldl (fun state work => applyWork work state) source

def workspaceStep (workspace : Workspace) (work : Work) : Workspace :=
  applyWork work workspace

/-- The useful background operation is independent of the real foreground
transition on every workspace state, not only on the worked fixture. -/
theorem foreground_refresh_commute (workspace : Workspace) :
    applyWork .refreshPremiseIndex (applyWork .foregroundBridge workspace) =
      applyWork .foregroundBridge (applyWork .refreshPremiseIndex workspace) := by
  rcases workspace with ⟨foreground, index⟩
  rfl

def semantics : ExecutionSemantics Work Workspace WorkspaceView :=
  deterministicSemantics workspaceStep observeWorkspace

def completeBagContract : Contract Work Unit (Multiset Work) where
  observer := { observe := fun batch => (batch : Multiset Work) }
  demand := { completion := .completeBag }

def parallelBatch : List Work :=
  [.foregroundBridge, .refreshPremiseIndex]

def parallelTarget : Workspace :=
  (afterBridge, selectedPremises)

theorem reference_order_reaches_parallelTarget :
    semantics.run initialWorkspace parallelBatch parallelTarget :=
  rfl

theorem swapped_order_reaches_parallelTarget :
    semantics.run initialWorkspace
      [.refreshPremiseIndex, .foregroundBridge] parallelTarget :=
  rfl

/-! ## Exact attention funding and the certified wave -/

inductive Agent where
  | foregroundChainer
  | premiseIndexer
deriving DecidableEq, Repr

def owner : Work → Agent
  | .foregroundBridge => .foregroundChainer
  | .refreshPremiseIndex => .premiseIndexer
  | .intrusiveRewind => .premiseIndexer

def unitFund (horizon : ImportanceHorizon) (agent : Agent) :
    Fund horizon Agent Nat where
  balances := Finsupp.single agent 1

/-- Both occurrences need immediate attention. -/
def shortDemand (work : Work) : Fund .shortTerm Agent Nat :=
  unitFund .shortTerm (owner work)

/-- The persistent indexer additionally needs long-term retention; the
foreground bridge is a one-shot demand. -/
def longDemand : Work → Fund .longTerm Agent Nat
  | .foregroundBridge => 0
  | .refreshPremiseIndex => unitFund .longTerm .premiseIndexer
  | .intrusiveRewind => unitFund .longTerm .premiseIndexer

def shortSource : Fund .shortTerm Agent Nat :=
  batchDemand shortDemand parallelBatch

def longSource : Fund .longTerm Agent Nat :=
  batchDemand longDemand parallelBatch

def shortSeparation :
    BatchSeparation (Fund .shortTerm Agent Nat)
      shortDemand shortSource parallelBatch where
  frame := 0
  source_eq := by simp [shortSource]

def longSeparation :
    BatchSeparation (Fund .longTerm Agent Nat)
      longDemand longSource parallelBatch where
  frame := 0
  source_eq := by simp [longSource]

/-- The exact two-occurrence batch is candidate-invariant, operationally
serializable, and separately funded in both attention instruments. -/
def certified :
    CertifiedBatch completeBagContract semantics initialWorkspace
      parallelTarget (ImportanceAccount Agent Nat)
      (fun work => (shortDemand work, longDemand work))
      (shortSource, longSource) parallelBatch where
  nonempty := by decide
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := by
    constructor
    · exact reference_order_reaches_parallelTarget
    · intro ordering permutation
      have pairOrdering :
          ordering = [.foregroundBridge, .refreshPremiseIndex] ∨
            ordering = [.refreshPremiseIndex, .foregroundBridge] :=
        List.perm_pair.mp (by simpa [parallelBatch] using permutation)
      rcases pairOrdering with rfl | rfl
      · exact ⟨parallelTarget, reference_order_reaches_parallelTarget, rfl⟩
      · exact ⟨parallelTarget, swapped_order_reaches_parallelTarget, rfl⟩
  resources := pairFunding shortSeparation longSeparation

/-! The foreground/index refresh square is not fixture-specific. -/

def parallelTargetAt (source : Workspace) : Workspace :=
  applyWork .refreshPremiseIndex (applyWork .foregroundBridge source)

/-- Every workspace state admits the same foreground/indexer batch.  The
certificate is source-parametric because the operations commute globally and
the two attention accounts are occurrence-indexed rather than state-minted. -/
def certifiedAt (source : Workspace) :
    CertifiedBatch completeBagContract semantics source
      (parallelTargetAt source) (ImportanceAccount Agent Nat)
      (fun work => (shortDemand work, longDemand work))
      (shortSource, longSource) parallelBatch where
  nonempty := by decide
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := by
    constructor
    · rfl
    · intro ordering permutation
      have pairOrdering :
          ordering = [.foregroundBridge, .refreshPremiseIndex] ∨
            ordering = [.refreshPremiseIndex, .foregroundBridge] :=
        List.perm_pair.mp (by simpa [parallelBatch] using permutation)
      rcases pairOrdering with rfl | rfl
      · exact ⟨parallelTargetAt source, rfl, rfl⟩
      · refine ⟨parallelTargetAt source, ?_, rfl⟩
        simpa [semantics, deterministicSemantics, workspaceStep,
          parallelTargetAt] using foreground_refresh_commute source
  resources := pairFunding shortSeparation longSeparation

def role (occurrence : Fin parallelBatch.length) : WorkRole :=
  if occurrence.val = 0 then .foreground else .background

def guidance : Guidance (Fin parallelBatch.length) Nat Nat where
  value occurrence :=
    if occurrence.val = 0 then some 10 else some 6
  priorityOf := id
  fallback _occurrence := 0

def wave : Wave completeBagContract semantics initialWorkspace parallelTarget
    shortDemand longDemand shortSource longSource parallelBatch Nat Nat where
  certified := certified
  role := role
  guidance := guidance
  foregroundPresent := ⟨⟨0, by decide⟩, rfl⟩
  backgroundPresent := ⟨⟨1, by decide⟩, rfl⟩

/-- The actual foreground transition and the actual premise-index refresh earn
bulk eligibility without erasing either cognitive role or attention account. -/
theorem real_foreground_and_background_run_together :
    (wave.certified.plan .general).activation = .bulk ∧
      foregroundPolicy.step admittedSnapshot
        (.requested () (selectedOccurrenceAt 0)) afterBridge
        (selectedOccurrenceAt 0) ∧
      (execute initialWorkspace parallelBatch).1 = afterBridge ∧
      true ∈ (execute initialWorkspace parallelBatch).2 ∧
      Nonempty (BatchSeparation (Fund .shortTerm Agent Nat)
        shortDemand shortSource parallelBatch) ∧
      Nonempty (BatchSeparation (Fund .longTerm Agent Nat)
        longDemand longSource parallelBatch) := by
  exact ⟨wave.completeBag_dispatches_bulk rfl,
    admitted_bridge_fires_exact_tick, rfl, requiredPremise_selected,
    ⟨wave.shortTermResources⟩, ⟨wave.longTermResources⟩⟩

/-! ## Negative control: an organizer that writes the foreground store -/

def intrusiveBatch : List Work :=
  [.foregroundBridge, .intrusiveRewind]

def intrusiveReferenceTarget : Workspace :=
  (admittedSnapshot, ∅)

theorem intrusive_reference_run :
    semantics.run initialWorkspace intrusiveBatch intrusiveReferenceTarget :=
  rfl

/-- Separate scheduling lanes are available even for the bad batch.  The
remaining obstruction is semantic, not a missing scalar budget. -/
def laneDemand : Work → Nat × Nat
  | .foregroundBridge => (1, 0)
  | .refreshPremiseIndex => (0, 1)
  | .intrusiveRewind => (0, 1)

def intrusiveLaneSeparation :
    BatchSeparation (Nat × Nat) laneDemand (1, 1) intrusiveBatch where
  frame := 0
  source_eq := rfl

/-- Foreground-then-rewind loses the tick; rewind-then-foreground retains it.
The two schedules differ at the declared progress observer. -/
theorem intrusive_not_serializable :
    ¬ semantics.SerializesTo initialWorkspace intrusiveBatch
      intrusiveReferenceTarget := by
  intro serializable
  obtain ⟨target, targetRun, sameObservation⟩ :=
    serializable.2 [.intrusiveRewind, .foregroundBridge]
      (List.Perm.swap Work.foregroundBridge Work.intrusiveRewind [])
  have targetIsAfterBridge : target = (afterBridge, ∅) := by
    simpa [semantics, deterministicSemantics, workspaceStep, execute,
      applyWork, initialWorkspace, afterBridge] using targetRun
  have sameObservationAtBridge := sameObservation
  rw [targetIsAfterBridge] at sameObservationAtBridge
  have lengthEqual :
      afterBridge.processed.length = admittedSnapshot.processed.length := by
    simpa [semantics, deterministicSemantics, observeWorkspace,
      intrusiveReferenceTarget] using
        congrArg Prod.fst sameObservationAtBridge
  have activationLength :=
    congrArg List.length first_activation_updates_real_store.2
  simp at activationLength
  omega

/-- Complete-bag demand and an exact two-lane budget still cannot turn a
foreground-writing organizer into a parallel wave. -/
theorem resources_do_not_grant_intrusive_wave :
    Nonempty
        (BatchSeparation (Nat × Nat) laneDemand (1, 1) intrusiveBatch) ∧
      ¬ Nonempty
        (CertifiedBatch completeBagContract semantics initialWorkspace
          intrusiveReferenceTarget (Nat × Nat) laneDemand (1, 1)
          intrusiveBatch) := by
  constructor
  · exact ⟨intrusiveLaneSeparation⟩
  · rintro ⟨badWave⟩
    exact intrusive_not_serializable badWave.executionSerializable

/-! ## Entry into the generic semantic parallel backend -/

def attentionDemand (work : Work) : ImportanceAccount Agent Nat :=
  (shortDemand work, longDemand work)

def attentionInventory (_workspace : Workspace) :
    ImportanceAccount Agent Nat :=
  (shortSource, longSource)

/-- The reusable pair bridge turns the same wave certificates into a
conservative semantic backend. -/
def parallelBackend :
    ParallelBackend (deterministicTheory workspaceStep observeWorkspace) :=
  certifiedPairBackend completeBagContract workspaceStep observeWorkspace
    (ImportanceAccount Agent Nat) attentionDemand attentionInventory

theorem useful_pair_admitted_by_parallel_backend :
    parallelBackend.Admits .foregroundBridge .refreshPremiseIndex
      initialWorkspace := by
  exact ⟨parallelTarget, ⟨certified⟩⟩

/-- The intrusive pair cannot enter even the semantic backend.  An executable
NIK article will additionally need a replayable checker and physical receipt;
this bridge does not manufacture either. -/
theorem intrusive_pair_refused_by_parallel_backend :
    ¬ parallelBackend.Admits .foregroundBridge .intrusiveRewind
      initialWorkspace := by
  rintro ⟨referenceTarget, ⟨badWave⟩⟩
  have referenceIsIntrusive : referenceTarget = intrusiveReferenceTarget := by
    simpa [semantics, deterministicSemantics, workspaceStep, execute,
      applyWork, initialWorkspace, intrusiveReferenceTarget] using
        badWave.executionSerializable.1
  have badSerialization := badWave.executionSerializable
  rw [referenceIsIntrusive] at badSerialization
  exact intrusive_not_serializable badSerialization

/-! ## A replayable conservative admission boundary -/

/-- The compiled backend uses a canonical event order for one proved-safe
pair.  The semantic square still validates both execution orders. -/
def CanonicalUsefulPair (first second : Work) : Prop :=
  first = .foregroundBridge ∧ second = .refreshPremiseIndex

/-- A source-parametric backend whose admitted subset is deliberately smaller
than all semantically commuting pairs and is therefore directly decidable. -/
def replayableParallelBackend :
    ParallelBackend (deterministicTheory workspaceStep observeWorkspace) where
  valuation := eventCount (deterministicTheory workspaceStep observeWorkspace)
  Admits := fun first second _source => CanonicalUsefulPair first second
  sound := by
    intro first second source admitted
    rcases admitted with ⟨rfl, rfl⟩
    exact ⟨certifiedPair_queryCoexecutible (certifiedAt source),
      additive_compatible
        (theory := deterministicTheory workspaceStep observeWorkspace)
        (Grade := Nat) (fun _work : Work => 1) Work.foregroundBridge
        Work.refreshPremiseIndex⟩

private instance workspaceRevisionDecidableEq :
    DecidableEq (deterministicTheory workspaceStep observeWorkspace).Revision :=
  inferInstanceAs (DecidableEq Work)

private instance workspaceQueryDecidableEq :
    DecidableEq (deterministicTheory workspaceStep observeWorkspace).Query :=
  inferInstanceAs (DecidableEq Unit)

def replayableAdmissionDecision
    (claim : EventClaim (deterministicTheory workspaceStep observeWorkspace)) :
    Bool :=
  decide (claim.first = Work.foregroundBridge ∧
    claim.second = Work.refreshPremiseIndex)

theorem replayableAdmissionDecision_reflects
    (claim : EventClaim (deterministicTheory workspaceStep observeWorkspace)) :
    replayableAdmissionDecision claim = true ↔
      Admitted replayableParallelBackend claim := by
  simp [replayableAdmissionDecision, Admitted, replayableParallelBackend,
    CanonicalUsefulPair]
  exact Iff.rfl

def replayableAdmission : AdmissionAuthority replayableParallelBackend :=
  ofBooleanDecision replayableAdmissionDecision
    replayableAdmissionDecision_reflects

def usefulEventClaim :
    EventClaim (deterministicTheory workspaceStep observeWorkspace) where
  first := .foregroundBridge
  second := .refreshPremiseIndex
  source := initialWorkspace
  request := ()

def intrusiveEventClaim :
    EventClaim (deterministicTheory workspaceStep observeWorkspace) where
  first := .foregroundBridge
  second := .intrusiveRewind
  source := initialWorkspace
  request := ()

theorem useful_event_claim_replays :
    replayableAdmission.checker.check usefulEventClaim () = true := by
  decide

theorem intrusive_event_claim_rejected :
    replayableAdmission.checker.check intrusiveEventClaim () = false := by
  decide

/-- Boolean replay projects back to the exact semantic admission predicate;
the checker is not merely a scheduler hint. -/
theorem useful_event_claim_is_admitted :
    Admitted replayableParallelBackend usefulEventClaim :=
  replayableAdmission.authority.sound usefulEventClaim ()
    useful_event_claim_replays

/-! ## A revision-bound operator article for the ordinary NIK frontend -/

/-- The finite physical view distinguishes authored work from the emitted
workspace observation. -/
inductive PhysicalPayload where
  | work (item : Work)
  | observed (view : WorkspaceView)
deriving DecidableEq

abbrev PhysicalSnapshot :=
  Mettapedia.GSLT.Dynamics.OperatorRealization.Snapshot
    Unit Nat PhysicalPayload

def physicalSnapshot : PhysicalSnapshot where
  storeId := ()
  revision := 0
  entries :=
    [.work .foregroundBridge, .work .refreshPremiseIndex]

def foregroundPhysicalOccurrence := physicalSnapshot.occurrenceId 0
def indexerPhysicalOccurrence := physicalSnapshot.occurrenceId 1

def physicalTargetSnapshot : PhysicalSnapshot where
  storeId := ()
  revision := 1
  entries := [.observed (observeWorkspace parallelTarget)]

def physicalPlan :
    Mettapedia.GSLT.Dynamics.OperatorRealization.OperatorPlan
      Unit Nat Unit Nat where
  id := 17
  observer := ()
  sourceBackend := ()
  targetBackend := ()
  sourceRevision := 0
  authoredOccurrences :=
    [foregroundPhysicalOccurrence, indexerPhysicalOccurrence]

def physicalDelta :
    Mettapedia.GSLT.Dynamics.OperatorRealization.Delta
      Unit Nat PhysicalPayload Nat where
  id := 23
  sourceBackend := ()
  targetBackend := ()
  sourceRevision := 0
  targetRevision := 1
  entries := physicalTargetSnapshot.occurrences

def physicalReceipt :
    Mettapedia.GSLT.Dynamics.OperatorRealization.Receipt
      Unit Nat Unit Nat Nat where
  planId := physicalPlan.id
  observer := ()
  sourceBackend := ()
  targetBackend := ()
  sourceRevision := 0
  targetRevision := 1
  deltaId := physicalDelta.id
  mode := .parallel
  authoredOccurrences := physicalPlan.authoredOccurrences
  emittedOccurrences := physicalDelta.entries.map Prod.fst

def physicalClaim :
    Claim (deterministicTheory workspaceStep observeWorkspace)
      Unit Nat PhysicalPayload Nat Nat where
  event := usefulEventClaim
  snapshot := physicalSnapshot
  plan := physicalPlan
  delta := physicalDelta
  receipt := physicalReceipt

/-- Semantic admission and the complete revision-bound operator receipt replay
together through one combined checker. -/
theorem physical_article_accepted :
    (replayChecker replayableAdmission).check physicalClaim () = true := by
  decide

theorem physical_article_has_declared_meaning :
    Meaning (backend := replayableParallelBackend) physicalClaim :=
  (authorityProjection replayableAdmission).sound physicalClaim ()
    physical_article_accepted

/-- The same article enters the ordinary statusful NIK frontend; parallel
execution does not require a privileged evaluator branch. -/
theorem physical_article_defaultNIK_accepts :
    (typedFrontend replayableAdmission).run
        ((typedFrontend replayableAdmission).encode
          (submission replayableAdmission physicalClaim ())) =
      Mettapedia.GSLT.LanguageDef.NIKDefaultProfile.SubmissionOutcome.accepted
        (Mettapedia.GSLT.LanguageDef.NIKDefaultProfile.TypedSubmission.claim
          (submission replayableAdmission physicalClaim ())) :=
  accepted_defaultRun replayableAdmission physicalClaim ()
    physical_article_accepted

def stalePhysicalClaim :=
  { physicalClaim with
    receipt := { physicalReceipt with sourceRevision := 9 } }

theorem stale_physical_article_rejected :
    (replayChecker replayableAdmission).check stalePhysicalClaim () = false := by
  decide

def reorderedPhysicalClaim :=
  { physicalClaim with
    receipt :=
      { physicalReceipt with
        authoredOccurrences :=
          [indexerPhysicalOccurrence, foregroundPhysicalOccurrence] } }

theorem reordered_physical_article_rejected :
    (replayChecker replayableAdmission).check
      reorderedPhysicalClaim () = false := by
  decide

#print axioms foreground_refresh_commute
#print axioms reference_order_reaches_parallelTarget
#print axioms swapped_order_reaches_parallelTarget
#print axioms real_foreground_and_background_run_together
#print axioms intrusive_not_serializable
#print axioms resources_do_not_grant_intrusive_wave
#print axioms useful_pair_admitted_by_parallel_backend
#print axioms intrusive_pair_refused_by_parallel_backend
#print axioms certifiedAt
#print axioms replayableAdmissionDecision_reflects
#print axioms useful_event_claim_replays
#print axioms intrusive_event_claim_rejected
#print axioms useful_event_claim_is_admitted
#print axioms physical_article_accepted
#print axioms physical_article_has_declared_meaning
#print axioms physical_article_defaultNIK_accepts
#print axioms stale_physical_article_rejected
#print axioms reordered_physical_article_rejected

end
end Mettapedia.CognitiveArchitecture.ForegroundBackgroundParallelWave
