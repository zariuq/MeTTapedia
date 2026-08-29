import Mettapedia.Cybernetics.ApproximateGeometricVisibility
import Mettapedia.GSLT.Core.ResourceAwareControl
import Mettapedia.GSLT.Dynamics.ChoiceEffectDistributiveLaws
import Mettapedia.GSLT.Dynamics.IncrementalSpaceInvariants
import Mettapedia.Machines.RevisionedOccurrenceStore
import Mathlib.Tactic

/-!
# Operational revision-bound wave admission

This module packages the evidence needed to activate one exact occurrence
batch from one live store revision.  The coordinates remain independent:

* every occurrence resolves at the captured store and revision;
* candidate observation, completion demand, operational serializability, and
  additive resource separation come from an existing certified batch;
* goal and cost factor exactly through the state observer;
* geometric value is reconstructed only within an authored error;
* a state invariant descends through that same observer and is proved at the
  source and reference target; and
* the effect handler is named explicitly as contextual or shared-state.

This is an operational revision boundary.  It is deliberately not called a
semantic-theory or NIK revision: connecting those revision notions requires a
separate currentness theorem.  Refusal leaves the exact occurrence batch
pending and carries no semantic refutation constructor.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.OperationalRevisionWaveAdmission

open Mettapedia.Cybernetics
open Mettapedia.Cybernetics.ApproximateGeometricVisibility
open Mettapedia.Cybernetics.MultiscaleGoal
open Mettapedia.Cybernetics.MultiscaleGoalCostControl
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.ContextualControlSurface
open Mettapedia.GSLT.Dynamics.IncrementalSpaceInvariants
open Mettapedia.GSLT.Dynamics.TypedValueGeometry
open Mettapedia.Machines

universe uGuard uCandidateView uState uStateView
universe uAccount uCost uValue uDelta uInvariantReceipt uAdmission

/-! ## Revision-scoped occurrences -/

/-- A payload occurrence whose identity includes a store and revision token. -/
abbrev RevisionedOccurrence
    (StoreId : Type) (Revision : Type) (Entry : Type) :=
  StoreOccurrenceId StoreId Revision × Entry

/-- One occurrence is current only when both its captured token and its
payload resolve against the live view.  Equal payloads at different logical
positions remain different occurrences. -/
structure CurrentOccurrence
    {StoreId Revision Entry : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry)
    (occurrence : RevisionedOccurrence StoreId Revision Entry) : Prop where
  token_eq : occurrence.1.read = view.readToken
  resolves : view.resolve occurrence.1 = some occurrence.2

/-- Every selected occurrence in a batch is current at the same captured
view. -/
def CurrentBatch
    {StoreId Revision Entry : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry)
    (batch : List (RevisionedOccurrence StoreId Revision Entry)) : Prop :=
  forall occurrence, occurrence ∈ batch -> CurrentOccurrence view occurrence

namespace CurrentOccurrence

variable {StoreId Revision Entry : Type}
variable [DecidableEq StoreId] [DecidableEq Revision]
variable {view : RevisionedStoreView StoreId Revision Entry}
variable {occurrence : RevisionedOccurrence StoreId Revision Entry}

/-- A genuinely changed store revision rejects every occurrence captured at
the old revision, even if an equal payload remains present. -/
theorem rejected_after_revision_change
    (current : CurrentOccurrence view occurrence)
    (nextRevision : Revision) (nextEntries : List Entry)
    (changed : nextRevision ≠ view.revision) :
    (view.replaceRevision nextRevision nextEntries).resolve occurrence.1 = none := by
  have oldRevision : occurrence.1.read.revision = view.revision :=
    congrArg StoreReadToken.revision current.token_eq
  have stale : occurrence.1.read.revision ≠ nextRevision := by
    intro same
    exact changed (same.symm.trans oldRevision)
  exact (view.replaceRevision nextRevision nextEntries).resolve_stale
    occurrence.1 stale

end CurrentOccurrence

/-- The complete enumerated occurrence list of a view is current by
construction. -/
theorem occurrences_current
    {StoreId Revision Entry : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry) :
    CurrentBatch view view.occurrences := by
  intro occurrence member
  obtain ⟨⟨entry, logicalIndex⟩, zipped, equality⟩ := List.mem_map.mp member
  subst occurrence
  refine ⟨rfl, ?_⟩
  exact view.resolve_of_mem_occurrences
    (List.mem_map.mpr ⟨(entry, logicalIndex), zipped, rfl⟩)

/-! ## Observer-visible transition invariants -/

/-- A state invariant is visible at an observer when it is exactly the
pullback of a predicate on the observer's view. -/
structure InvariantReadout
    {State : Type uState} {View : Type uStateView}
    (observe : State -> View) (invariant : State -> Prop) where
  run : View -> Prop
  agrees : forall state, run (observe state) <-> invariant state

/-- Proof-relevant evidence that one transition begins and ends inside an
invariant.  The receipt retains the route by which preservation was earned. -/
structure TransitionInvariant
    (Receipt : Type uInvariantReceipt)
    {State : Type uState} (invariant : State -> Prop)
    (source target : State) where
  receipt : Receipt
  source_holds : invariant source
  target_holds : invariant target

namespace TransitionInvariant

/-- A locally balanced fragment update supplies a global additive transition
invariant without rescanning the untouched frame. -/
def ofBalanced
    {Item : Type*} {Summary : Type*} [AddCommMonoid Summary]
    (summary : Multiset Item →+ Summary) (required : Summary)
    (update : FramedUpdate Item)
    (sourceInvariant : summary update.source = required)
    (balanced : Balanced summary update.fragment) :
    TransitionInvariant (FramedUpdate Item)
      (fun state => summary state = required)
      update.source update.target where
  receipt := update
  source_holds := sourceInvariant
  target_holds := invariant_preserved_of_balanced summary required update
    sourceInvariant balanced

end TransitionInvariant

/-! ## Explicit effect and refusal policies -/

/-- Contextual resolution occurs after isolated exploration.  Shared-state
execution is a distinct constructor because reads may already have observed
earlier writes. -/
inductive EffectHandlerPolicy (Delta : Type uDelta)
  | contextual (policy : ResolutionPolicy Delta)
  | shared

/-- Independent axes on which an operational request may be conservatively
deferred. -/
inductive RefusalAxis where
  | staleRevision
  | candidateObservation
  | completionDemand
  | serialization
  | resources
  | goalCostVisibility
  | valueAccuracy
  | invariantVisibility
  | invariantPreservation
  | handlerUnavailable
deriving DecidableEq, Repr

/-- Admission or exact deferral of one indexed occurrence batch.  A deferred
constructor retains the original `batch` in its type; it cannot return an
empty semantic answer in its place. -/
inductive AdmissionDecision
    {Item : Type*} (Admission : List Item -> Type uAdmission)
    (batch : List Item) where
  | admitted (evidence : Admission batch)
  | deferred (axis : RefusalAxis)

namespace AdmissionDecision

variable {Item : Type*} {Admission : List Item -> Type uAdmission}
variable {batch : List Item}

/-- Exact occurrence ledger at the admission boundary. -/
def ledger (decision : AdmissionDecision Admission batch) :
    FundingDecision.Ledger Item :=
  match decision with
  | .admitted _ => ⟨(batch : Multiset Item), 0⟩
  | .deferred _ => ⟨0, (batch : Multiset Item)⟩

/-- Admission and deferral both account for every requested occurrence. -/
theorem ledger_accounts (decision : AdmissionDecision Admission batch) :
    decision.ledger.executed + decision.ledger.pending =
      (batch : Multiset Item) := by
  cases decision <;> simp [ledger]

/-- Every refusal axis leaves the exact request pending. -/
theorem deferred_pending (axis : RefusalAxis) :
    (AdmissionDecision.deferred (Admission := Admission) (batch := batch)
      axis).ledger.pending = (batch : Multiset Item) :=
  rfl

end AdmissionDecision

/-! ## The operational admission crown -/

/-- The state observer packaged in an execution semantics. -/
def stateObserver
    {Item : Type*} {State : Type uState} {View : Type uStateView}
    (semantics : ExecutionSemantics Item State View) : Observer State View where
  observe := semantics.observe

/-- One exact, revision-current, observer-relative, resource-certified wave.

The structure is intentionally an intersection of evidence.  Approximate
value can guide a plan but is not an input to `CertifiedBatch.plan`; the
effect policy names semantics but does not manufacture serializability; and
invariant preservation must both hold at the reference transition and
descend through the observer used for serialized alternatives. -/
structure OperationalAdmission
    {StoreId Revision Entry : Type}
    [DecidableEq StoreId] [DecidableEq Revision]
    {Guard : Type uGuard} {CandidateView : Type uCandidateView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account]
    {Cost : Type uCost} {Value : Type uValue}
    (Delta : Type uDelta) (InvariantReceipt : Type uInvariantReceipt)
    (view : RevisionedStoreView StoreId Revision Entry)
    (contract : Contract (RevisionedOccurrence StoreId Revision Entry)
      Guard CandidateView)
    (semantics : ExecutionSemantics
      (RevisionedOccurrence StoreId Revision Entry) State StateView)
    (initial referenceTarget : State)
    (demand : RevisionedOccurrence StoreId Revision Entry -> Account)
    (source : Account)
    (batch : List (RevisionedOccurrence StoreId Revision Entry))
    (problem : ProblemSpace State) (cost : State -> Cost)
    (value : State -> Value) (geometry : ValueGeometry Value)
    (error : Real) (invariant : State -> Prop) where
  current : CurrentBatch view batch
  certified : CertifiedBatch contract semantics initial referenceTarget
    Account demand source batch
  goalCostReadout :
    (goalCostFamily problem cost).ReadoutRealization semantics.observe
  valueReadout : ApproximateValueReadout geometry value
    (stateObserver semantics) error
  invariantReadout : InvariantReadout semantics.observe invariant
  invariantEvidence : TransitionInvariant InvariantReceipt invariant
    initial referenceTarget
  handler : EffectHandlerPolicy Delta

namespace OperationalAdmission

variable {StoreId Revision Entry : Type}
variable [DecidableEq StoreId] [DecidableEq Revision]
variable {Guard : Type uGuard} {CandidateView : Type uCandidateView}
variable {State : Type uState} {StateView : Type uStateView}
variable {Account : Type uAccount} [AddMonoid Account]
variable {Cost : Type uCost} {Value : Type uValue} {Delta : Type uDelta}
variable {InvariantReceipt : Type uInvariantReceipt}
variable {view : RevisionedStoreView StoreId Revision Entry}
variable {contract : Contract (RevisionedOccurrence StoreId Revision Entry)
  Guard CandidateView}
variable {semantics : ExecutionSemantics
  (RevisionedOccurrence StoreId Revision Entry) State StateView}
variable {initial referenceTarget : State}
variable {demand : RevisionedOccurrence StoreId Revision Entry -> Account}
variable {source : Account}
variable {batch : List (RevisionedOccurrence StoreId Revision Entry)}
variable {problem : ProblemSpace State} {cost : State -> Cost}
variable {value : State -> Value} {geometry : ValueGeometry Value}
variable {error : Real} {invariant : State -> Prop}

/-- Read the exact currentness proof for one retained occurrence. -/
theorem occurrence_current
    (admission : OperationalAdmission Delta InvariantReceipt view contract
      semantics initial
      referenceTarget demand source batch problem cost value geometry error
      invariant)
    {occurrence : RevisionedOccurrence StoreId Revision Entry}
    (member : occurrence ∈ batch) : CurrentOccurrence view occurrence :=
  admission.current occurrence member

/-- Replaying an admitted occurrence against a changed store revision is
rejected before payload equality can hide the stale identity. -/
theorem occurrence_rejected_after_revision_change
    (admission : OperationalAdmission Delta InvariantReceipt view contract
      semantics initial
      referenceTarget demand source batch problem cost value geometry error
      invariant)
    {occurrence : RevisionedOccurrence StoreId Revision Entry}
    (member : occurrence ∈ batch)
    (nextRevision : Revision) (nextEntries : List Entry)
    (changed : nextRevision ≠ view.revision) :
    (view.replaceRevision nextRevision nextEntries).resolve occurrence.1 = none :=
  (admission.occurrence_current member).rejected_after_revision_change
    nextRevision nextEntries changed

/-- Every ordering admitted by the exact occurrence batch reaches an
observer-equivalent state that also satisfies the declared invariant. -/
theorem every_serialized_target_satisfies_invariant
    (admission : OperationalAdmission Delta InvariantReceipt view contract
      semantics initial
      referenceTarget demand source batch problem cost value geometry error
      invariant)
    (ordering : List (RevisionedOccurrence StoreId Revision Entry))
    (permutation : ordering.Perm batch) :
    exists target, semantics.run initial ordering target /\
      invariant target := by
  obtain ⟨target, run, agrees⟩ :=
    admission.certified.executionSerializable.2 ordering permutation
  refine ⟨target, run, ?_⟩
  apply (admission.invariantReadout.agrees target).mp
  rw [agrees]
  exact (admission.invariantReadout.agrees referenceTarget).mpr
    admission.invariantEvidence.target_holds

/-- Complete-bag activation is inherited solely from the certified semantic,
schedule, and resource evidence. -/
theorem completeBag_dispatches_bulk
    (admission : OperationalAdmission Delta InvariantReceipt view contract
      semantics initial
      referenceTarget demand source batch problem cost value geometry error
      invariant)
    (complete : contract.demand.completion = .completeBag) :
    (admission.certified.plan .general).activation = .bulk :=
  admission.certified.completeBag_dispatches_bulk complete

/-- Approximate geometry supplies a two-sided advice-quality bound and no
additional activation authority. -/
theorem targetDistance_bounds
    (admission : OperationalAdmission Delta InvariantReceipt view contract
      semantics initial
      referenceTarget demand source batch problem cost value geometry error
      invariant)
    (symmetric : geometry.Symmetric) (desired : Value) (state : State) :
    geometry.distance
        (admission.valueReadout.run (semantics.observe state)) desired <=
      error + geometry.distance (value state) desired /\
    geometry.distance (value state) desired <=
      error + geometry.distance
        (admission.valueReadout.run (semantics.observe state)) desired :=
  admission.valueReadout.targetDistance_bounds symmetric desired state

end OperationalAdmission

/-! ## Positive and adversarial controls -/

namespace Canary

abbrev StoreView := RevisionedStoreView Unit Nat Unit
abbrev Candidate := RevisionedOccurrence Unit Nat Unit
abbrev State := Bool × Bool × Bool
abbrev StateView := Bool × Bool

def view0 : StoreView where
  storeId := ()
  revision := 0
  entries := [()]

def candidate : Candidate := (view0.occurrenceId 0, ())
def batch : List Candidate := [candidate]

theorem candidate_current : CurrentOccurrence view0 candidate := by
  refine ⟨rfl, ?_⟩
  change view0.resolve (view0.occurrenceId 0) = some ()
  rw [RevisionedStoreView.resolve_current]
  rfl

theorem batch_current : CurrentBatch view0 batch := by
  intro occurrence member
  simp only [batch, List.mem_singleton] at member
  subst occurrence
  exact candidate_current

def initial : State := (false, false, false)
def target : State := (true, true, true)

def run (source : State) (items : List Candidate) (result : State) : Prop :=
  source = initial /\ items = batch /\ result = target

def semantics : ExecutionSemantics Candidate State StateView where
  run := run
  observe := fun state => (state.1, state.2.1)

def completeContract : Contract Candidate Unit (Multiset Candidate) where
  observer := { observe := fun items => (items : Multiset Candidate) }
  demand := { completion := .completeBag }

def firstContract : Contract Candidate Unit (Multiset Candidate) where
  observer := { observe := fun items => (items : Multiset Candidate) }
  demand := { completion := .first }

def demand (_candidate : Candidate) : Nat := 1

def certified (contract : Contract Candidate Unit (Multiset Candidate))
    (observes : forall items,
      contract.observer.observe items = (items : Multiset Candidate)) :
    CertifiedBatch contract semantics initial target Nat demand 1 batch where
  nonempty := by decide
  candidateInvariant := by
    intro ordering permutation
    rw [observes ordering, observes batch]
    exact Quot.sound permutation
  executionSerializable := by
    constructor
    · exact ⟨rfl, rfl, rfl⟩
    · intro ordering permutation
      have ordering_eq : ordering = batch := by
        simpa [batch] using permutation
      subst ordering
      exact ⟨target, ⟨rfl, rfl, rfl⟩, rfl⟩
  resources :=
    { frame := 0
      source_eq := by simp [batch, demand, batchDemand] }

def problem : ProblemSpace State where
  preferredRegion := {state | state.1 = true}

def cost : State -> Nat := fun state => if state.2.1 then 1 else 0

def value : State -> Real := fun state => if state.2.2 then 1 else 0

/-- A cost that depends on the hidden coordinate. -/
def hiddenCost : State -> Nat := fun state => if state.2.2 then 1 else 0

noncomputable def geometry : ValueGeometry Real :=
  ValueGeometry.ofPseudoMetric Real

def goalCostReadout :
    (goalCostFamily problem cost).ReadoutRealization semantics.observe where
  run
    | .preferred => fun observed => ULift.up (observed.1 = true)
    | .cost => show StateView -> Nat from
        fun observed => if observed.2 then 1 else 0
  agrees := by
    intro policy state
    cases policy <;> rfl

/-- Seeing the goal and the structural coordinate cannot reconstruct a cost
carried only by the hidden coordinate. -/
theorem hiddenCost_not_visible :
    Not ((goalCostFamily problem hiddenCost).SupportsReadout
      semantics.observe) := by
  change Not ((goalCostFamily problem hiddenCost).SupportsReadout
    (stateObserver semantics).observe)
  rw [supports_goalCostFamily_iff]
  intro supported
  rcases supported.2 with ⟨coarseCost, recovers⟩
  have zero := recovers (false, false, false)
  have one := recovers (false, false, true)
  simp [hiddenCost, semantics, stateObserver] at zero one
  omega

noncomputable def halfValueReadout :
    ApproximateValueReadout geometry value (stateObserver semantics) (1 / 2) where
  error_nonnegative := by norm_num
  run := fun _ => 1 / 2
  agrees := by
    rintro ⟨visible, structural, hidden⟩
    cases hidden <;>
      norm_num [geometry, value, stateObserver,
        ValueGeometry.ofPseudoMetric, Real.dist_eq]

def visibleInvariant (state : State) : Prop :=
  state.1 = state.2.1

def visibleInvariantReadout :
    InvariantReadout semantics.observe visibleInvariant where
  run := fun observed => observed.1 = observed.2
  agrees := by intro state; rfl

def visibleInvariantEvidence :
    TransitionInvariant Unit visibleInvariant initial target where
  receipt := ()
  source_holds := rfl
  target_holds := rfl

abbrev AdmissionAt
    (contract : Contract Candidate Unit (Multiset Candidate))
    (source : Nat) (error : Real) (invariant : State -> Prop) :=
  OperationalAdmission Unit Unit view0 contract semantics initial target
    demand source batch problem cost value geometry error invariant

/-- Positive control: one current occurrence, an exact goal/cost view, a
radius-one-half geometric value view, a visible invariant, and explicit
contextual retention form one complete-bag admission. -/
noncomputable def admitted : AdmissionAt completeContract 1 (1 / 2)
    visibleInvariant where
  current := batch_current
  certified := certified completeContract (by intro items; rfl)
  goalCostReadout := goalCostReadout
  valueReadout := halfValueReadout
  invariantReadout := visibleInvariantReadout
  invariantEvidence := visibleInvariantEvidence
  handler := .contextual .retain

theorem admitted_bulk_and_invariant :
    (admitted.certified.plan .general).activation = .bulk /\
      exists reached, semantics.run initial batch reached /\
        visibleInvariant reached := by
  constructor
  · exact admitted.completeBag_dispatches_bulk rfl
  · exact admitted.every_serialized_target_satisfies_invariant batch
      (List.Perm.refl batch)

/-- The same semantic, resource, invariant, and value evidence under
first-witness demand remains controlled. -/
noncomputable def admittedFirst : AdmissionAt firstContract 1 (1 / 2)
    visibleInvariant where
  current := batch_current
  certified := certified firstContract (by intro items; rfl)
  goalCostReadout := goalCostReadout
  valueReadout := halfValueReadout
  invariantReadout := visibleInvariantReadout
  invariantEvidence := visibleInvariantEvidence
  handler := .contextual .retain

theorem first_witness_refuses_bulk :
    (admittedFirst.certified.plan .general).activation = .controlled :=
  admittedFirst.certified.first_remains_controlled rfl

/-- Equal payload at a new revision does not revive the old occurrence ID. -/
theorem stale_candidate_rejected :
    (view0.replaceRevision 1 [()]).resolve candidate.1 = none :=
  candidate_current.rejected_after_revision_change 1 [()] (by decide)

/-- A hidden invariant may hold at both admitted endpoints while still
failing to descend through the coarse observer. -/
def hiddenInvariant (state : State) : Prop :=
  state.2.2 = state.1

def hiddenInvariantEvidence :
    TransitionInvariant Unit hiddenInvariant initial target where
  receipt := ()
  source_holds := rfl
  target_holds := rfl

theorem hiddenInvariant_not_visible :
    Not (Nonempty (InvariantReadout semantics.observe hiddenInvariant)) := by
  rintro ⟨readout⟩
  have sourceAgreement := readout.agrees (false, false, false)
  have counterAgreement := readout.agrees (false, false, true)
  have sourceHolds : hiddenInvariant (false, false, false) := rfl
  have observedHolds : readout.run (false, false) :=
    sourceAgreement.mpr sourceHolds
  have counterFails : Not (hiddenInvariant (false, false, true)) := by
    norm_num [hiddenInvariant]
  exact counterFails (counterAgreement.mp observedHolds)

/-- All endpoint facts can hold while missing invariant descent still blocks
the integrated admission. -/
theorem hiddenInvariant_blocks_admission :
    Not (Nonempty (AdmissionAt completeContract 1 (1 / 2)
      hiddenInvariant)) := by
  rintro ⟨admission⟩
  exact hiddenInvariant_not_visible ⟨admission.invariantReadout⟩

/-- Radius one third is impossible because one observer fibre contains the
two hidden values zero and one. -/
theorem third_value_radius_impossible :
    Not (ApproximatelyVisibleAt geometry value
      (stateObserver semantics) (1 / 3)) := by
  rintro ⟨readout⟩
  have diameter := readout.fibre_distance_le_two_error
    (ValueGeometry.ofPseudoMetric_symmetric Real)
    (false, false, false) (false, false, true) rfl
  norm_num [geometry, value, ValueGeometry.ofPseudoMetric,
    Real.dist_eq] at diameter

theorem third_value_radius_blocks_admission :
    Not (Nonempty (AdmissionAt completeContract 1 (1 / 3)
      visibleInvariant)) := by
  rintro ⟨admission⟩
  exact third_value_radius_impossible ⟨admission.valueReadout⟩

/-- Visibility and invariant evidence cannot fund the exact occurrence. -/
theorem zero_budget_blocks_admission :
    Not (Nonempty (AdmissionAt completeContract 0 (1 / 2)
      visibleInvariant)) := by
  rintro ⟨admission⟩
  have equation := admission.certified.resources.source_eq
  simp [batch, demand, batchDemand] at equation
  omega

/-- Refusing the unfunded request keeps its occurrence pending verbatim. -/
def unfundedDecision :
    AdmissionDecision (fun _batch : List Candidate => Unit) batch :=
  .deferred .resources

theorem unfunded_occurrence_remains_pending :
    unfundedDecision.ledger.pending = ({candidate} : Multiset Candidate) := by
  rfl

/-- The effect constructor is semantically relevant: shared execution cannot
be reconstructed as an occurrence-preserving post-hoc contextual policy. -/
theorem shared_is_not_contextual_postprocessing :
    ChoiceEffectDistributiveLaws.isolatedIncrementAnswers ≠
      ChoiceEffectDistributiveLaws.sharedIncrementAnswers :=
  ChoiceEffectDistributiveLaws.isolated_shared_increment_answers_differ

/-- One theorem-level ledger of concrete countermodels for the independent
admission coordinates.  Each field changes or withholds one authority while
leaving meaningful neighboring evidence available. -/
structure AxisSeparationEvidence : Prop where
  staleRevision :
    (view0.replaceRevision 1 [()]).resolve candidate.1 = none
  candidateObservation :
    Not (PermutationInvariantAt
      Mettapedia.GSLT.Core.ResourceAwareControl.Canary.streamObserver.observe
      [Mettapedia.GSLT.Core.ResourceAwareControl.Canary.Job.left,
       Mettapedia.GSLT.Core.ResourceAwareControl.Canary.Job.right])
  resourcesDoNotSerialize :
    (BatchSeparation.analyze?
      Mettapedia.GSLT.Core.ResourceAwareControl.Canary.demand
      Mettapedia.GSLT.Core.ResourceAwareControl.Canary.inventory
      [Mettapedia.GSLT.Core.ResourceAwareControl.Canary.Job.left,
       Mettapedia.GSLT.Core.ResourceAwareControl.Canary.Job.right]).isSome = true /\
      Not (Mettapedia.GSLT.Core.ResourceAwareControl.Canary.appendStreamSemantics.SerializesTo
        []
        [Mettapedia.GSLT.Core.ResourceAwareControl.Canary.Job.left,
         Mettapedia.GSLT.Core.ResourceAwareControl.Canary.Job.right]
        [Mettapedia.GSLT.Core.ResourceAwareControl.Canary.Job.left,
         Mettapedia.GSLT.Core.ResourceAwareControl.Canary.Job.right])
  serializationDoesNotFund :
    Mettapedia.GSLT.Core.ResourceAwareControl.Canary.appendBagSemantics.SerializesTo
        []
        [Mettapedia.GSLT.Core.ResourceAwareControl.Canary.Job.left,
         Mettapedia.GSLT.Core.ResourceAwareControl.Canary.Job.contested]
        [Mettapedia.GSLT.Core.ResourceAwareControl.Canary.Job.left,
         Mettapedia.GSLT.Core.ResourceAwareControl.Canary.Job.contested] /\
      (BatchSeparation.analyze?
        Mettapedia.GSLT.Core.ResourceAwareControl.Canary.demand
        Mettapedia.GSLT.Core.ResourceAwareControl.Canary.inventory
        [Mettapedia.GSLT.Core.ResourceAwareControl.Canary.Job.left,
         Mettapedia.GSLT.Core.ResourceAwareControl.Canary.Job.contested]).isSome = false
  completionDemand :
    (admittedFirst.certified.plan .general).activation = .controlled
  goalCostVisibility :
    Not ((goalCostFamily problem hiddenCost).SupportsReadout
      semantics.observe)
  valueAccuracy :
    Not (ApproximatelyVisibleAt geometry value
      (stateObserver semantics) (1 / 3))
  invariantVisibility :
    Not (Nonempty (InvariantReadout semantics.observe hiddenInvariant))
  resources :
    Not (Nonempty (AdmissionAt completeContract 0 (1 / 2)
      visibleInvariant))
  deferredOccurrences :
    unfundedDecision.ledger.pending = ({candidate} : Multiset Candidate)
  handlerSemantics :
    ChoiceEffectDistributiveLaws.isolatedIncrementAnswers ≠
      ChoiceEffectDistributiveLaws.sharedIncrementAnswers

/-- The operational crown's refusal axes are witnessed as genuinely
different facts rather than constructor names alone. -/
theorem refusal_axes_are_separate : AxisSeparationEvidence where
  staleRevision := stale_candidate_rejected
  candidateObservation :=
    Mettapedia.GSLT.Core.ResourceAwareControl.Canary.stream_not_permutationInvariant
  resourcesDoNotSerialize :=
    Mettapedia.GSLT.Core.ResourceAwareControl.Canary.resources_do_not_grant_stream_serializability
  serializationDoesNotFund :=
    Mettapedia.GSLT.Core.ResourceAwareControl.Canary.bag_serializability_does_not_grant_resources
  completionDemand := first_witness_refuses_bulk
  goalCostVisibility := hiddenCost_not_visible
  valueAccuracy := third_value_radius_impossible
  invariantVisibility := hiddenInvariant_not_visible
  resources := zero_budget_blocks_admission
  deferredOccurrences := unfunded_occurrence_remains_pending
  handlerSemantics := shared_is_not_contextual_postprocessing

end Canary

/-! ## Axiom audit -/

#print axioms occurrences_current
#print axioms CurrentOccurrence.rejected_after_revision_change
#print axioms TransitionInvariant.ofBalanced
#print axioms AdmissionDecision.ledger_accounts
#print axioms OperationalAdmission.every_serialized_target_satisfies_invariant
#print axioms OperationalAdmission.completeBag_dispatches_bulk
#print axioms OperationalAdmission.targetDistance_bounds
#print axioms Canary.admitted_bulk_and_invariant
#print axioms Canary.first_witness_refuses_bulk
#print axioms Canary.stale_candidate_rejected
#print axioms Canary.hiddenCost_not_visible
#print axioms Canary.hiddenInvariant_blocks_admission
#print axioms Canary.third_value_radius_blocks_admission
#print axioms Canary.zero_budget_blocks_admission
#print axioms Canary.unfunded_occurrence_remains_pending
#print axioms Canary.shared_is_not_contextual_postprocessing
#print axioms Canary.refusal_axes_are_separate

end Mettapedia.GSLT.Dynamics.OperationalRevisionWaveAdmission
