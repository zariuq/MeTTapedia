import Mettapedia.TypeTheory.CertificateGSLTCoherentRunObservation
import Mettapedia.TypeTheory.Authority
import Mettapedia.GSLT.Core.OpenTotalityObservation
import Mettapedia.GSLT.Core.SearchStreamProductivity

/-!
# Operational search observations and semantic authority

A finite search run has two independent interpretations.  Operationally, it
may be open, budget-exhausted, closed, cancelled, or faulted.  Semantically, a
selected authority may establish a judgment, refute it, report that the
judgment lies outside its certified fragment, or retain an incomplete receipt.
This module connects those existing algebras without identifying them.

The generic trajectory layer turns each finite observation of a resumable
branching process into an exact open-search observation.  Open and exhausted
observations may retain the live snapshot and its revision; closed,
cancelled, and faulted observations cannot.  Resuming a retained snapshot is
proved equal to the corresponding later point of the same trajectory.

The certificate-GSLT specialization observes only complete checked
derivation forests.  Finding one establishes derivability by soundness alone.
In contrast, a closed run with no such forest refutes derivability only when
the candidate profile covers every checked justification.  Without that
coverage theorem the same finite closure is an authority boundary, not a
negative logical result.  Increasing a budget cannot cross this boundary;
strengthening the search authority can.

No Horn, first-order, higher-order, termination, or global finiteness
assumption is made.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CertificateGSLTSearchAuthorityBoundary

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.OpenTotalityObservation
open Mettapedia.GSLT.Core.SearchStreamProductivity
open Mettapedia.GSLT.Core.SearchControlProperties
open Mettapedia.TypeTheory.AuthorityTheory
open Mettapedia.TypeTheory.CertificateGSLTCoherentRunObservation

universe uNode uAnswer uView uBound uReceipt uFault

/-! ## Exact operational observations of a resumable trajectory -/

/-- A live residual retains the complete snapshot and evidence that work
remains.  In particular, the event prefix is not reconstructed from the
frontier. -/
structure LiveSnapshot (Node : Type uNode) (Answer : Type uAnswer) where
  snapshot : Snapshot Node Answer
  live : snapshot.frontier ≠ []

/-- Coverage for one closed observation is the exact inspected snapshot and
evidence that its frontier is empty. -/
structure ClosedSnapshot (Node : Type uNode) (Answer : Type uAnswer) where
  snapshot : Snapshot Node Answer
  closed : snapshot.frontier = []

section Trajectory

variable {Node : Type uNode} {Answer : Type uAnswer}
variable {system : BranchingSystem Node Answer}
variable {scheduler : Scheduler Node}
variable {start : Snapshot Node Answer}
variable {View : Type uView} {Bound : Type uBound}
variable {RunReceipt : Type uReceipt} {Fault : Type uFault}

/-- Capture admission means that the retained residual is exactly the
snapshot at the named trajectory revision. -/
def ExactCapture
    (trajectory : ResumableTrajectory system scheduler start)
    (residual : LiveSnapshot Node Answer) (revision : Nat) : Prop :=
  residual.snapshot = trajectory.observation revision

/-- The exact live residual at one finite observation boundary. -/
def liveAt
    (trajectory : ResumableTrajectory system scheduler start)
    (fuel : Nat) (live : (trajectory.observation fuel).frontier ≠ []) :
    LiveSnapshot Node Answer where
  snapshot := trajectory.observation fuel
  live := live

/-- The exact coverage witness at one finite observation boundary. -/
def closedAt
    (trajectory : ResumableTrajectory system scheduler start)
    (fuel : Nat) (closed : (trajectory.observation fuel).frontier = []) :
    ClosedSnapshot Node Answer where
  snapshot := trajectory.observation fuel
  closed := closed

/-- Existing open-totality observations specialized to exact resumable
trajectories. -/
abbrev TrajectoryObservation
    (trajectory : ResumableTrajectory system scheduler start)
    (View : Type uView) (Bound : Type uBound) (RunReceipt : Type uReceipt)
    (Fault : Type uFault) :=
  Observation View (LiveSnapshot Node Answer) Nat
    (ClosedSnapshot Node Answer) Bound RunReceipt Fault (ExactCapture trajectory)

/-- A cooperative open observation retains its exact live residual. -/
def observeOpenAt
    (trajectory : ResumableTrajectory system scheduler start)
    (observer : EventObserver Node Answer View)
    (fuel : Nat) (live : (trajectory.observation fuel).frontier ≠ []) :
    TrajectoryObservation trajectory View Bound RunReceipt Fault :=
  Observation.openCaptured
    (observer.observeList (trajectory.observation fuel).events)
    (liveAt trajectory fuel live) fuel rfl

/-- Budget exhaustion remains distinct from closure and may retain the same
exact live residual for later resumption. -/
def observeExhaustedAt
    (trajectory : ResumableTrajectory system scheduler start)
    (observer : EventObserver Node Answer View)
    (fuel : Nat) (live : (trajectory.observation fuel).frontier ≠ [])
    (bound : Bound) (receipt : RunReceipt) :
    TrajectoryObservation trajectory View Bound RunReceipt Fault :=
  Observation.exhaustedCaptured
    (observer.observeList (trajectory.observation fuel).events)
    bound receipt (liveAt trajectory fuel live) fuel rfl

/-- A closed observation carries inspected coverage and exports no residual. -/
def observeClosedAt
    (trajectory : ResumableTrajectory system scheduler start)
    (observer : EventObserver Node Answer View)
    (fuel : Nat) (closed : (trajectory.observation fuel).frontier = []) :
    TrajectoryObservation trajectory View Bound RunReceipt Fault :=
  Observation.withoutCapture
    (observer.observeList (trajectory.observation fuel).events)
    (.closed (closedAt trajectory fuel closed))

/-- Cancellation preserves the finite event prefix but grants no capture. -/
def observeCancelledAt
    (trajectory : ResumableTrajectory system scheduler start)
    (observer : EventObserver Node Answer View) (fuel : Nat) :
    TrajectoryObservation trajectory View Bound RunReceipt Fault :=
  Observation.withoutCapture
    (observer.observeList (trajectory.observation fuel).events) .cancelled

/-- A resource fault preserves the finite event prefix and exact fault
payload, but grants no capture. -/
def observeFaultAt
    (trajectory : ResumableTrajectory system scheduler start)
    (observer : EventObserver Node Answer View) (fuel : Nat) (fault : Fault) :
    TrajectoryObservation trajectory View Bound RunReceipt Fault :=
  Observation.withoutCapture
    (observer.observeList (trajectory.observation fuel).events)
    (.resourceFault fault)

@[simp] theorem observeOpenAt_resume?
    (trajectory : ResumableTrajectory system scheduler start)
    (observer : EventObserver Node Answer View)
    (fuel : Nat) (live : (trajectory.observation fuel).frontier ≠ []) :
    (observeOpenAt (Bound := Bound) (RunReceipt := RunReceipt) (Fault := Fault)
      trajectory observer fuel live).resume? =
      some (liveAt trajectory fuel live, fuel) :=
  rfl

@[simp] theorem observeExhaustedAt_resume?
    (trajectory : ResumableTrajectory system scheduler start)
    (observer : EventObserver Node Answer View)
    (fuel : Nat) (live : (trajectory.observation fuel).frontier ≠ [])
    (bound : Bound) (receipt : RunReceipt) :
    (observeExhaustedAt (Fault := Fault) trajectory observer fuel live
      bound receipt).resume? = some (liveAt trajectory fuel live, fuel) :=
  rfl

/-- Resuming the retained snapshot computes the later point of the same
trajectory exactly; it does not restart from the roots. -/
theorem liveAt_resumes_exactly
    (trajectory : ResumableTrajectory system scheduler start)
    (fuel extra : Nat)
    (live : (trajectory.observation fuel).frontier ≠ []) :
    run system scheduler extra (liveAt trajectory fuel live).snapshot =
      trajectory.observation (fuel + extra) := by
  exact (trajectory.resume fuel extra).symm

@[simp] theorem observeClosedAt_resume?
    (trajectory : ResumableTrajectory system scheduler start)
    (observer : EventObserver Node Answer View)
    (fuel : Nat) (closed : (trajectory.observation fuel).frontier = []) :
    (observeClosedAt (Bound := Bound) (RunReceipt := RunReceipt) (Fault := Fault)
      trajectory observer fuel closed).resume? = none :=
  rfl

@[simp] theorem observeCancelledAt_resume?
    (trajectory : ResumableTrajectory system scheduler start)
    (observer : EventObserver Node Answer View) (fuel : Nat) :
    (observeCancelledAt (Bound := Bound) (RunReceipt := RunReceipt) (Fault := Fault)
      trajectory observer fuel).resume? = none :=
  rfl

@[simp] theorem observeFaultAt_resume?
    (trajectory : ResumableTrajectory system scheduler start)
    (observer : EventObserver Node Answer View) (fuel : Nat) (fault : Fault) :
    (observeFaultAt (Bound := Bound) (RunReceipt := RunReceipt)
      trajectory observer fuel fault).resume? = none :=
  rfl

/-- Closed absence is obtained only when the selected observer saw no views
and the execution frontier was inspected empty. -/
theorem observeClosedAt_establishesClosedAbsence
    (trajectory : ResumableTrajectory system scheduler start)
    (observer : EventObserver Node Answer View)
    (fuel : Nat) (closed : (trajectory.observation fuel).frontier = [])
    (noViews : observer.observeList
      (trajectory.observation fuel).events = []) :
    Observation.EstablishesClosedAbsence
      (observeClosedAt (Bound := Bound) (RunReceipt := RunReceipt) (Fault := Fault)
        trajectory observer fuel closed) := by
  exact ⟨noViews, closedAt trajectory fuel closed, rfl⟩

/-- Even an empty observed prefix cannot turn budget exhaustion into closed
absence. -/
theorem observeExhaustedAt_not_closedAbsence
    (trajectory : ResumableTrajectory system scheduler start)
    (observer : EventObserver Node Answer View)
    (fuel : Nat) (live : (trajectory.observation fuel).frontier ≠ [])
    (bound : Bound) (receipt : RunReceipt) :
    ¬ Observation.EstablishesClosedAbsence
      (observeExhaustedAt (Fault := Fault) trajectory observer fuel live
        bound receipt) := by
  rintro ⟨_, coverage, equality⟩
  cases equality

/-- Cancellation is an operational interruption, never a closed-absence
certificate. -/
theorem observeCancelledAt_not_closedAbsence
    (trajectory : ResumableTrajectory system scheduler start)
    (observer : EventObserver Node Answer View) (fuel : Nat) :
    ¬ Observation.EstablishesClosedAbsence
      (observeCancelledAt (Bound := Bound) (RunReceipt := RunReceipt)
        (Fault := Fault) trajectory observer fuel) := by
  rintro ⟨_, coverage, equality⟩
  cases equality

/-- A resource fault is likewise constructor-distinct from closure. -/
theorem observeFaultAt_not_closedAbsence
    (trajectory : ResumableTrajectory system scheduler start)
    (observer : EventObserver Node Answer View) (fuel : Nat) (fault : Fault) :
    ¬ Observation.EstablishesClosedAbsence
      (observeFaultAt (Bound := Bound) (RunReceipt := RunReceipt)
        trajectory observer fuel fault) := by
  rintro ⟨_, coverage, equality⟩
  cases equality

end Trajectory

/-! ## Complete certificate derivations as the selected observation -/

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.TypeTheory.CertificateGSLTScheduledHistory
open Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration
open Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration.ScheduledSearchProfile

/-- A retained search node yields a checked derivation forest exactly when
its remaining obligation list is empty. -/
def completeDerivation?
    {definition : ValidatedCalculusLanguageDef} {roots : GoalState} :
    ScheduledSearchNode definition roots ->
      Option (DerivationList definition roots)
  | ⟨[], history⟩ => some (scheduledPathToDerivationList history)
  | ⟨_ :: _, _⟩ => none

/-- Observe only completed checked derivation forests.  Intermediate search
nodes remain present in the underlying snapshot but are hidden from this
logical-result observer. -/
def completedDerivationObserver
    (definition : ValidatedCalculusLanguageDef) (roots : GoalState) :
    EventObserver (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)
      (DerivationList definition roots) where
  observe event := completeDerivation? event.value

/-- Chronological complete results visible in one finite search snapshot. -/
def completedDerivations
    {definition : ValidatedCalculusLanguageDef} {roots : GoalState}
    (snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)) :
    List (DerivationList definition roots) :=
  (completedDerivationObserver definition roots).observeList snapshot.events

@[simp] theorem completeDerivation?_follow_complete
    {definition : ValidatedCalculusLanguageDef} {roots : GoalState}
    (path : ScheduledProofSearchPath definition roots []) :
    completeDerivation? ((initialNode definition roots).follow path) =
      some (scheduledPathToDerivationList path) := by
  rfl

/-- An emitted complete path contributes its reconstructed checked
derivation forest to the selected observation. -/
theorem completedDerivation_mem_of_complete_emission
    {definition : ValidatedCalculusLanguageDef} {roots : GoalState}
    (path : ScheduledProofSearchPath definition roots [])
    {snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)}
    (member :
      (⟨(initialNode definition roots).follow path,
          (initialNode definition roots).follow path⟩ :
        Emission (ScheduledSearchNode definition roots)
          (ScheduledSearchNode definition roots)) ∈ snapshot.events) :
    scheduledPathToDerivationList path ∈ completedDerivations snapshot := by
  apply List.mem_filterMap.mpr
  exact ⟨_, member, completeDerivation?_follow_complete path⟩

/-! ## The derivability authority -/

/-- The semantic judgment checked by certificate search is existence of a
checked derivation forest for the selected obligation list. -/
def derivabilityAuthority
    (definition : ValidatedCalculusLanguageDef) : Authority GoalState where
  Holds roots := Nonempty (DerivationList definition roots)
  Evidence roots := DerivationList definition roots
  Obstruction roots := PLift (¬ Nonempty (DerivationList definition roots))
  evidenceSound := by
    intro roots derivations
    exact Nonempty.intro derivations
  obstructionSound := by
    intro roots obstruction derivable
    exact obstruction.down derivable

/-- A completed result retains both its checked derivation and the finite
observation in which it occurred. -/
structure EstablishedAt
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat) where
  derivations : DerivationList definition roots
  observed : derivations ∈ completedDerivations
    ((scheduledTrajectory profile roots scheduler).observation fuel)

/-- Sound discovery alone promotes a completed certificate to semantic
establishment.  No search-completeness assumption is needed. -/
def EstablishedAt.toOutcome
    {definition : ValidatedCalculusLanguageDef}
    {profile : ScheduledSearchProfile definition} {roots : GoalState}
    {scheduler : Scheduler (ScheduledSearchNode definition roots)}
    {fuel : Nat} {Boundary : Type*} {Incomplete : Type*}
    (established : EstablishedAt profile roots scheduler fuel) :
    AuthorizedOutcome (derivabilityAuthority definition) Boundary Incomplete
      roots :=
  .established established.derivations

@[simp] theorem EstablishedAt.toOutcome_asBool
    {definition : ValidatedCalculusLanguageDef}
    {profile : ScheduledSearchProfile definition} {roots : GoalState}
    {scheduler : Scheduler (ScheduledSearchNode definition roots)}
    {fuel : Nat} {Boundary : Type*} {Incomplete : Type*}
    (established : EstablishedAt profile roots scheduler fuel) :
    (established.toOutcome (Boundary := Boundary)
      (Incomplete := Incomplete)).asBool = some true :=
  rfl

/-! ## Coverage is an authority theorem, not a budget -/

/-- Candidate generation covers the selected judgment when every checked
justification has at least one admitted operational schedule. -/
def JustificationCompleteAt
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState) : Prop :=
  forall derivations : DerivationList definition roots,
    profile.CoversJustification derivations

/-- Global one-step completeness is sufficient, but not required, for
judgment-local justification coverage. -/
theorem justificationCompleteAt_of_locallyComplete
    {definition : ValidatedCalculusLanguageDef}
    {profile : ScheduledSearchProfile definition}
    (complete : profile.LocallyComplete) (roots : GoalState) :
    JustificationCompleteAt profile roots := by
  intro derivations
  exact coversJustification_of_locallyComplete complete derivations

/-- If breadth-first execution has genuinely closed, an emitted event found
at any other finite fuel is already in the closed snapshot. -/
theorem emitted_mem_of_breadthFirst_closed
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (closedFuel : Nat)
    (closed :
      ((scheduledTrajectory profile roots Scheduler.breadthFirst).observation
        closedFuel).frontier = [])
    {event : Emission (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)}
    {witnessFuel : Nat}
    (member : event ∈
      ((scheduledTrajectory profile roots Scheduler.breadthFirst).observation
        witnessFuel).events) :
    event ∈
      ((scheduledTrajectory profile roots Scheduler.breadthFirst).observation
        closedFuel).events := by
  have bounded : witnessFuel <= witnessFuel + closedFuel := by omega
  have eventPrefix :
      ((scheduledTrajectory profile roots Scheduler.breadthFirst).observation
        witnessFuel).events.IsPrefix
      ((scheduledTrajectory profile roots Scheduler.breadthFirst).observation
        (witnessFuel + closedFuel)).events :=
    scheduled_events_mono profile roots Scheduler.breadthFirst bounded
  have laterMember := List.IsPrefix.mem member eventPrefix
  have stable := ResumableTrajectory.observation_constant_after_completion
    (scheduledTrajectory profile roots Scheduler.breadthFirst)
    closedFuel witnessFuel closed
  have reordered :
      (scheduledTrajectory profile roots Scheduler.breadthFirst).observation
          (witnessFuel + closedFuel) =
        (scheduledTrajectory profile roots Scheduler.breadthFirst).observation
          closedFuel := by
    simpa [Nat.add_comm] using stable
  rw [reordered] at laterMember
  exact laterMember

/-- Closed finite execution plus justification coverage turns absence of a
completed observed certificate into a sound obstruction. -/
theorem no_derivation_of_closed_complete_search
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (complete : JustificationCompleteAt profile roots) (fuel : Nat)
    (closed :
      ((scheduledTrajectory profile roots Scheduler.breadthFirst).observation
        fuel).frontier = [])
    (noCompleted : completedDerivations
      ((scheduledTrajectory profile roots Scheduler.breadthFirst).observation
        fuel) = []) :
    ¬ Nonempty (DerivationList definition roots) := by
  rintro ⟨derivations⟩
  obtain ⟨path, admitted, replay, witnessFuel, emitted⟩ :=
    breadthFirst_emits_coveredJustification profile derivations
      (complete derivations)
  have emittedAtClosure := emitted_mem_of_breadthFirst_closed
    profile roots fuel closed emitted
  have observed := completedDerivation_mem_of_complete_emission path emittedAtClosure
  have noMember :
      scheduledPathToDerivationList path ∉ completedDerivations
        ((scheduledTrajectory profile roots Scheduler.breadthFirst).observation
          fuel) := by
    rw [noCompleted]
    exact List.not_mem_nil
  exact noMember (by
    simpa only [scheduledTrajectory_observation] using observed)

/-- A closed finite run whose candidate profile lacks a coverage theorem is
an authority boundary.  The payload retains the exact closure and absence
evidence needed by a later authority upgrade. -/
structure CoverageBoundary
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState) where
  fuel : Nat
  closed :
    ((scheduledTrajectory profile roots Scheduler.breadthFirst).observation
      fuel).frontier = []
  noCompleted : completedDerivations
    ((scheduledTrajectory profile roots Scheduler.breadthFirst).observation
      fuel) = []

/-- Before coverage is supplied, a closed silent run reports an explicit
authority boundary rather than a false negative. -/
def CoverageBoundary.uncertifiedOutcome
    {definition : ValidatedCalculusLanguageDef}
    {profile : ScheduledSearchProfile definition} {roots : GoalState}
    {Incomplete : Type*}
    (boundary : CoverageBoundary profile roots) :
    AuthorizedOutcome (derivabilityAuthority definition)
      (CoverageBoundary profile roots) Incomplete roots :=
  .outsideFragment boundary

/-- Supplying justification coverage converts the exact same closure receipt
into a checked obstruction. -/
def CoverageBoundary.obstruction
    {definition : ValidatedCalculusLanguageDef}
    {profile : ScheduledSearchProfile definition} {roots : GoalState}
    (boundary : CoverageBoundary profile roots)
    (complete : JustificationCompleteAt profile roots) :
    (derivabilityAuthority definition).Obstruction roots :=
  ⟨no_derivation_of_closed_complete_search profile roots complete boundary.fuel
    boundary.closed boundary.noCompleted⟩

/-- The coverage-certified negative result. -/
def CoverageBoundary.certifiedOutcome
    {definition : ValidatedCalculusLanguageDef}
    {profile : ScheduledSearchProfile definition} {roots : GoalState}
    {Incomplete : Type*}
    (boundary : CoverageBoundary profile roots)
    (complete : JustificationCompleteAt profile roots) :
    AuthorizedOutcome (derivabilityAuthority definition)
      (CoverageBoundary profile roots) Incomplete roots :=
  .refuted (boundary.obstruction complete)

@[simp] theorem CoverageBoundary.uncertifiedOutcome_asBool
    {definition : ValidatedCalculusLanguageDef}
    {profile : ScheduledSearchProfile definition} {roots : GoalState}
    {Incomplete : Type*}
    (boundary : CoverageBoundary profile roots) :
    (boundary.uncertifiedOutcome (Incomplete := Incomplete)).asBool = none :=
  rfl

@[simp] theorem CoverageBoundary.certifiedOutcome_asBool
    {definition : ValidatedCalculusLanguageDef}
    {profile : ScheduledSearchProfile definition} {roots : GoalState}
    {Incomplete : Type*}
    (boundary : CoverageBoundary profile roots)
    (complete : JustificationCompleteAt profile roots) :
    (boundary.certifiedOutcome (Incomplete := Incomplete) complete).asBool =
      some false :=
  rfl

/-- Adding a coverage theorem is an authority refinement from boundary to
refutation. -/
def CoverageBoundary.authorityUpgrade
    {definition : ValidatedCalculusLanguageDef}
    {profile : ScheduledSearchProfile definition} {roots : GoalState}
    {Incomplete : Type*}
    (boundary : CoverageBoundary profile roots)
    (complete : JustificationCompleteAt profile roots) :
    Outcome.AuthorityRefinementEvidence
      (boundary.uncertifiedOutcome (Incomplete := Incomplete))
      (boundary.certifiedOutcome (Incomplete := Incomplete) complete) :=
  .outsideRefuted boundary (boundary.obstruction complete)

/-- No increase of the execution budget can reinterpret missing coverage as
a checked refutation. -/
theorem CoverageBoundary.no_budget_upgrade
    {definition : ValidatedCalculusLanguageDef}
    {profile : ScheduledSearchProfile definition} {roots : GoalState}
    {Incomplete : Type*}
    (boundary : CoverageBoundary profile roots)
    (complete : JustificationCompleteAt profile roots) :
    ¬ Outcome.BudgetRefines
      (boundary.uncertifiedOutcome (Incomplete := Incomplete))
      (boundary.certifiedOutcome (Incomplete := Incomplete) complete) := by
  intro refinement
  cases refinement

/-! ## Each operational stop enters the authority algebra honestly -/

section OperationalOutcomes

variable {Bound : Type uBound} {RunReceipt : Type uReceipt}
variable {Fault : Type uFault}

/-- The exact observation type for one scheduled certificate-search
trajectory and its complete-derivation observer. -/
abbrev ScheduledObservation
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (Bound : Type uBound) (RunReceipt : Type uReceipt)
    (Fault : Type uFault) :=
  TrajectoryObservation (scheduledTrajectory profile roots scheduler)
    (DerivationList definition roots) Bound RunReceipt Fault

/-- A cooperative open stop is a semantic incomplete result containing its
exact resumable observation. -/
def openSearchOutcome
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat)
    (live : ((scheduledTrajectory profile roots scheduler).observation fuel).frontier
      ≠ []) :
    AuthorizedOutcome (derivabilityAuthority definition)
      (CoverageBoundary profile roots)
      (ScheduledObservation profile roots scheduler Bound RunReceipt Fault)
      roots :=
  .incomplete <| observeOpenAt
    (scheduledTrajectory profile roots scheduler)
    (completedDerivationObserver definition roots) fuel live

/-- A budget stop is likewise incomplete, while retaining both its resource
receipt and exact resumable frontier. -/
def exhaustedSearchOutcome
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat)
    (live : ((scheduledTrajectory profile roots scheduler).observation fuel).frontier
      ≠ []) (bound : Bound) (receipt : RunReceipt) :
    AuthorizedOutcome (derivabilityAuthority definition)
      (CoverageBoundary profile roots)
      (ScheduledObservation profile roots scheduler Bound RunReceipt Fault)
      roots :=
  .incomplete <| observeExhaustedAt
    (scheduledTrajectory profile roots scheduler)
    (completedDerivationObserver definition roots) fuel live bound receipt

@[simp] theorem openSearchOutcome_asBool
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat)
    (live : ((scheduledTrajectory profile roots scheduler).observation fuel).frontier
      ≠ []) :
    (openSearchOutcome (Bound := Bound) (RunReceipt := RunReceipt)
      (Fault := Fault) profile roots scheduler fuel live).asBool = none :=
  rfl

@[simp] theorem exhaustedSearchOutcome_asBool
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat)
    (live : ((scheduledTrajectory profile roots scheduler).observation fuel).frontier
      ≠ []) (bound : Bound) (receipt : RunReceipt) :
    (exhaustedSearchOutcome (Fault := Fault) profile roots scheduler fuel live
      bound receipt).asBool = none :=
  rfl

/-- Pending observations remain safely retained and are not executable as
checked positive results. -/
theorem openSearchOutcome_control_readouts
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat)
    (live : ((scheduledTrajectory profile roots scheduler).observation fuel).frontier
      ≠ []) :
    (openSearchOutcome (Bound := Bound) (RunReceipt := RunReceipt)
        (Fault := Fault) profile roots scheduler fuel live).safeRetain = true /\
      (openSearchOutcome (Bound := Bound) (RunReceipt := RunReceipt)
        (Fault := Fault) profile roots scheduler fuel live).executable = false :=
  ⟨rfl, rfl⟩

theorem exhaustedSearchOutcome_control_readouts
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat)
    (live : ((scheduledTrajectory profile roots scheduler).observation fuel).frontier
      ≠ []) (bound : Bound) (receipt : RunReceipt) :
    (exhaustedSearchOutcome (Fault := Fault) profile roots scheduler fuel live
        bound receipt).safeRetain = true /\
      (exhaustedSearchOutcome (Fault := Fault) profile roots scheduler fuel live
        bound receipt).executable = false :=
  ⟨rfl, rfl⟩

/-- A proof discovered after exact resumption is a budget refinement from
incomplete to established, not an authority change. -/
def exhaustedToEstablished
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel extra : Nat)
    (live : ((scheduledTrajectory profile roots scheduler).observation fuel).frontier
      ≠ []) (bound : Bound) (receipt : RunReceipt)
    (established : EstablishedAt profile roots scheduler (fuel + extra)) :
    Outcome.BudgetRefinementEvidence
      (exhaustedSearchOutcome (Fault := Fault) profile roots scheduler fuel live
        bound receipt)
      (established.toOutcome
        (Boundary := CoverageBoundary profile roots)
        (Incomplete := ScheduledObservation profile roots scheduler Bound
          RunReceipt Fault)) :=
  .incompleteEstablished _ established.derivations

/-- Cancellation is outside the semantic outcome sum.  Its exact observation
is instead the failure payload of `RunResult`. -/
def cancelledSearchResult
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat) :
    RunResult (ScheduledObservation profile roots scheduler Bound RunReceipt Fault)
      (AuthorizedOutcome (derivabilityAuthority definition)
        (CoverageBoundary profile roots)
        (ScheduledObservation profile roots scheduler Bound RunReceipt Fault)
        roots) :=
  .fault <| observeCancelledAt
    (scheduledTrajectory profile roots scheduler)
    (completedDerivationObserver definition roots) fuel

/-- A resource fault follows the same outer operational channel. -/
def faultedSearchResult
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat) (fault : Fault) :
    RunResult (ScheduledObservation profile roots scheduler Bound RunReceipt Fault)
      (AuthorizedOutcome (derivabilityAuthority definition)
        (CoverageBoundary profile roots)
        (ScheduledObservation profile roots scheduler Bound RunReceipt Fault)
        roots) :=
  .fault <| observeFaultAt
    (scheduledTrajectory profile roots scheduler)
    (completedDerivationObserver definition roots) fuel fault

@[simp] theorem cancelledSearchResult_is_operationalFault
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat) :
    (cancelledSearchResult (Bound := Bound) (RunReceipt := RunReceipt)
      (Fault := Fault) profile roots scheduler fuel).publicObservation =
      PublicObservation.operationalFault
        (observeCancelledAt
          (scheduledTrajectory profile roots scheduler)
          (completedDerivationObserver definition roots) fuel) :=
  rfl

@[simp] theorem faultedSearchResult_is_operationalFault
    {definition : ValidatedCalculusLanguageDef}
    (profile : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat) (fault : Fault) :
    (faultedSearchResult (Bound := Bound) (RunReceipt := RunReceipt)
      profile roots scheduler fuel fault).publicObservation =
      PublicObservation.operationalFault
        (observeFaultAt
          (scheduledTrajectory profile roots scheduler)
          (completedDerivationObserver definition roots) fuel fault) :=
  rfl

end OperationalOutcomes

/-! ## Positive and negative controls -/

namespace Canary

variable {definition : ValidatedCalculusLanguageDef}
variable {goal : Pattern} {ruleInstance : RuleInstance}

/-- One admitted zero-premise rule provides a concrete positive checked
derivation. -/
abbrev axiomDerivations
    (application : RuleApplication definition ruleInstance [] goal) :
    DerivationList definition [goal] :=
  .cons (CertificateGSLTScheduledHistory.Canary.axiomDerivation application)
    .nil

/-- Breadth-first traversal of the exact singleton candidate profile
eventually reports the checked derivation. -/
theorem singleton_profile_eventually_establishes
    (application : RuleApplication definition ruleInstance [] goal) :
    exists fuel,
      Nonempty (EstablishedAt
        (singletonOccurrence
          (CertificateGSLTScheduledHistory.Canary.sole application))
        [goal] Scheduler.breadthFirst fuel) := by
  let occurrence := CertificateGSLTScheduledHistory.Canary.sole application
  obtain ⟨fuel, emitted⟩ := breadthFirst_emits_singletonOccurrence occurrence
  refine ⟨fuel, Nonempty.intro
    { derivations := axiomDerivations application
      observed := ?_ }⟩
  have observed := completedDerivation_mem_of_complete_emission
    (.cons occurrence (.refl [])) emitted
  simpa [occurrence, axiomDerivations,
    CertificateGSLTScheduledHistory.Canary.sole_prepend_nil,
    scheduledPathToDerivationList,
    scheduledPathPrependDerivations] using observed

/-- The empty candidate profile closes after emitting only its non-complete
root, despite the independently checked axiom derivation. -/
def emptyProfileBoundary
    (_application : RuleApplication definition ruleInstance [] goal) :
    CoverageBoundary (empty definition) [goal] where
  fuel := 1
  closed := by
    rw [scheduledTrajectory_observation,
      Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration.ScheduledSearchProfile.Canary.empty_run_successor
        ([goal] : GoalState) 0]
  noCompleted := by
    rw [scheduledTrajectory_observation,
      Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration.ScheduledSearchProfile.Canary.empty_run_successor
        ([goal] : GoalState) 0]
    rfl

/-- Therefore closure of an incomplete candidate profile cannot soundly
refute derivability. -/
theorem empty_profile_boundary_is_not_refutation
    (application : RuleApplication definition ruleInstance [] goal) :
    ¬ Nonempty ((derivabilityAuthority definition).Obstruction [goal]) := by
  rintro ⟨obstruction⟩
  exact obstruction.down (Nonempty.intro (axiomDerivations application))

/-- The empty profile's closure is correctly classified as an authority
boundary while checked positive evidence remains available independently. -/
theorem empty_profile_requires_authority_upgrade
    (application : RuleApplication definition ruleInstance [] goal) :
    ((emptyProfileBoundary application).uncertifiedOutcome
      (Incomplete := Unit)).asBool = none /\
      Nonempty (DerivationList definition [goal]) /\
      ¬ Nonempty ((derivabilityAuthority definition).Obstruction [goal]) := by
  exact ⟨rfl, Nonempty.intro (axiomDerivations application),
    empty_profile_boundary_is_not_refutation application⟩

/-! The existing generic productive-loop model supplies the independent
control: productive open-ended output, fair occurrence selection, failure to
close finitely, and absence of a fabricated finite-bag meaning coexist. -/
theorem productive_open_search_is_not_finite_completion
    {ObservedAnswer : Type uAnswer} (answer : ObservedAnswer) :
    let scenario :=
      Mettapedia.GSLT.Core.SearchControlProperties.Canaries.productiveScenario
        answer
    Scenario.StreamProductiveFor scenario EventObserver.value
        (fun _ => answer) /\
      scenario.OccurrenceFair /\
      ¬ scenario.FinitelyCloses /\
      ¬ Nonempty (Scenario.DeclaredBagMeaning scenario) := by
  exact Canaries.productive_fair_open_and_not_finite_bag answer

end Canary

/-! ## Audited theorem crowns -/

#print axioms liveAt_resumes_exactly
#print axioms observeClosedAt_establishesClosedAbsence
#print axioms observeExhaustedAt_not_closedAbsence
#print axioms observeCancelledAt_not_closedAbsence
#print axioms observeFaultAt_not_closedAbsence
#print axioms completeDerivation?_follow_complete
#print axioms completedDerivation_mem_of_complete_emission
#print axioms EstablishedAt.toOutcome_asBool
#print axioms justificationCompleteAt_of_locallyComplete
#print axioms emitted_mem_of_breadthFirst_closed
#print axioms no_derivation_of_closed_complete_search
#print axioms CoverageBoundary.uncertifiedOutcome_asBool
#print axioms CoverageBoundary.certifiedOutcome_asBool
#print axioms CoverageBoundary.authorityUpgrade
#print axioms CoverageBoundary.no_budget_upgrade
#print axioms openSearchOutcome_control_readouts
#print axioms exhaustedSearchOutcome_control_readouts
#print axioms exhaustedToEstablished
#print axioms cancelledSearchResult_is_operationalFault
#print axioms faultedSearchResult_is_operationalFault
#print axioms Canary.singleton_profile_eventually_establishes
#print axioms Canary.empty_profile_requires_authority_upgrade
#print axioms Canary.productive_open_search_is_not_finite_completion

end Mettapedia.TypeTheory.CertificateGSLTSearchAuthorityBoundary
