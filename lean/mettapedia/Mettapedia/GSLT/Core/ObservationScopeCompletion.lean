import Mettapedia.GSLT.Core.ObservationDemandControl
import Mettapedia.GSLT.Dynamics.SpaceExecutionClosureBoundary

/-!
# Observation-scope completion is not execution closure

An observer may have seen enough before the selected execution is quiescent.
For example, first-witness demand is discharged by one occurrence even when a
live residual remains.  Conversely, a closed source may complete a first or
finite-prefix request without producing the requested number of occurrences.

This file places those facts on two independent axes:

* count satisfaction handles only first and finite-prefix demand;
* execution closure requires an inspected coverage witness;
* a scope is complete when either its finite demand is satisfied or its
  execution is closed.

Complete-bag, ordered-stream, and undetermined observations cannot be
discharged by a finite occurrence count alone.  This is the proof boundary
needed by runtimes which stop a consumer after one witness while retaining an
owned continuation for the unobserved alternatives.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ObservationScopeCompletion

open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.OpenTotalityObservation
open Mettapedia.GSLT.Dynamics.SpaceExecutionClosureBoundary

universe uOccurrence uResidual uRevision uCoverage uBound uReceipt uFault

/-! ## Independent completion axes -/

/-- The observation demands that can be discharged from a finite occurrence
count alone.  Whole-result and open-stream demands require an independent
closure judgment. -/
def CountSatisfied : CompletionDemand → Nat → Prop
  | .first, observed => 1 ≤ observed
  | .finitePrefix requested, observed => requested ≤ observed
  | .completeBag, _ => False
  | .orderedStream, _ => False
  | .undetermined, _ => False

theorem countSatisfied_mono
    {demand : CompletionDemand} {observed later : Nat}
    (satisfied : CountSatisfied demand observed)
    (monotone : observed ≤ later) :
    CountSatisfied demand later := by
  cases demand <;> simp [CountSatisfied] at satisfied ⊢ <;> omega

@[simp] theorem completeBag_not_countSatisfied (observed : Nat) :
    ¬ CountSatisfied .completeBag observed := by
  simp [CountSatisfied]

@[simp] theorem orderedStream_not_countSatisfied (observed : Nat) :
    ¬ CountSatisfied .orderedStream observed := by
  simp [CountSatisfied]

@[simp] theorem undetermined_not_countSatisfied (observed : Nat) :
    ¬ CountSatisfied .undetermined observed := by
  simp [CountSatisfied]

/-- An observation paired with the exact consumer demand that delimits its
scope.  The underlying occurrence/completion/residual carrier is unchanged. -/
structure ScopedObservation
    (Occurrence : Type uOccurrence)
    (Residual : Type uResidual) (Revision : Type uRevision)
    (Coverage : Type uCoverage) (Bound : Type uBound)
    (Receipt : Type uReceipt) (Fault : Type uFault)
    (CaptureAdmitted : Residual → Revision → Prop) where
  demand : CompletionDemand
  observation : Observation Occurrence Residual Revision Coverage Bound
    Receipt Fault CaptureAdmitted

namespace ScopedObservation

variable
    {Occurrence : Type uOccurrence}
    {Residual : Type uResidual} {Revision : Type uRevision}
    {Coverage : Type uCoverage} {Bound : Type uBound}
    {Receipt : Type uReceipt} {Fault : Type uFault}
    {CaptureAdmitted : Residual → Revision → Prop}

def observedCount
    (scope : ScopedObservation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted) : Nat :=
  scope.observation.occurrences.length

/-- The finite consumer demand has been met by the observed occurrence
prefix.  This says nothing about the residual frontier. -/
def DemandSatisfied
    (scope : ScopedObservation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted) : Prop :=
  CountSatisfied scope.demand scope.observedCount

/-- The selected execution is actually closed.  This requires the coverage
witness stored in the observation's completion constructor. -/
def ExecutionClosed
    (scope : ScopedObservation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted) : Prop :=
  ∃ coverage, scope.observation.completion = .closed coverage

/-- A delimited observation scope may finish because its finite demand was
met or because the underlying execution was proved closed.  The disjunction
does not erase which reason occurred. -/
def ScopeComplete
    (scope : ScopedObservation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted) : Prop :=
  scope.DemandSatisfied ∨ scope.ExecutionClosed

theorem complete_of_demandSatisfied
    {scope : ScopedObservation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted}
    (satisfied : scope.DemandSatisfied) :
    scope.ScopeComplete :=
  Or.inl satisfied

theorem complete_of_executionClosed
    {scope : ScopedObservation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted}
    (closed : scope.ExecutionClosed) :
    scope.ScopeComplete :=
  Or.inr closed

/-- When closure is the reason available, the generic open-totality carrier
forbids a resumable residual. -/
theorem no_residual_of_executionClosed
    (scope : ScopedObservation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted)
    (closed : scope.ExecutionClosed) :
    scope.observation.resumable = none := by
  rcases closed with ⟨coverage, equality⟩
  exact scope.observation.resumable_eq_none_of_closed coverage equality

/-- Complete-bag scope completion is exactly execution closure: a finite
answer count cannot close the bag. -/
theorem completeBag_scopeComplete_iff_executionClosed
    (scope : ScopedObservation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted)
    (demand : scope.demand = .completeBag) :
    scope.ScopeComplete ↔ scope.ExecutionClosed := by
  simp [ScopeComplete, DemandSatisfied, CountSatisfied, demand]

/-- The same is true for an ordered stream considered as a completed finite
observation.  Finite pulls are expressed separately as prefix demand. -/
theorem orderedStream_scopeComplete_iff_executionClosed
    (scope : ScopedObservation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted)
    (demand : scope.demand = .orderedStream) :
    scope.ScopeComplete ↔ scope.ExecutionClosed := by
  simp [ScopeComplete, DemandSatisfied, CountSatisfied, demand]

end ScopedObservation

/-! ## A first-witness/live-residual discriminator -/

namespace Canary

namespace Tick

abbrev Phase :=
  Mettapedia.GSLT.Dynamics.SpaceExecutionClosureBoundary.Canary.Phase

abbrev tickDriver :=
  Mettapedia.GSLT.Dynamics.SpaceExecutionClosureBoundary.Canary.tickDriver

theorem one_tick_expires :
    tickDriver.toHostedDriver.runReport .start () 1 =
      .expired .middle () :=
  Mettapedia.GSLT.Dynamics.SpaceExecutionClosureBoundary.Canary.one_tick_expires

end Tick

def exactMiddleCapture
    (configuration : Tick.Phase × Unit) (_revision : Unit) : Prop :=
  configuration = (.middle, ())

abbrev TickScope :=
  ScopedObservation Unit (Tick.Phase × Unit) Unit
    (ActivationDriver.QuiescentCoverage Tick.tickDriver) Nat
    (ActivationDriver.ExactRunReceipt Tick.tickDriver) Empty
    exactMiddleCapture

/-- One witnessed occurrence discharges first-result demand while the exact
one-tick residual remains captured and resumable. -/
def firstCapturedAfterOne : TickScope where
  demand := .first
  observation :=
    Tick.tickDriver.captureExpiredRun [()] .start () 1 .middle ()
      Tick.one_tick_expires (by rfl)

theorem first_after_one_satisfies_demand :
    firstCapturedAfterOne.DemandSatisfied := by
  change 1 ≤ 1
  omega

theorem first_after_one_is_not_execution_closed :
    ¬ firstCapturedAfterOne.ExecutionClosed := by
  rintro ⟨coverage, equality⟩
  cases equality

theorem first_after_one_retains_exact_residual :
    firstCapturedAfterOne.observation.resume? =
      some ((.middle, ()), ()) :=
  rfl

/-- First-witness scope completion and execution closure are therefore not
the same proposition. -/
theorem first_scope_completes_before_execution_closes :
    firstCapturedAfterOne.ScopeComplete ∧
      ¬ firstCapturedAfterOne.ExecutionClosed ∧
      firstCapturedAfterOne.observation.resume? =
        some ((.middle, ()), ()) :=
  ⟨firstCapturedAfterOne.complete_of_demandSatisfied
      first_after_one_satisfies_demand,
    first_after_one_is_not_execution_closed,
    first_after_one_retains_exact_residual⟩

/-- The identical live run does not complete a whole-bag request merely
because it emitted one occurrence. -/
def completeBagAfterOne : TickScope where
  demand := .completeBag
  observation := firstCapturedAfterOne.observation

theorem complete_bag_one_occurrence_is_not_scope_complete :
    ¬ completeBagAfterOne.ScopeComplete := by
  rintro (satisfied | closed)
  · exact completeBag_not_countSatisfied 1 satisfied
  · exact first_after_one_is_not_execution_closed closed

/-- A closed empty execution still completes first-result scope: source
closure, not an invented witness, explains the short result. -/
def closedEmptyFirst : TickScope where
  demand := .first
  observation := Tick.tickDriver.observeBoundedRun [] .done () 0

theorem closed_empty_first_is_not_count_satisfied :
    ¬ closedEmptyFirst.DemandSatisfied := by
  simp [ScopedObservation.DemandSatisfied,
    ScopedObservation.observedCount, CountSatisfied, closedEmptyFirst]

theorem closed_empty_first_is_execution_closed :
    closedEmptyFirst.ExecutionClosed := by
  refine ⟨{
    store := .done
    control := ()
    quiescent := rfl
  }, ?_⟩
  rfl

theorem closed_empty_first_scope_completes :
    closedEmptyFirst.ScopeComplete :=
  closedEmptyFirst.complete_of_executionClosed
    closed_empty_first_is_execution_closed

/-- Positive complete-bag control: after both ticks, inspected quiescence
does close the bag scope. -/
def closedCompleteBag : TickScope where
  demand := .completeBag
  observation := Tick.tickDriver.observeBoundedRun [()] .start () 2

theorem closed_complete_bag_scope_completes :
    closedCompleteBag.ScopeComplete := by
  apply closedCompleteBag.complete_of_executionClosed
  refine ⟨{
    store := .done
    control := ()
    quiescent := rfl
  }, ?_⟩
  rfl

/-- The paired canaries establish both directions of independence relevant to
a runtime: demand satisfaction may precede closure, and closure may complete
a scope without satisfying its requested count. -/
theorem observation_scope_and_execution_closure_do_not_collapse :
    (firstCapturedAfterOne.ScopeComplete ∧
      ¬ firstCapturedAfterOne.ExecutionClosed ∧
      firstCapturedAfterOne.observation.resume? =
        some ((.middle, ()), ())) ∧
    (¬ closedEmptyFirst.DemandSatisfied ∧
      closedEmptyFirst.ExecutionClosed ∧
      closedEmptyFirst.ScopeComplete) ∧
    ¬ completeBagAfterOne.ScopeComplete ∧
    closedCompleteBag.ScopeComplete := by
  exact ⟨first_scope_completes_before_execution_closes,
    ⟨closed_empty_first_is_not_count_satisfied,
      closed_empty_first_is_execution_closed,
      closed_empty_first_scope_completes⟩,
    complete_bag_one_occurrence_is_not_scope_complete,
    closed_complete_bag_scope_completes⟩

end Canary

#print axioms countSatisfied_mono
#print axioms ScopedObservation.no_residual_of_executionClosed
#print axioms ScopedObservation.completeBag_scopeComplete_iff_executionClosed
#print axioms ScopedObservation.orderedStream_scopeComplete_iff_executionClosed
#print axioms Canary.first_scope_completes_before_execution_closes
#print axioms Canary.complete_bag_one_occurrence_is_not_scope_complete
#print axioms Canary.closed_empty_first_scope_completes
#print axioms Canary.closed_complete_bag_scope_completes
#print axioms Canary.observation_scope_and_execution_closure_do_not_collapse

end Mettapedia.GSLT.Core.ObservationScopeCompletion
