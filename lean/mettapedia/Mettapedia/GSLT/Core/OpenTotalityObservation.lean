import Mettapedia.GSLT.Core.InferenceControl
import Mettapedia.GSLT.Dynamics.AnswerEffect
import Mettapedia.GSLT.LanguageDef.InferenceSearch
import Mettapedia.Machines.RunObservation

/-!
# Open and closed search observations

This module relates three existing result layers without replacing them:

* `InferenceSearch.SearchOutcome` classifies authored proof search;
* `Machines.RunObservation` records occurrence-machine depth cuts and
  interruptions;
* `InferenceControl.Snapshot` records controller-ordered event prefixes and
  live work.

An observation keeps exact occurrences separate from its completion status.
In particular, exhausting a budget is not a closed absence claim.  Closure
contains evidence, and a resumable residual exists only when an explicit
capture predicate is inhabited.
-/

namespace Mettapedia.GSLT.Core.OpenTotalityObservation

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Dynamics.OperationalRegion

/-! ## Generic observation boundary -/

/-- Why an exact finite observation stopped.  The parameters remain distinct
because revisions, coverage witnesses, bounds, receipts, and resource faults
have different semantic roles. -/
inductive CompletionStatus
    (Residual Revision Coverage Bound Receipt Fault : Type*) where
  | open (residual : Residual) (revision : Revision)
  | closed (coverage : Coverage)
  | exhausted (bound : Bound) (receipt : Receipt)
  | cancelled
  | resourceFault (fault : Fault)

/-- Evidence that a completion status permits a particular captured residual.
Open observations must capture the residual and revision named by the status.
An exhausted observation may separately export an admitted residual.  Closed,
cancelled, and faulted observations have no capture constructor. -/
inductive CaptureEligible
    {Residual Revision Coverage Bound Receipt Fault : Type*} :
    CompletionStatus Residual Revision Coverage Bound Receipt Fault →
      Residual → Revision → Prop where
  | forOpen (residual : Residual) (revision : Revision) :
      CaptureEligible (.open residual revision) residual revision
  | forExhausted (bound : Bound) (receipt : Receipt)
      (residual : Residual) (revision : Revision) :
      CaptureEligible (.exhausted bound receipt) residual revision

/-- A resumable state consists of an exact residual, its revision, explicit
capture admission, and evidence that the stop status permits capture. -/
structure CapturedResidual
    {Residual Revision Coverage Bound Receipt Fault : Type*}
    (CaptureAdmitted : Residual → Revision → Prop)
    (completion : CompletionStatus Residual Revision Coverage Bound Receipt Fault) where
  residual : Residual
  revision : Revision
  admitted : CaptureAdmitted residual revision
  eligible : CaptureEligible completion residual revision

/-- Exact observed occurrences, a proof-relevant completion status, and an
optional admitted residual.  Occurrence order and multiplicity are retained. -/
structure Observation
    (Occurrence Residual Revision Coverage Bound Receipt Fault : Type*)
    (CaptureAdmitted : Residual → Revision → Prop) where
  occurrences : List Occurrence
  completion : CompletionStatus Residual Revision Coverage Bound Receipt Fault
  resumable : Option (CapturedResidual CaptureAdmitted completion)

namespace Observation

variable {Occurrence Residual Revision Coverage Bound Receipt Fault : Type*}
  {CaptureAdmitted : Residual → Revision → Prop}

/-- Construct an observation which exports no resumable state. -/
def withoutCapture (occurrences : List Occurrence)
    (completion : CompletionStatus Residual Revision Coverage Bound Receipt Fault) :
    Observation Occurrence Residual Revision Coverage Bound Receipt Fault
      CaptureAdmitted where
  occurrences := occurrences
  completion := completion
  resumable := none

/-- Construct an open observation with an explicitly admitted capture. -/
def openCaptured (occurrences : List Occurrence) (residual : Residual)
    (revision : Revision) (admitted : CaptureAdmitted residual revision) :
    Observation Occurrence Residual Revision Coverage Bound Receipt Fault
      CaptureAdmitted where
  occurrences := occurrences
  completion := .open residual revision
  resumable := some {
    residual := residual
    revision := revision
    admitted := admitted
    eligible := .forOpen residual revision }

/-- Construct a budget-exhausted observation which separately exports an
admitted residual. -/
def exhaustedCaptured (occurrences : List Occurrence) (bound : Bound)
    (receipt : Receipt) (residual : Residual) (revision : Revision)
    (admitted : CaptureAdmitted residual revision) :
    Observation Occurrence Residual Revision Coverage Bound Receipt Fault
      CaptureAdmitted where
  occurrences := occurrences
  completion := .exhausted bound receipt
  resumable := some {
    residual := residual
    revision := revision
    admitted := admitted
    eligible := .forExhausted bound receipt residual revision }

/-- Forget occurrence order while retaining multiplicity. -/
def occurrenceBag {Answer : Type*}
    (value : Occurrence → Answer)
    (observation : Observation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted) : Multiset Answer :=
  observation.occurrences.map value

/-- Extract the admitted resumable state, if one was explicitly captured. -/
def resume?
    (observation : Observation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted) : Option (Residual × Revision) :=
  observation.resumable.map fun captured =>
    (captured.residual, captured.revision)

@[simp] theorem resume?_openCaptured
    (occurrences : List Occurrence) (residual : Residual)
    (revision : Revision) (admitted : CaptureAdmitted residual revision) :
    (openCaptured (Coverage := Coverage) (Bound := Bound) (Receipt := Receipt)
      (Fault := Fault) occurrences residual revision admitted).resume? =
        some (residual, revision) :=
  rfl

@[simp] theorem resume?_withoutCapture
    (occurrences : List Occurrence)
    (completion :
      CompletionStatus Residual Revision Coverage Bound Receipt Fault) :
    (withoutCapture (CaptureAdmitted := CaptureAdmitted)
      occurrences completion).resume? = none :=
  rfl

/-- A closed absence claim requires both an empty occurrence list and an
actual coverage witness. -/
def EstablishesClosedAbsence
    (observation : Observation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted) : Prop :=
  observation.occurrences = [] ∧
    ∃ coverage, observation.completion = .closed coverage

/-- Budget exhaustion is constructor-distinct from closure. -/
theorem exhausted_ne_closed (bound : Bound) (receipt : Receipt)
    (coverage : Coverage) :
    (CompletionStatus.exhausted bound receipt :
      CompletionStatus Residual Revision Coverage Bound Receipt Fault) ≠
      .closed coverage := by
  intro equality
  cases equality

/-- Exhausting a bound never establishes semantic refutation by closed
absence, even when the observed occurrence list is empty. -/
theorem exhausted_not_establishesClosedAbsence
    (occurrences : List Occurrence) (bound : Bound) (receipt : Receipt) :
    ¬ EstablishesClosedAbsence
      (withoutCapture (Coverage := Coverage) (Fault := Fault)
        (CaptureAdmitted := CaptureAdmitted) occurrences
        (.exhausted bound receipt)) := by
  rintro ⟨_, coverage, equality⟩
  cases equality

/-- Every exported residual carries the caller's explicit admission proof. -/
theorem resumable_requires_admission
    (observation : Observation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted)
    {captured : CapturedResidual CaptureAdmitted observation.completion}
    (_ : observation.resumable = some captured) :
    CaptureAdmitted captured.residual captured.revision :=
  captured.admitted

/-- A closed observation cannot contain a resumable residual. -/
theorem resumable_eq_none_of_closed
    (observation : Observation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted)
    (coverage : Coverage) (closed : observation.completion = .closed coverage) :
    observation.resumable = none := by
  cases observation with
  | mk occurrences completion resumable =>
      cases closed
      cases resumable with
      | none => rfl
      | some captured => cases captured.eligible

/-- Capture is impossible when no residual/revision pair is admitted. -/
theorem resumable_eq_none_of_no_admission
    (observation : Observation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted)
    (denied : ∀ residual revision, ¬ CaptureAdmitted residual revision) :
    observation.resumable = none := by
  cases capturedEquation : observation.resumable with
  | none => rfl
  | some captured => exact False.elim (denied _ _ captured.admitted)

/-! The extra fields below are deliberately outside `Observation`: semantic
grades, scheduling priorities, and consumable budgets neither determine nor
are determined by answer occurrences or completion evidence. -/

/-- Independent assessment and control data attached to an observation. -/
structure Assessed
    (Grade Priority ConsumableBudget : Type*) where
  observation : Observation Occurrence Residual Revision Coverage Bound Receipt
    Fault CaptureAdmitted
  semanticGrade : Grade
  priority : Priority
  consumableBudget : ConsumableBudget

end Observation

/-! ## Existing result adapters -/

open Mettapedia.GSLT.LanguageDef.InferenceSearch

/-- Coverage supplied by the existing authored search result itself. -/
structure SearchClosedCoverage (outcome : SearchOutcome) : Type where
  outcomeClosed : outcome = .closed

/-- Interpret the existing authored-search result together with a caller-owned
exact residual.  A first found proof remains open because
`SearchOutcome.found` carries no coverage witness; `closed` itself supplies
the exact coverage evidence; and `exhausted` remains a bound/receipt event. -/
def observeSearchOutcomeWithResidual
    {Residual Revision Bound Receipt Fault : Type*}
    {CaptureAdmitted : Residual → Revision → Prop}
    (outcome : SearchOutcome) (residual : Residual) (revision : Revision)
    (bound : Bound) (receipt : Receipt) :
    Observation
      Mettapedia.GSLT.LanguageDef.InferenceChecker.RawProof Residual Revision
      (SearchClosedCoverage outcome) Bound Receipt Fault CaptureAdmitted :=
  match outcome with
  | .found proof => Observation.withoutCapture [proof] (.open residual revision)
  | .closed => Observation.withoutCapture [] (.closed ⟨rfl⟩)
  | .exhausted => Observation.withoutCapture [] (.exhausted bound receipt)

@[simp] theorem observeSearchOutcomeWithResidual_found_completion
    {Residual Revision Bound Receipt Fault : Type*}
    {CaptureAdmitted : Residual → Revision → Prop}
    (proof : Mettapedia.GSLT.LanguageDef.InferenceChecker.RawProof)
    (residual : Residual) (revision : Revision)
    (bound : Bound) (receipt : Receipt) :
    (observeSearchOutcomeWithResidual (Fault := Fault)
      (CaptureAdmitted := CaptureAdmitted)
      (.found proof) residual revision bound receipt).completion =
        .open residual revision :=
  rfl

@[simp] theorem observeSearchOutcomeWithResidual_closed_completion
    {Residual Revision Bound Receipt Fault : Type*}
    {CaptureAdmitted : Residual → Revision → Prop}
    (residual : Residual) (revision : Revision)
    (bound : Bound) (receipt : Receipt) :
    (observeSearchOutcomeWithResidual (Fault := Fault)
      (CaptureAdmitted := CaptureAdmitted)
      .closed residual revision bound receipt).completion = .closed ⟨rfl⟩ :=
  rfl

@[simp] theorem observeSearchOutcomeWithResidual_exhausted_completion
    {Residual Revision Bound Receipt Fault : Type*}
    {CaptureAdmitted : Residual → Revision → Prop}
    (residual : Residual) (revision : Revision)
    (bound : Bound) (receipt : Receipt) :
    (observeSearchOutcomeWithResidual (Fault := Fault)
      (CaptureAdmitted := CaptureAdmitted)
      .exhausted residual revision bound receipt).completion =
        .exhausted bound receipt :=
  rfl

open Mettapedia.Machines

/-- Coverage supplied by an occurrence-machine completion result. -/
structure RunClosedCoverage {State Answer : Type}
    (source : RunObservation State Answer) : Type where
  stopComplete : source.stop = .complete

/-- Refine the existing occurrence-machine stop classification.  A depth cut
is open with its exact pending frontier.  External fuel exhaustion remains
exhaustion; cancellation remains cancellation; stack and capacity failures
remain resource faults. -/
def observeRunObservation
    {State Answer Revision Receipt : Type}
    {CaptureAdmitted : List (State × List Nat) → Revision → Prop}
    (source : RunObservation State Answer) (revision : Revision)
    (bound : Nat) (receipt : Receipt) :
    Observation (Answer × List Nat) (List (State × List Nat)) Revision
      (RunClosedCoverage source) Nat Receipt ResourceInterruption CaptureAdmitted :=
  match stopEquation : source.stop with
  | .complete =>
      Observation.withoutCapture source.answers (.closed ⟨stopEquation⟩)
  | .depthCut pending _ =>
      Observation.withoutCapture source.answers (.open pending revision)
  | .interrupted .fuelExhausted =>
      Observation.withoutCapture source.answers (.exhausted bound receipt)
  | .interrupted .cancelled =>
      Observation.withoutCapture source.answers .cancelled
  | .interrupted .stackExhausted =>
      Observation.withoutCapture source.answers
        (.resourceFault .stackExhausted)
  | .interrupted .capacityExhausted =>
      Observation.withoutCapture source.answers
        (.resourceFault .capacityExhausted)

@[simp] theorem observeRunObservation_occurrences
    {State Answer Revision Receipt : Type}
    {CaptureAdmitted : List (State × List Nat) → Revision → Prop}
    (source : RunObservation State Answer) (revision : Revision)
    (bound : Nat) (receipt : Receipt) :
    (observeRunObservation (CaptureAdmitted := CaptureAdmitted)
      source revision bound receipt).occurrences = source.answers := by
  cases source with
  | mk answers stop =>
      cases stop with
      | complete => rfl
      | depthCut pending nonempty => rfl
      | interrupted reason => cases reason <;> rfl

/-! ## Controlled observations and denotational agreement -/

/-- Coverage evidence for one bounded controlled run is an empty live
frontier.  Occurrence preservation is supplied by the `Controller` interface;
the additive denotation below turns this operational coverage into semantic
agreement. -/
structure ControlledCoverage
    {Node Answer Memory : Type*}
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (roots : List Node) (fuel : Nat) : Type where
  frontierEmpty :
    (InferenceControl.Snapshot.run system controller fuel
      (InferenceControl.Snapshot.initial controller roots)).search.frontier = []

/-- An exact controlled residual is a snapshot with live work.  It includes
both the occurrence frontier and controller memory needed for resumption. -/
structure LiveControlledResidual (Node Answer Memory : Type) : Type where
  snapshot : InferenceControl.Snapshot Node Answer Memory
  live : snapshot.search.frontier ≠ []

/-- Package the residual produced by one bounded controlled run. -/
def controlledResidual
    {Node Answer Memory : Type}
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (roots : List Node) (fuel : Nat)
    (live :
      (InferenceControl.Snapshot.run system controller fuel
        (InferenceControl.Snapshot.initial controller roots)).search.frontier ≠ []) :
    LiveControlledResidual Node Answer Memory where
  snapshot := InferenceControl.Snapshot.run system controller fuel
    (InferenceControl.Snapshot.initial controller roots)
  live := live

/-- An open controlled observation retains its exact live snapshot and
revision but exports no resumable handle by default. -/
def observeOpenController
    {Node Answer Memory Revision Receipt Fault : Type}
    {CaptureAdmitted : LiveControlledResidual Node Answer Memory →
      Revision → Prop}
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (roots : List Node) (fuel : Nat) (revision : Revision)
    (live :
      (InferenceControl.Snapshot.run system controller fuel
        (InferenceControl.Snapshot.initial controller roots)).search.frontier ≠ []) :
    Observation (Emission Node Answer) (LiveControlledResidual Node Answer Memory)
      Revision (ControlledCoverage system controller roots fuel) Nat Receipt
      Fault CaptureAdmitted :=
  let residual := controlledResidual system controller roots fuel live
  Observation.withoutCapture residual.snapshot.search.events
    (.open residual revision)

/-- The same open result becomes resumable only after the capture authority
admits that exact residual and revision. -/
def observeOpenControllerCaptured
    {Node Answer Memory Revision Receipt Fault : Type}
    {CaptureAdmitted : LiveControlledResidual Node Answer Memory →
      Revision → Prop}
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (roots : List Node) (fuel : Nat) (revision : Revision)
    (live :
      (InferenceControl.Snapshot.run system controller fuel
        (InferenceControl.Snapshot.initial controller roots)).search.frontier ≠ [])
    (admitted : CaptureAdmitted
      (controlledResidual system controller roots fuel live) revision) :
    Observation (Emission Node Answer) (LiveControlledResidual Node Answer Memory)
      Revision (ControlledCoverage system controller roots fuel) Nat Receipt
      Fault CaptureAdmitted :=
  let residual := controlledResidual system controller roots fuel live
  Observation.openCaptured residual.snapshot.search.events residual revision
    admitted

@[simp] theorem observeOpenControllerCaptured_resume?
    {Node Answer Memory Revision Receipt Fault : Type}
    {CaptureAdmitted : LiveControlledResidual Node Answer Memory →
      Revision → Prop}
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (roots : List Node) (fuel : Nat) (revision : Revision)
    (live :
      (InferenceControl.Snapshot.run system controller fuel
        (InferenceControl.Snapshot.initial controller roots)).search.frontier ≠ [])
    (admitted : CaptureAdmitted
      (controlledResidual system controller roots fuel live) revision) :
    (observeOpenControllerCaptured (Receipt := Receipt) (Fault := Fault)
      system controller roots fuel revision live admitted).resume? =
        some (controlledResidual system controller roots fuel live, revision) :=
  rfl

/-- The closed observation associated with a coverage-certified controlled
run. -/
def observeClosedController
    {Node Answer Memory Revision Receipt Fault : Type*}
    {CaptureAdmitted : InferenceControl.Snapshot Node Answer Memory →
      Revision → Prop}
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (roots : List Node) (fuel : Nat)
    (coverage : ControlledCoverage system controller roots fuel) :
    Observation (Emission Node Answer)
      (InferenceControl.Snapshot Node Answer Memory) Revision
      (ControlledCoverage system controller roots fuel) Nat Receipt Fault
      CaptureAdmitted :=
  Observation.withoutCapture
    (InferenceControl.Snapshot.run system controller fuel
      (InferenceControl.Snapshot.initial controller roots)).search.events
    (.closed coverage)

/-- Closure evidence, together with the controller accounting invariant,
forces agreement with the declared additive denotation. -/
theorem observeClosedController_agrees_declaredDenotation
    {Node Answer Memory Revision Receipt Fault : Type*}
    {CaptureAdmitted : InferenceControl.Snapshot Node Answer Memory →
      Revision → Prop}
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (denotation : AdditiveDenotation system)
    (roots : List Node) (fuel : Nat)
    (coverage : ControlledCoverage system controller roots fuel) :
    (observeClosedController (Revision := Revision) (Receipt := Receipt)
      (Fault := Fault) (CaptureAdmitted := CaptureAdmitted)
      system controller roots fuel coverage).occurrenceBag Emission.value =
        foldValues denotation.value roots := by
  exact InferenceControl.Snapshot.completed_run_denotation system controller
    denotation roots fuel coverage.frontierEmpty

/-- Increasing the budget of one fixed controller extends, rather than
rewrites, its exact observed event prefix. -/
theorem controlled_budget_prefix
    {Node Answer Memory : Type*}
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (roots : List Node) (small extra : Nat) :
    (InferenceControl.Snapshot.run system controller small
        (InferenceControl.Snapshot.initial controller roots)).search.events.IsPrefix
      (InferenceControl.Snapshot.run system controller (small + extra)
        (InferenceControl.Snapshot.initial controller roots)).search.events := by
  rw [InferenceControl.Snapshot.run_add]
  exact InferenceControl.Snapshot.events_prefix_run system controller extra _

/-- A prefix extension induces a subbag extension after forgetting order. -/
theorem eventBag_mono_of_prefix
    {Node Answer : Type*}
    {first second : List (Emission Node Answer)}
    (isPrefix : first.IsPrefix second) :
    eventBag first ≤ eventBag second := by
  apply Multiset.le_iff_exists_add.mpr
  refine ⟨eventBag (second.drop first.length), ?_⟩
  have appendEquality := (List.prefix_iff_eq_append.mp isPrefix)
  calc
    eventBag second =
        eventBag (first ++ second.drop first.length) :=
      congrArg eventBag appendEquality.symm
    _ = eventBag first + eventBag (second.drop first.length) :=
      eventBag_append _ _

/-- Increasing the budget of one fixed controller also grows the observed
answer bag monotonically. -/
theorem controlled_budget_subbag
    {Node Answer Memory : Type*}
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (roots : List Node) (small extra : Nat) :
    eventBag
        (InferenceControl.Snapshot.run system controller small
          (InferenceControl.Snapshot.initial controller roots)).search.events ≤
      eventBag
        (InferenceControl.Snapshot.run system controller (small + extra)
          (InferenceControl.Snapshot.initial controller roots)).search.events :=
  eventBag_mono_of_prefix
    (controlled_budget_prefix system controller roots small extra)

/-- Two completed controllers realize the same declared `BagObservation`.
The bridge hypothesis identifies the branching denotation with the selected
host term's existing bag semantics. -/
theorem completed_controllers_realize_bagObservation
    {Node Answer Request FirstMemory SecondMemory : Type} [DecidableEq Answer]
    (system : BranchingSystem Node Answer)
    (first : Controller Node Answer FirstMemory)
    (second : Controller Node Answer SecondMemory)
    (denotation : AdditiveDenotation system) (roots : List Node)
    (firstFuel secondFuel : Nat)
    (firstComplete :
      (InferenceControl.Snapshot.run system first firstFuel
        (InferenceControl.Snapshot.initial first roots)).search.frontier = [])
    (secondComplete :
      (InferenceControl.Snapshot.run system second secondFuel
        (InferenceControl.Snapshot.initial second roots)).search.frontier = [])
    (point : OccurrencePoint Request Answer)
    (declared : OccurrencePoint.BagObservation point)
    (term : point.host.Term)
    (declares : declared.meaning term = foldValues denotation.value roots) :
    eventBag
        (InferenceControl.Snapshot.run system first firstFuel
          (InferenceControl.Snapshot.initial first roots)).search.events =
        declared.meaning term ∧
      eventBag
        (InferenceControl.Snapshot.run system second secondFuel
          (InferenceControl.Snapshot.initial second roots)).search.events =
        declared.meaning term := by
  constructor
  · exact (InferenceControl.Snapshot.completed_run_denotation system first
      denotation roots firstFuel firstComplete).trans declares.symm
  · exact (InferenceControl.Snapshot.completed_run_denotation system second
      denotation roots secondFuel secondComplete).trans declares.symm

/-- Completed fair controllers agree at the existing `BagObservation`
boundary.  Fairness is a liveness property used to justify eventual coverage;
once both coverage witnesses are present, occurrence accounting alone proves
the equality. -/
theorem completed_fair_controllers_agree_at_bagObservation
    {Node Answer Request FirstMemory SecondMemory : Type} [DecidableEq Answer]
    (system : BranchingSystem Node Answer)
    (first : Controller Node Answer FirstMemory)
    (second : Controller Node Answer SecondMemory)
    (denotation : AdditiveDenotation system) (roots : List Node)
    (_firstFair : InferenceControl.Snapshot.FairFrom system first roots)
    (_secondFair : InferenceControl.Snapshot.FairFrom system second roots)
    (firstFuel secondFuel : Nat)
    (firstComplete :
      (InferenceControl.Snapshot.run system first firstFuel
        (InferenceControl.Snapshot.initial first roots)).search.frontier = [])
    (secondComplete :
      (InferenceControl.Snapshot.run system second secondFuel
        (InferenceControl.Snapshot.initial second roots)).search.frontier = [])
    (point : OccurrencePoint Request Answer)
    (declared : OccurrencePoint.BagObservation point)
    (term : point.host.Term)
    (declares : declared.meaning term = foldValues denotation.value roots) :
    eventBag
        (InferenceControl.Snapshot.run system first firstFuel
          (InferenceControl.Snapshot.initial first roots)).search.events =
        declared.meaning term ∧
      eventBag
        (InferenceControl.Snapshot.run system second secondFuel
          (InferenceControl.Snapshot.initial second roots)).search.events =
        declared.meaning term := by
  exact completed_controllers_realize_bagObservation system first second
    denotation roots firstFuel secondFuel firstComplete secondComplete point
    declared term declares

/-! ## Executable positive and negative discriminators -/

namespace Examples

/-- Explicit admission yields a resumable open residual. -/
example :
    let observation : Observation Nat Nat Nat Unit Nat Unit Unit
        (fun residual revision => residual = 3 ∧ revision = 7) :=
      Observation.openCaptured [11] 3 7 ⟨rfl, rfl⟩
    observation.resume? = some (3, 7) := by
  rfl

/-- If the capture authority admits no state, no observation can export one. -/
example (observation :
    Observation Nat Nat Nat Unit Nat Unit Unit (fun _ _ => False)) :
    observation.resumable = none := by
  exact Observation.resumable_eq_none_of_no_admission observation
    (fun _ _ denied => denied)

namespace ControllerOrder

open BranchingTemporal.FiniteSearch

/-- A finite tree whose left answer is delayed by one expansion. -/
def root : FiniteSearch Bool :=
  .choice (.delay (.answer false)) (.answer true)

def fifo : Controller (FiniteSearch Bool) Bool Unit :=
  Controller.fixed Scheduler.breadthFirst

def dfs : Controller (FiniteSearch Bool) Bool Unit :=
  Controller.fixed Scheduler.depthFirst

/-- At the same incomplete bound, FIFO and DFS expose different exact answer
prefixes.  Both retain live work, so neither prefix is a complete denotation. -/
theorem bounded_fifo_dfs_prefixes_differ :
    let fifoResult := InferenceControl.Snapshot.run system fifo 3
      (InferenceControl.Snapshot.initial fifo [root])
    let dfsResult := InferenceControl.Snapshot.run system dfs 3
      (InferenceControl.Snapshot.initial dfs [root])
    fifoResult.search.events.map Emission.value = [true] ∧
      dfsResult.search.events.map Emission.value = [false] ∧
      fifoResult.search.events.map Emission.value ≠
        dfsResult.search.events.map Emission.value ∧
      fifoResult.search.frontier ≠ [] ∧ dfsResult.search.frontier ≠ [] := by
  decide

end ControllerOrder

end Examples

#print axioms observeClosedController_agrees_declaredDenotation
#print axioms Observation.exhausted_not_establishesClosedAbsence
#print axioms observeOpenControllerCaptured_resume?
#print axioms controlled_budget_prefix
#print axioms controlled_budget_subbag
#print axioms completed_fair_controllers_agree_at_bagObservation
#print axioms Examples.ControllerOrder.bounded_fifo_dfs_prefixes_differ

end Mettapedia.GSLT.Core.OpenTotalityObservation
