import Mettapedia.Languages.MeTTa.Prime.NativeInteraction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.WorkSpan

/-!
# Native work/span accounting for Prime interaction

Prime's interaction computation fibre retains exact chronological events.
Its canonical work/span readout is therefore serial: each event contributes
one unit of work and one unit of span.  Genuine parallel span requires more
information than an endpoint path contains, so this module separately
internalizes Cost-rho's proof-relevant `ParallelCostSchedule`, whose wave
boundaries are retained in `Type`.

Both objects are ordinary types and terms of Prime's semantic CwF.  The
schedule erases to the established proposition-valued `ParallelCostTrace`;
its executable work/span value is computed from the schedule, never from a
proof in `Prop`.  This keeps logical reachability, scheduling, and accounting
at their proper abstraction boundaries.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeInteractionCost

open Mettapedia.Algebra
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.NativeInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-! ## Work/span as a native semantic value -/

/-- Work/span pairs are ordinary closed Prime semantic values. -/
def workSpanTy : familiesCwF.Ty PrimeContext :=
  fun _ => WorkSpan

def internalWorkSpan (value : WorkSpan) :
    familiesCwF.Tm PrimeContext workSpanTy :=
  fun _ => value

/-! ## Chronological interaction paths -/

/-- The serial work/span readout of an authenticated event path.  A plain
path contains order but no concurrency-wave partition, so its span equals its
work. -/
def pathWorkSpan {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {source target : theory.Term}
    (path : familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation source target)) :
    familiesCwF.Tm PrimeContext workSpanTy :=
  fun context =>
    let count := EventPath.pathLength presentation (path context)
    ⟨count, count⟩

@[simp] theorem pathWorkSpan_work {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {source target : theory.Term}
    (path : familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation source target))
    (context : PrimeContext) :
    (pathWorkSpan path context).work =
      EventPath.pathLength presentation (path context) :=
  rfl

@[simp] theorem pathWorkSpan_span {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {source target : theory.Term}
    (path : familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation source target))
    (context : PrimeContext) :
    (pathWorkSpan path context).span =
      EventPath.pathLength presentation (path context) :=
  rfl

/-- Chronological path composition is exactly sequential work/span
composition. -/
theorem pathWorkSpan_compose {theory : GSLT}
    {presentation : InteractionPresentation theory}
    {source middle target : theory.Term}
    (firstPath : familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation source middle))
    (secondPath : familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation middle target)) :
    pathWorkSpan (composePath firstPath secondPath) =
      fun context => WorkSpan.sequential
        (pathWorkSpan firstPath context) (pathWorkSpan secondPath context) := by
  funext context
  apply WorkSpan.ext <;>
    simp [pathWorkSpan, composePath, WorkSpan.sequential,
      EventPath.pathLength_append]

/-! ## Proof-relevant concurrent schedules -/

/-- Cost-rho schedules are native Prime semantic types indexed by endpoints,
the complete occurrence receipt, exact work, and exact wave count. -/
def parallelScheduleTy {Ground : Type}
    (source : CostConfig Ground)
    (receipt : Multiset (SpendEvent Ground (CostName Ground)))
    (target : CostConfig Ground) (count waves : Nat) :
    familiesCwF.Ty PrimeContext :=
  fun _ => ParallelCostSchedule source receipt target count waves

/-- The logical trace to which a proof-relevant schedule erases. -/
def parallelTraceTy {Ground : Type}
    (source : CostConfig Ground)
    (receipt : Multiset (SpendEvent Ground (CostName Ground)))
    (target : CostConfig Ground) (count : Nat) :
    familiesCwF.Ty PrimeContext :=
  fun _ => PLift (ParallelCostTrace source receipt target count)

def internalSchedule {Ground : Type}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : ParallelCostSchedule source receipt target count waves) :
    familiesCwF.Tm PrimeContext
      (parallelScheduleTy source receipt target count waves) :=
  fun _ => schedule

/-- Logical erasure is internalized as a map between Prime semantic types. -/
def eraseSchedule {Ground : Type}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : familiesCwF.Tm PrimeContext
      (parallelScheduleTy source receipt target count waves)) :
    familiesCwF.Tm PrimeContext
      (parallelTraceTy source receipt target count) :=
  fun context => ⟨(schedule context).toTrace⟩

/-- Executable accounting reads the proof-relevant schedule. -/
def scheduleWorkSpan {Ground : Type}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : familiesCwF.Tm PrimeContext
      (parallelScheduleTy source receipt target count waves)) :
    familiesCwF.Tm PrimeContext workSpanTy :=
  fun context => (schedule context).workSpan

@[simp] theorem scheduleWorkSpan_work {Ground : Type}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : familiesCwF.Tm PrimeContext
      (parallelScheduleTy source receipt target count waves))
    (context : PrimeContext) :
    (scheduleWorkSpan schedule context).work = count :=
  (schedule context).workSpan_work_eq_count

@[simp] theorem scheduleWorkSpan_span {Ground : Type}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : familiesCwF.Tm PrimeContext
      (parallelScheduleTy source receipt target count waves))
    (context : PrimeContext) :
    (scheduleWorkSpan schedule context).span = waves :=
  (schedule context).workSpan_span_eq_waves

/-- Internal scheduling never exceeds the serial span for the same exact
event count. -/
theorem scheduleWorkSpan_le_serial {Ground : Type}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : familiesCwF.Tm PrimeContext
      (parallelScheduleTy source receipt target count waves))
    (context : PrimeContext) :
    (show WorkSpan from scheduleWorkSpan schedule context) ≤
      ParallelCostSchedule.serialBaseline count :=
  by
    change (schedule context).workSpan ≤
      ParallelCostSchedule.serialBaseline count
    exact (schedule context).workSpan_le_serialBaseline

/-! ## Positive and negative controls -/

/-- Positive: a one-event rho computation has unit work and unit span. -/
theorem internalComm_workSpan :
    pathWorkSpan internalComm PUnit.unit = ⟨1, 1⟩ :=
  rfl

/-- Negative: two independent unit events have the same work but smaller span
than the chronological two-event path. -/
theorem parallel_two_events_ne_sequential :
    WorkSpan.parallel ⟨1, 1⟩ ⟨1, 1⟩ ≠
      WorkSpan.sequential ⟨1, 1⟩ ⟨1, 1⟩ := by
  intro equal
  have spanEqual := congrArg WorkSpan.span equal
  norm_num [WorkSpan.parallel, WorkSpan.sequential] at spanEqual

#print axioms pathWorkSpan_compose
#print axioms scheduleWorkSpan_work
#print axioms scheduleWorkSpan_span
#print axioms scheduleWorkSpan_le_serial
#print axioms parallel_two_events_ne_sequential

end Mettapedia.Languages.MeTTa.Prime.NativeInteractionCost
