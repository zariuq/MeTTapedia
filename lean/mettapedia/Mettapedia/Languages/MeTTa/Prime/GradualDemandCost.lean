import Mettapedia.Algebra.WorkSpan
import Mettapedia.GSLT.Dynamics.ProofRelevantNeedValuation
import Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan

/-!
# Demand-sensitive work/span for gradual checks

`GradualExecutionPlan` proves that ordinary execution cannot force a suspended
check and that the first explicit demand claims exactly one evaluation.  This
module connects that proof-relevant demand trace to the shared work/span
algebra.

The projection is deliberately chronological: `n` claimed evaluations have
work `n` and span `n`.  It does not infer parallelism from the mere presence of
multiple checks.  A smaller span requires a separate independence or product-
factorization witness before `WorkSpan.parallel` may be used.

The construction does not introduce another counter.  Its work coordinate is
the existing `evaluationWorkValuation`, and the theorem
`evaluationWorkGrade_eq` connects that valuation to the exact trace count.
Cached observations remain distinct: observing cached evidence or stable blame
has zero evaluation work while still contributing one outcome observation.

The design follows the call-by-need separation of evaluation from observation
and the gradual-typing separation of dynamic execution from explicitly
requested evidence.  Relevant sources include Launchbury's natural semantics,
New and Ahmed's embedding-projection account of graduality, and Jacobs et al.'s
robust dynamic embedding criterion.
-/

open Mettapedia.Algebra
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan

universe uCell uOrigin uValue uStableFault uRetryableFault uRaw uKey
  uObligation uEvidence uBlame uRetry

/-! ## The generic trace projection -/

namespace Mettapedia.GSLT.Dynamics.ProofRelevantNeed.Trace

variable {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
  {StableFault : Type uStableFault}
  {RetryableFault : Type uRetryableFault} {cell : Cell}
  {source target : ProofRelevantNeed.CellState Origin Value StableFault}

/-- A chronological Need trace has one unit of span per claimed evaluation.
This is the serial embedding of the existing evaluation count into work/span. -/
def evaluationWorkSpan
    (trace : ProofRelevantNeed.Trace RetryableFault cell source target) :
    WorkSpan :=
  ⟨trace.evaluationCount, trace.evaluationCount⟩

@[simp] theorem evaluationWorkSpan_work
    (trace : ProofRelevantNeed.Trace RetryableFault cell source target) :
    trace.evaluationWorkSpan.work = trace.evaluationCount :=
  rfl

@[simp] theorem evaluationWorkSpan_span
    (trace : ProofRelevantNeed.Trace RetryableFault cell source target) :
    trace.evaluationWorkSpan.span = trace.evaluationCount :=
  rfl

/-- Chronological trace composition becomes sequential work/span composition. -/
theorem evaluationWorkSpan_trans
    {middle : ProofRelevantNeed.CellState Origin Value StableFault}
    (first : ProofRelevantNeed.Trace RetryableFault cell source middle)
    (second : ProofRelevantNeed.Trace RetryableFault cell middle target) :
    (first.trans second).evaluationWorkSpan =
      WorkSpan.sequential first.evaluationWorkSpan
        second.evaluationWorkSpan := by
  ext <;> simp [evaluationWorkSpan, WorkSpan.sequential]

/-- The additive evaluation valuation computes the same work as the direct
trace count.  This ensures the work/span projection observes the established
valuation rather than inventing an independent accounting mechanism. -/
theorem evaluationWorkGrade_eq
    (trace : ProofRelevantNeed.Trace RetryableFault cell source target) :
    trace.grade ProofRelevantNeed.evaluationWorkValuation =
      some trace.evaluationCount := by
  induction trace with
  | refl => rfl
  | tail event step rest inductionHypothesis =>
      change
        ProofRelevantNeed.evaluationWorkValuation.historyGrade
            (event :: rest.events) =
          some (event.evaluationCount + rest.evaluationCount)
      change
        ProofRelevantNeed.evaluationWorkValuation.historyGrade rest.events =
          some rest.evaluationCount at inductionHypothesis
      rw [Valuation.historyGrade_cons, inductionHypothesis]
      rfl

/-- Zero projected checking work is exactly zero claimed evaluations. -/
theorem evaluationWorkSpan_eq_zero_iff
    (trace : ProofRelevantNeed.Trace RetryableFault cell source target) :
    trace.evaluationWorkSpan = 0 ↔ trace.evaluationCount = 0 := by
  constructor
  · intro equal
    have workEqual := congrArg WorkSpan.work equal
    simpa using workEqual
  · intro count
    ext <;> simp [evaluationWorkSpan, count]

end Mettapedia.GSLT.Dynamics.ProofRelevantNeed.Trace

/-! ## Checked-plan readouts -/

namespace Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan.CheckedPlan

variable {Raw : Type uRaw} {Key : Type uKey}
  {Obligation : Type uObligation} {Evidence : Type uEvidence}
  {Blame : Type uBlame} {Retry : Type uRetry} {Cell : Type uCell}

/-- Preparing a checked plan without demanding it contributes no checking
work or span. -/
def noDemandWorkSpan (plan : CheckedPlan Raw Key Obligation) (cell : Cell) :
    WorkSpan :=
  (plan.noDemandTrace (Evidence := Evidence) (Blame := Blame)
    (Retry := Retry) cell).evaluationWorkSpan

@[simp] theorem noDemandWorkSpan_eq_zero
    (plan : CheckedPlan Raw Key Obligation) (cell : Cell) :
    plan.noDemandWorkSpan (Evidence := Evidence) (Blame := Blame)
      (Retry := Retry) cell = 0 :=
  rfl

/-- The checking cost of one explicit demand, for any checker outcome. -/
def demandWorkSpan
    (plan : CheckedPlan Raw Key Obligation)
    (checker : Checker Obligation Evidence Blame Retry) (cell : Cell) :
    WorkSpan :=
  (plan.demandCheck checker cell).2.evaluationWorkSpan

/-- A first explicit demand contributes one unit of work and one unit of
chronological span, independently of whether it returns evidence, stable
blame, or a retry request. -/
theorem demandWorkSpan_eq_unit
    (plan : CheckedPlan Raw Key Obligation)
    (checker : Checker Obligation Evidence Blame Retry) (cell : Cell) :
    plan.demandWorkSpan checker cell = ⟨1, 1⟩ := by
  ext <;> simp [demandWorkSpan,
    GradualExecutionPlan.CheckedPlan.demandCheck_evaluationCount]

/-- Raw execution plus an undemanded gradual obligation.  The checker is not
an argument because this path has no authority to force it. -/
def executionWorkSpanWithoutDemand (rawWorkSpan : Raw → WorkSpan)
    (plan : CheckedPlan Raw Key Obligation) (cell : Cell) : WorkSpan :=
  WorkSpan.sequential (rawWorkSpan plan.term)
    (plan.noDemandWorkSpan (Evidence := Evidence) (Blame := Blame)
      (Retry := Retry) cell)

/-- Suspending a gradual obligation leaves the raw execution cost exactly
unchanged. -/
@[simp] theorem executionWorkSpanWithoutDemand_eq_raw
    (rawWorkSpan : Raw → WorkSpan) (plan : CheckedPlan Raw Key Obligation)
    (cell : Cell) :
    executionWorkSpanWithoutDemand (Evidence := Evidence) (Blame := Blame)
      (Retry := Retry) rawWorkSpan plan cell = rawWorkSpan plan.term := by
  simp [executionWorkSpanWithoutDemand]

/-- Raw execution plus a separately requested gradual check. -/
def executionWorkSpanWithDemand (rawWorkSpan : Raw → WorkSpan)
    (plan : CheckedPlan Raw Key Obligation)
    (checker : Checker Obligation Evidence Blame Retry) (cell : Cell) :
    WorkSpan :=
  WorkSpan.sequential (rawWorkSpan plan.term)
    (plan.demandWorkSpan checker cell)

/-- Requesting the first check adds exactly one chronological unit to the raw
execution readout. -/
theorem executionWorkSpanWithDemand_eq_raw_then_unit
    (rawWorkSpan : Raw → WorkSpan) (plan : CheckedPlan Raw Key Obligation)
    (checker : Checker Obligation Evidence Blame Retry) (cell : Cell) :
    executionWorkSpanWithDemand rawWorkSpan plan checker cell =
      WorkSpan.sequential (rawWorkSpan plan.term) ⟨1, 1⟩ := by
  rw [executionWorkSpanWithDemand, demandWorkSpan_eq_unit]

/-- The requested check has a real cost: it cannot equal the undemanded raw
path for any raw work/span readout. -/
theorem executionWorkSpanWithDemand_ne_withoutDemand
    (rawWorkSpan : Raw → WorkSpan) (plan : CheckedPlan Raw Key Obligation)
    (checker : Checker Obligation Evidence Blame Retry) (cell : Cell) :
    executionWorkSpanWithDemand rawWorkSpan plan checker cell ≠
      executionWorkSpanWithoutDemand (Evidence := Evidence) (Blame := Blame)
        (Retry := Retry) rawWorkSpan plan cell := by
  rw [executionWorkSpanWithDemand_eq_raw_then_unit,
    executionWorkSpanWithoutDemand_eq_raw]
  intro equal
  have workEqual := congrArg WorkSpan.work equal
  simp [WorkSpan.sequential] at workEqual

/-- Re-observing cached evidence contributes no evaluation work. -/
def cachedValueWorkSpan (origin : CheckOrigin Key Obligation)
    (evidence : Evidence) (cell : Cell) : WorkSpan :=
  ((GradualExecutionPlan.CheckedPlan.observeCachedValue cell origin evidence :
      ProofRelevantNeed.Trace Retry cell
        (show CheckState Key Obligation Evidence Blame from
          .cachedValue origin evidence)
        (show CheckState Key Obligation Evidence Blame from
          .cachedValue origin evidence))).evaluationWorkSpan

@[simp] theorem cachedValueWorkSpan_eq_zero
    (origin : CheckOrigin Key Obligation) (evidence : Evidence) (cell : Cell) :
    cachedValueWorkSpan (Blame := Blame) (Retry := Retry) origin evidence cell =
      0 :=
  rfl

/-- Re-observing cached stable blame also contributes no evaluation work. -/
def cachedBlameWorkSpan (origin : CheckOrigin Key Obligation)
    (blame : Blame) (cell : Cell) : WorkSpan :=
  ((GradualExecutionPlan.CheckedPlan.observeCachedBlame cell origin blame :
      ProofRelevantNeed.Trace Retry cell
        (show CheckState Key Obligation Evidence Blame from
          .cachedStableFault origin blame)
        (show CheckState Key Obligation Evidence Blame from
          .cachedStableFault origin blame))).evaluationWorkSpan

@[simp] theorem cachedBlameWorkSpan_eq_zero
    (origin : CheckOrigin Key Obligation) (blame : Blame) (cell : Cell) :
    cachedBlameWorkSpan (Evidence := Evidence) (Retry := Retry) origin blame
      cell = 0 :=
  rfl

/-- The first demand is observably more checking work than no demand.  This is
the negative control preventing demand-sensitive accounting from collapsing
to the always-zero readout. -/
theorem demandWorkSpan_ne_noDemandWorkSpan
    (plan : CheckedPlan Raw Key Obligation)
    (checker : Checker Obligation Evidence Blame Retry) (cell : Cell) :
    plan.demandWorkSpan checker cell ≠
      plan.noDemandWorkSpan (Evidence := Evidence) (Blame := Blame)
        (Retry := Retry) cell := by
  rw [demandWorkSpan_eq_unit, noDemandWorkSpan_eq_zero]
  decide

/-- Zero cached checking work does not erase the cached observation event.
The cost and observation axes remain distinct readouts of the same trace. -/
theorem cachedValue_zero_work_one_observation
    (origin : CheckOrigin Key Obligation) (evidence : Evidence) (cell : Cell) :
    cachedValueWorkSpan (Blame := Blame) (Retry := Retry) origin evidence cell =
        0 ∧
      ((GradualExecutionPlan.CheckedPlan.observeCachedValue cell origin evidence :
        ProofRelevantNeed.Trace Retry cell
          (show CheckState Key Obligation Evidence Blame from
            .cachedValue origin evidence)
          (show CheckState Key Obligation Evidence Blame from
            .cachedValue origin evidence))).outcomeObservationCount = 1 :=
  ⟨rfl, rfl⟩

end Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan.CheckedPlan

/-! ## Native canaries -/

namespace Mettapedia.Languages.MeTTa.Prime.GradualDemandCost.NativeCanary

open GradualExecutionPlan.NativeCanary

/-- The undemanded rejected protocol remains cost-free on the checking axis. -/
example :
    rejectedRequest.noDemandWorkSpan
      (Evidence := ProtocolEvidence) (Blame := ProtocolBlame)
      (Retry := ProtocolRetry) (0 : Nat) = 0 :=
  rfl

/-- Explicitly demanding the rejected protocol pays one checking unit. -/
example :
    rejectedRequest.demandWorkSpan protocolChecker (0 : Nat) = ⟨1, 1⟩ :=
  CheckedPlan.demandWorkSpan_eq_unit _ _ _

/-- Caching is semantically relevant: the demanded and undemanded readouts
are not equal. -/
example :
    rejectedRequest.demandWorkSpan protocolChecker (0 : Nat) ≠
      rejectedRequest.noDemandWorkSpan
        (Evidence := ProtocolEvidence) (Blame := ProtocolBlame)
        (Retry := ProtocolRetry) (0 : Nat) :=
  CheckedPlan.demandWorkSpan_ne_noDemandWorkSpan _ _ _

/-- If the raw request costs work four and span three, suspending a rejected
check preserves that readout. -/
example :
    CheckedPlan.executionWorkSpanWithoutDemand
      (Evidence := ProtocolEvidence) (Blame := ProtocolBlame)
      (Retry := ProtocolRetry) (fun _ => (⟨4, 3⟩ : WorkSpan))
      rejectedRequest (0 : Nat) = ⟨4, 3⟩ :=
  rfl

/-- Demanding that check adds one unit to each chronological coordinate. -/
example :
    CheckedPlan.executionWorkSpanWithDemand
      (fun _ => (⟨4, 3⟩ : WorkSpan)) rejectedRequest protocolChecker
      (0 : Nat) = ⟨5, 4⟩ := by
  rw [CheckedPlan.executionWorkSpanWithDemand_eq_raw_then_unit]
  rfl

end Mettapedia.Languages.MeTTa.Prime.GradualDemandCost.NativeCanary
