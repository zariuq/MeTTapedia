import Mettapedia.Algebra.WorkSpan
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelBudget

/-!
# Work/span readout for parallel Cost–rho traces

`ParallelCostTrace` is intentionally proposition-valued: it certifies
reachability, but proof irrelevance means that it cannot serve as executable
scheduler data.  `ParallelCostSchedule` is the proof-relevant companion.  It
preserves the wave decomposition in `Type`, records exact work and wave-count
indices, and erases to the existing trace proposition.

The work/span readout assigns:

* one wave contributes its receipt cardinality to work;
* the same wave contributes one unit of span;
* successive waves compose sequentially.

Two schedules with the same endpoints may group occurrences into different
waves and therefore have different span.  Their erasures remain ordinary
`ParallelCostTrace` proofs, so the existing serialization theorem ensures that
the extra data records scheduling without adding computational outcomes.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open Mettapedia.Algebra

universe u

/-! ## Proof-relevant schedules and logical erasure -/

/-- A proof-relevant concurrent schedule.  The first natural-number index is
the exact number of funded reaction occurrences; the second is the exact number
of nonempty concurrent waves.  Keeping this family in `Type` is essential:
`ParallelCostTrace` lives in `Prop`, so Lean correctly forbids extracting a
runtime span from one of its proofs. -/
inductive ParallelCostSchedule {Ground : Type u} :
    CostConfig Ground →
    Multiset (SpendEvent Ground (CostName Ground)) →
    CostConfig Ground → Nat → Nat → Type u where
  | nil (config : CostConfig Ground) :
      ParallelCostSchedule config 0 config 0 0
  | cons {source middle target : CostConfig Ground}
      {waveReceipt tailReceipt :
        Multiset (SpendEvent Ground (CostName Ground))}
      {tailCount tailWaves : Nat}
      (head : ParallelCostStep source waveReceipt middle)
      (tail : ParallelCostSchedule middle tailReceipt target
        tailCount tailWaves) :
      ParallelCostSchedule source (waveReceipt + tailReceipt) target
        (waveReceipt.card + tailCount) (1 + tailWaves)

namespace ParallelCostSchedule

/-- Forget wave boundaries and retain the established logical trace. -/
def toTrace {Ground : Type u}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : ParallelCostSchedule source receipt target count waves) :
    ParallelCostTrace source receipt target count :=
  match schedule with
  | .nil config => .nil config
  | .cons head tail => .cons head tail.toTrace

@[simp] theorem toTrace_nil {Ground : Type u} (config : CostConfig Ground) :
    (ParallelCostSchedule.nil config).toTrace = ParallelCostTrace.nil config :=
  rfl

@[simp] theorem toTrace_cons {Ground : Type u}
    {source middle target : CostConfig Ground}
    {waveReceipt tailReceipt :
      Multiset (SpendEvent Ground (CostName Ground))}
    {tailCount tailWaves : Nat}
    (head : ParallelCostStep source waveReceipt middle)
    (tail : ParallelCostSchedule middle tailReceipt target
      tailCount tailWaves) :
    (ParallelCostSchedule.cons head tail).toTrace =
      ParallelCostTrace.cons head tail.toTrace :=
  rfl

/-- Work/span cost of a concurrent schedule.  A wave has work equal to the
cardinality of its occurrence receipt and span one. -/
def workSpan {Ground : Type u}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : ParallelCostSchedule source receipt target count waves) :
    WorkSpan :=
  match schedule with
  | .nil _ => 0
  | @cons _ _ _ _ waveReceipt _ _ _ _ tail =>
      WorkSpan.sequential ⟨waveReceipt.card, 1⟩ (workSpan tail)

@[simp] theorem workSpan_nil {Ground : Type u} (config : CostConfig Ground) :
    (ParallelCostSchedule.nil config).workSpan = 0 :=
  rfl

@[simp] theorem workSpan_cons {Ground : Type u}
    {source middle target : CostConfig Ground}
    {waveReceipt tailReceipt :
      Multiset (SpendEvent Ground (CostName Ground))}
    {tailCount tailWaves : Nat}
    (head : ParallelCostStep source waveReceipt middle)
    (tail : ParallelCostSchedule middle tailReceipt target
      tailCount tailWaves) :
    (ParallelCostSchedule.cons head tail).workSpan =
      WorkSpan.sequential ⟨waveReceipt.card, 1⟩ tail.workSpan :=
  rfl

/-- The work coordinate is exactly the event-count index. -/
theorem workSpan_work_eq_count {Ground : Type u}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : ParallelCostSchedule source receipt target count waves) :
    schedule.workSpan.work = count := by
  induction schedule with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [workSpan, WorkSpan.sequential, inductionHypothesis]

/-- The span coordinate is exactly the schedule's wave-count index. -/
theorem workSpan_span_eq_waves {Ground : Type u}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : ParallelCostSchedule source receipt target count waves) :
    schedule.workSpan.span = waves := by
  induction schedule with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [workSpan, WorkSpan.sequential, inductionHypothesis]

/-- Every wave is nonempty, hence wave count never exceeds occurrence count. -/
theorem waves_le_count {Ground : Type u}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : ParallelCostSchedule source receipt target count waves) :
    waves ≤ count := by
  induction schedule with
  | nil => exact le_rfl
  | @cons source middle target waveReceipt tailReceipt tailCount tailWaves
      head tail inductionHypothesis =>
      have positive : 0 < waveReceipt.card :=
        Multiset.card_pos.mpr head.receipt_ne_zero
      change 1 + tailWaves ≤ waveReceipt.card + tailCount
      omega

/-- Work can also be read directly from the complete occurrence receipt. -/
theorem workSpan_work_eq_receipt_card {Ground : Type u}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : ParallelCostSchedule source receipt target count waves) :
    schedule.workSpan.work = receipt.card := by
  rw [schedule.workSpan_work_eq_count,
    schedule.toTrace.count_eq_receipt_card]

/-- The all-serial baseline for a fixed number of event occurrences. -/
def serialBaseline (count : Nat) : WorkSpan := ⟨count, count⟩

/-- A concurrent grouping preserves work and can only reduce span relative to
the occurrence-by-occurrence serial baseline. -/
theorem workSpan_le_serialBaseline {Ground : Type u}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count waves : Nat}
    (schedule : ParallelCostSchedule source receipt target count waves) :
    schedule.workSpan ≤ serialBaseline count := by
  constructor
  · rw [schedule.workSpan_work_eq_count]
    exact le_rfl
  · rw [schedule.workSpan_span_eq_waves]
    exact schedule.waves_le_count

/-- A wide first wave yields a strict span improvement over the serial
baseline.  This is the negative control against collapsing work and span. -/
theorem workSpan_lt_serialBaseline_of_wideHead {Ground : Type u}
    {source middle target : CostConfig Ground}
    {waveReceipt tailReceipt :
      Multiset (SpendEvent Ground (CostName Ground))}
    {tailCount tailWaves : Nat}
    (head : ParallelCostStep source waveReceipt middle)
    (tail : ParallelCostSchedule middle tailReceipt target
      tailCount tailWaves)
    (wide : 1 < waveReceipt.card) :
    (ParallelCostSchedule.cons head tail).workSpan <
      serialBaseline (waveReceipt.card + tailCount) := by
  refine ⟨(ParallelCostSchedule.cons head tail).workSpan_le_serialBaseline, ?_⟩
  intro reverse
  have spanLower := reverse.2
  have tailBound := tail.waves_le_count
  rw [(ParallelCostSchedule.cons head tail).workSpan_span_eq_waves] at spanLower
  change waveReceipt.card + tailCount ≤ 1 + tailWaves at spanLower
  omega

/-- Positive example: the empty schedule has no work and no span. -/
example {Ground : Type u} (config : CostConfig Ground) :
    (ParallelCostSchedule.nil config).workSpan = 0 :=
  rfl

/-- Negative control: a schedule beginning with a genuinely wide wave cannot
have the serial baseline as its work/span value. -/
example {Ground : Type u}
    {source middle target : CostConfig Ground}
    {waveReceipt tailReceipt :
      Multiset (SpendEvent Ground (CostName Ground))}
    {tailCount tailWaves : Nat}
    (head : ParallelCostStep source waveReceipt middle)
    (tail : ParallelCostSchedule middle tailReceipt target
      tailCount tailWaves)
    (wide : 1 < waveReceipt.card) :
    (ParallelCostSchedule.cons head tail).workSpan ≠
      serialBaseline (waveReceipt.card + tailCount) :=
  ne_of_lt (workSpan_lt_serialBaseline_of_wideHead head tail wide)

end ParallelCostSchedule

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
