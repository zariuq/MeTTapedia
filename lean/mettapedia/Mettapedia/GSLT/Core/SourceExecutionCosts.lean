import Mettapedia.GSLT.Core.FiniteSearchCertificate
import Mettapedia.Algorithms.OnlineBulkSwitch
import Mathlib.Data.Fintype.BigOperators

/-!
# Source-operation ledgers for selective and bulk execution

Operations count candidate, binding and index visits separately from retained
captures, restores, queue visits and publication. Prices are parameters of
the cost model; they are not wall-clock or allocation measurements.

The source-tree fold reuses executable finite observation certificates. A
qualified pure bulk traversal can avoid the per-quantum agenda overhead while
performing the same source work. This does not assert that every runtime bulk
mode avoids those operations or that arbitrary host services can be folded.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.SourceExecutionCosts

open BranchingTemporal FiniteSearchCertificate
open scoped BigOperators

inductive Operation where
  | candidate | binding | index | capture | restore | queue | publication
  deriving DecidableEq, Repr

instance : Fintype Operation where
  elems := {.candidate, .binding, .index, .capture, .restore, .queue, .publication}
  complete operation := by cases operation <;> simp

abbrev Ledger := Operation → Nat

def unit (operation : Operation) : Ledger := fun observed => if observed = operation then 1 else 0

def agenda : Ledger := unit .capture + unit .restore + unit .queue

def price (prices : Operation → Nat) (ledger : Ledger) : Nat :=
  ∑ operation, prices operation * ledger operation

theorem price_add (prices : Operation → Nat) (first second : Ledger) :
    price prices (first + second) = price prices first + price prices second := by
  simp [price, Nat.mul_add, Finset.sum_add_distrib]

variable {Node Answer Value : Type*}

theorem fold_add [AddCommMonoid Value] (first second : Node → Value) (tree : FiniteSearchCertificate.Tree Node) :
    FiniteSearchCertificate.Tree.fold (first + second) tree = FiniteSearchCertificate.Tree.fold first tree + FiniteSearchCertificate.Tree.fold second tree := by
  induction tree using FiniteSearchCertificate.Tree.rec
    (motive_2 := fun children =>
      (children.map (FiniteSearchCertificate.Tree.fold (first + second))).sum =
        (children.map (FiniteSearchCertificate.Tree.fold first)).sum + (children.map (FiniteSearchCertificate.Tree.fold second)).sum) with
  | branch node children ih => simp only [FiniteSearchCertificate.Tree.fold, Pi.add_apply, ih]; ac_rfl
  | nil => simp
  | cons head tail headIH tailIH =>
      simp only [List.map_cons, List.sum_cons, headIH, tailIH]
      ac_rfl

theorem fold_scale (multiplier : Nat) (tree : FiniteSearchCertificate.Tree Node) :
    FiniteSearchCertificate.Tree.fold (fun _ => multiplier) tree = multiplier * FiniteSearchCertificate.Tree.fold (fun _ => (1 : Nat)) tree := by
  induction tree using FiniteSearchCertificate.Tree.rec
    (motive_2 := fun children =>
      (children.map (FiniteSearchCertificate.Tree.fold (fun _ => multiplier))).sum =
        multiplier * (children.map (FiniteSearchCertificate.Tree.fold (fun _ => (1 : Nat)))).sum) with
  | branch node children ih => simp [FiniteSearchCertificate.Tree.fold, ih, Nat.mul_add]
  | nil => simp
  | cons head tail headIH tailIH =>
      simp [List.map_cons, List.sum_cons, headIH, tailIH, Nat.mul_add]

theorem fold_coordinate (charge : Node → Ledger) (tree : FiniteSearchCertificate.Tree Node) (operation : Operation) :
    FiniteSearchCertificate.Tree.fold charge tree operation = FiniteSearchCertificate.Tree.fold (fun node => charge node operation) tree := by
  induction tree using FiniteSearchCertificate.Tree.rec
    (motive_2 := fun children =>
      (children.map (FiniteSearchCertificate.Tree.fold charge)).sum operation =
        (children.map (FiniteSearchCertificate.Tree.fold (fun node => charge node operation))).sum) with
  | branch node children ih => simp only [FiniteSearchCertificate.Tree.fold, Pi.add_apply, ih]
  | nil => rfl
  | cons head tail headIH tailIH =>
      simp only [List.map_cons, List.sum_cons, Pi.add_apply, headIH, tailIH]

def selective (base : Node → Ledger) (tree : FiniteSearchCertificate.Tree Node) : Ledger :=
  FiniteSearchCertificate.Tree.fold (fun node => base node + agenda) tree

def bulk (base : Node → Ledger) (tree : FiniteSearchCertificate.Tree Node) : Ledger := FiniteSearchCertificate.Tree.fold base tree

/-- Every actual certified source node contributes its base work exactly once
in both modes. The difference is the explicitly charged agenda protocol. -/
theorem selective_bulk_exact (base : Node → Ledger) (tree : FiniteSearchCertificate.Tree Node)
    (operation : Operation) :
    selective base tree operation = bulk base tree operation +
      agenda operation * FiniteSearchCertificate.Tree.fold (fun _ => (1 : Nat)) tree := by
  change (FiniteSearchCertificate.Tree.fold (base + (fun _ : Node => agenda)) tree : Ledger) operation =
    bulk base tree operation + agenda operation * FiniteSearchCertificate.Tree.fold (fun _ => 1) tree
  rw [fold_add, Pi.add_apply]
  apply congrArg (fun amount => bulk base tree operation + amount)
  rw [fold_coordinate, fold_scale]

theorem bulk_no_more (prices : Operation → Nat) (base : Node → Ledger) (tree : FiniteSearchCertificate.Tree Node) :
    price prices (bulk base tree) ≤ price prices (selective base tree) := by
  change price prices (bulk base tree) ≤
    price prices (FiniteSearchCertificate.Tree.fold (base + (fun _ => agenda)) tree)
  rw [fold_add, price_add]
  exact Nat.le_add_right _ _

/-- A bounded producer exposes one successor at a time. No answer suffix is
materialized by constructing its initial work item. -/
def producer (count : Nat) : BranchingSystem Nat Nat where
  emit position := if position < count then some position else none
  successors position := if position + 1 < count then [position + 1] else []

def countingController : InferenceControl.Controller Nat Nat Nat where
  initialMemory := 0
  scheduler _ := Scheduler.breadthFirst
  advance visits _ _ _ := visits + 1

def producerState (count visited : Nat) : InferenceControl.Snapshot Nat Nat Nat where
  search :=
    { events := (List.range visited).map (fun position => ⟨position, position⟩)
      frontier := if visited < count then [visited] else [] }
  memory := visited

theorem producer_initial (count : Nat) :
    InferenceControl.Snapshot.initial countingController
      (if count = 0 then [] else [0]) = producerState count 0 := by
  by_cases empty : count = 0
  · subst count; rfl
  · have positive : 0 < count := by omega
    simp [InferenceControl.Snapshot.initial, BranchingTemporal.initial,
      countingController, producerState, empty, positive]

private theorem producer_tick (count visited : Nat) (live : visited < count) :
    InferenceControl.Snapshot.tick (producer count) countingController
      (producerState count visited) = producerState count (visited + 1) := by
  by_cases next : visited + 1 < count
  · simp [InferenceControl.Snapshot.tick, BranchingTemporal.tick, countingController,
      Scheduler.breadthFirst, producerState, producer, live, next,
      List.range_succ, List.map_append]
    rfl
  · simp [InferenceControl.Snapshot.tick, BranchingTemporal.tick, countingController,
      Scheduler.breadthFirst, producerState, producer, live, next,
      List.range_succ, List.map_append]
    rfl

/-- The visit counter records actual expansions of the existing controller,
not a prescribed minimum of two numbers. -/
theorem producer_run (count visited : Nat) (within : visited ≤ count) :
    InferenceControl.Snapshot.run (producer count) countingController visited
      (producerState count 0) = producerState count visited := by
  induction visited with
  | zero => rfl
  | succ visited ih =>
      rw [InferenceControl.Snapshot.run, ih (by omega)]
      exact producer_tick count visited (by omega)

/-- Demand stops at the requested source prefix, retaining the unforced suffix
in its frontier. The allowance and demand are both the requested count. -/
theorem producer_demand (count requested : Nat) (enough : requested ≤ count) :
    DemandExecution.run (producer count) countingController
      (DemandExecution.atLeast requested) requested (producerState count 0) =
        producerState count requested := by
  obtain ⟨used, bound, correspondence⟩ := DemandExecution.run_prefix (producer count)
    countingController (DemandExecution.atLeast requested) requested (producerState count 0)
  have observed : DemandExecution.run (producer count) countingController
      (DemandExecution.atLeast requested) requested (producerState count 0) =
        producerState count used := correspondence.trans (producer_run count used (by omega))
  have fullStopped : DemandExecution.stopped (DemandExecution.atLeast requested)
      (InferenceControl.Snapshot.run (producer count) countingController requested
        (producerState count 0)) = true := by
    rw [producer_run count requested enough]
    simp [DemandExecution.stopped, DemandExecution.satisfied, DemandExecution.answers,
      DemandExecution.atLeast, producerState]
  have stopped := DemandExecution.stopped_of_full_run (producer count) countingController
    (DemandExecution.atLeast requested) requested (producerState count 0) fullStopped
  rw [observed] at stopped
  have exactUsed : used = requested := by
    by_contra different
    have before : used < requested := by omega
    have live : used < count := by omega
    simp [DemandExecution.stopped, DemandExecution.satisfied, DemandExecution.answers,
      DemandExecution.atLeast, DemandExecution.closed, producerState, live,
      Nat.not_le.mpr before] at stopped
  simpa [exactUsed] using observed

def completeTree (position : Nat) : Nat → FiniteSearchCertificate.Tree Nat
  | 0 => .branch position []
  | remaining + 1 => .branch position [completeTree (position + 1) remaining]

theorem completeTree_size (position remaining : Nat) :
    FiniteSearchCertificate.Tree.fold (fun _ => (1 : Nat)) (completeTree position remaining) =
      remaining + 1 := by
  induction remaining generalizing position with
  | zero => simp [completeTree, FiniteSearchCertificate.Tree.fold]
  | succ remaining ih => simp [completeTree, FiniteSearchCertificate.Tree.fold, ih]; omega

/-- The cost example's tree is the completed unfolding of its actual producer,
including its terminal node. The source builder independently checks it. -/
theorem producer_tree (position remaining : Nat) :
    FiniteSearchCertificate.build (producer (position + remaining + 1))
      (remaining + 1) position = some (completeTree position remaining) := by
  induction remaining generalizing position with
  | zero =>
      simp [FiniteSearchCertificate.build, FiniteSearchCertificate.collect,
        producer, completeTree]
  | succ remaining ih =>
      have live : position + 1 < position + (remaining + 1) + 1 := by omega
      have child := ih (position + 1)
      have same : (position + 1) + remaining + 1 = position + (remaining + 1) + 1 := by omega
      rw [same] at child
      have children : (producer (position + (remaining + 1) + 1)).successors position =
          [position + 1] := by simp only [producer, live, if_pos]
      rw [FiniteSearchCertificate.build, children]
      simp [FiniteSearchCertificate.collect, child, completeTree]

theorem producer_complete_visits (remaining : Nat) :
    (InferenceControl.Snapshot.run (producer (remaining + 1)) countingController
      (remaining + 1) (producerState (remaining + 1) 0)).memory =
        FiniteSearchCertificate.Tree.fold (fun _ => (1 : Nat)) (completeTree 0 remaining) := by
  rw [producer_run _ _ le_rfl, completeTree_size]
  rfl

/-- In this productive family, a fixed prefix performs a fixed number of
actual source expansions, whereas exhaustive execution performs all of them. -/
theorem fixed_prefix_unbounded_savings (requested extra : Nat) :
    let count := requested + extra
    let partialState := DemandExecution.run (producer count) countingController
      (DemandExecution.atLeast requested) requested (producerState count 0)
    let exhaustive := InferenceControl.Snapshot.run (producer count) countingController
      count (producerState count 0)
    partialState.memory = requested ∧ exhaustive.memory - partialState.memory = extra := by
  dsimp only
  rw [producer_demand (requested + extra) requested (Nat.le_add_right _ _),
    producer_run (requested + extra) (requested + extra) le_rfl]
  simp [producerState]

namespace Controls

def base (_ : Nat) : Ledger := unit .candidate + unit .binding + unit .index + unit .publication

example : selective base (completeTree 0 9) .queue = 10 := by
  rw [selective_bulk_exact, completeTree_size]
  have : bulk base (completeTree 0 9) .queue = 0 := by
    simp [bulk, base, FiniteSearchCertificate.Tree.fold, completeTree, unit]
  simp [this, agenda, unit]

example : bulk base (completeTree 0 9) .publication = 10 := by
  rw [bulk, fold_coordinate]
  change FiniteSearchCertificate.Tree.fold (fun _ => (1 : Nat)) (completeTree 0 9) = 10
  exact completeTree_size 0 9

example : (DemandExecution.run (producer 200) countingController
    (DemandExecution.atLeast 7) 7 (producerState 200 0)).memory = 7 := by decide +kernel

example : (DemandExecution.run (producer 200) countingController
    (DemandExecution.atLeast 7) 7 (producerState 200 0)).search.frontier = [7] :=
  by decide +kernel

example : (InferenceControl.Snapshot.run (producer 200) countingController
    200 (producerState 200 0)).memory = 200 := by decide +kernel

/- The competitive theorem is conditional on the fixed-price model. Its
existing state-dependent-cost control refuses a universal evaluator bound. -/
example : Mettapedia.Algorithms.OnlineBulkSwitch.Receipt.total
    (Mettapedia.Algorithms.OnlineBulkSwitch.execute 5 20 0) ≤
      2 * min 20 5 := by
  exact Mettapedia.Algorithms.OnlineBulkSwitch.competitive _ _

end Controls

end Mettapedia.GSLT.Core.SourceExecutionCosts
