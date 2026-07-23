import Mettapedia.Languages.MeTTa.PrimeNeedReferenceSemantics

/-!
# Prime recursive-workload reference instance

This module immediately instantiates `PrimeNeedReference` with the first-order
fragment exercised by the pinned recursion probes:

* natural literals and strict arithmetic results;
* equation-style `sum` and `fib` calls;
* occurrence-sensitive choice;
* repeated demand of one shared cell;
* deliberate resampling into a fresh cell;
* stable and retryable failures; and
* an explicit effect followed by a value.

The instance is an executable semantic projection, not a second MeTTa
implementation.  Its constructors correspond to existing evaluator
mechanisms: literals and arithmetic to grounded dispatch, `sum`/`fib` to
equation selection and recursive application, and `choose` to ordered
superposition.  The generic Need machine continues to own cells, worlds,
branching, caching, retry, and receipts.
-/

namespace Mettapedia.Languages.MeTTa.PrimeRecursionReference

open PrimeNeedReference

/-- Minimal origins needed to distinguish accidental per-path overhead from
the intentional Fibonacci call tree. -/
inductive Origin where
  | literal (value : Nat)
  | sum (argument : Nat)
  | fib (argument : Nat)
  | choose (values : List Nat)
  | twice (origin : Origin)
  | resampleTwice (origin : Origin)
  | stable (fault : Nat)
  | retryable (fault : Nat)
  | effectThen (effect value : Nat)
deriving DecidableEq, Repr

inductive Rule where
  | literal
  | sumZero
  | sumSucc
  | fibBase
  | fibStep
  | choose (occurrence : Nat)
  | twice
  | resampleTwice
  | stable
  | retryable
  | effectThen
deriving DecidableEq, Repr

abbrev Outcome := Produced Nat Nat Nat

/-- Local states make every recursive allocation and demand explicit. -/
inductive Local where
  | output (outcome : Outcome)
  | sumAllocate (predecessor : Nat)
  | sumDemand (cell : CellId)
  | fibAllocateLeft (left right : Nat)
  | fibAllocateRight (left : CellId) (right : Nat)
  | fibDemandLeft (left right : CellId)
  | fibDemandRight (leftValue : Nat) (right : CellId)
  | twiceAllocate (origin : Origin)
  | twiceDemandFirst (cell : CellId)
  | twiceDemandSecond (cell : CellId) (firstValue : Nat)
  | resampleAllocate (origin : Origin)
  | resampleDemandFirst (cell : CellId)
  | resampleFresh (source : CellId) (firstValue : Nat)
  | resampleDemandSecond (fresh : CellId) (firstValue : Nat)
  | perform (effect value : Nat)
deriving DecidableEq, Repr

inductive Resume where
  | sumAllocated
  | sumReturned
  | fibLeftAllocated (right : Nat)
  | fibRightAllocated (left : CellId)
  | fibLeftReturned (right : CellId)
  | fibRightReturned (leftValue : Nat)
  | twiceAllocated
  | twiceFirstReturned (cell : CellId)
  | twiceSecondReturned (firstValue : Nat)
  | resampleAllocated
  | resampleFirstReturned (source : CellId)
  | resampleFreshAllocated (firstValue : Nat)
  | resampleSecondReturned (firstValue : Nat)
deriving DecidableEq, Repr

private def choiceAlternatives : Nat → List Nat → List (Rule × Local)
  | _, [] => []
  | occurrence, value :: rest =>
      (.choose occurrence, .output (.value value)) ::
        choiceAlternatives (occurrence + 1) rest

def alternatives : Origin → List (Rule × Local)
  | .literal value => [(.literal, .output (.value value))]
  | .sum 0 => [(.sumZero, .output (.value 0))]
  | .sum (Nat.succ predecessor) =>
      [(.sumSucc, .sumAllocate predecessor)]
  | .fib 0 => [(.fibBase, .output (.value 0))]
  | .fib 1 => [(.fibBase, .output (.value 1))]
  | .fib (Nat.succ (Nat.succ predecessor)) =>
      [(.fibStep, .fibAllocateLeft (predecessor + 1) predecessor)]
  | .choose values => choiceAlternatives 0 values
  | .twice origin => [(.twice, .twiceAllocate origin)]
  | .resampleTwice origin =>
      [(.resampleTwice, .resampleAllocate origin)]
  | .stable fault => [(.stable, .output (.stableFault fault))]
  | .retryable fault =>
      [(.retryable, .output (.retryableFault (.domain fault)))]
  | .effectThen effect value =>
      [(.effectThen, .perform effect value)]

private def continueValue (outcome : Outcome) (next : Nat → Local) : Local :=
  match outcome with
  | .value value => next value
  | .stableFault fault => .output (.stableFault fault)
  | .retryableFault reason => .output (.retryableFault reason)

def action :
    Local → Action Origin Local Resume Nat Nat Nat Nat
  | .output outcome => .done outcome
  | .sumAllocate predecessor => .allocate (.sum predecessor) .sumAllocated
  | .sumDemand cell => .demand cell .sumReturned
  | .fibAllocateLeft left right =>
      .allocate (.fib left) (.fibLeftAllocated right)
  | .fibAllocateRight left right =>
      .allocate (.fib right) (.fibRightAllocated left)
  | .fibDemandLeft left right =>
      .demand left (.fibLeftReturned right)
  | .fibDemandRight leftValue right =>
      .demand right (.fibRightReturned leftValue)
  | .twiceAllocate origin => .allocate origin .twiceAllocated
  | .twiceDemandFirst cell =>
      .demand cell (.twiceFirstReturned cell)
  | .twiceDemandSecond cell firstValue =>
      .demand cell (.twiceSecondReturned firstValue)
  | .resampleAllocate origin => .allocate origin .resampleAllocated
  | .resampleDemandFirst cell =>
      .demand cell (.resampleFirstReturned cell)
  | .resampleFresh source firstValue =>
      .resample source (.resampleFreshAllocated firstValue)
  | .resampleDemandSecond fresh firstValue =>
      .demand fresh (.resampleSecondReturned firstValue)
  | .perform effect value =>
      .perform effect (.output (.value value))

def afterDemand : Resume → Outcome → Local
  | .sumReturned, outcome =>
      continueValue outcome fun value => .output (.value (value + 1))
  | .fibLeftReturned right, outcome =>
      continueValue outcome fun value => .fibDemandRight value right
  | .fibRightReturned leftValue, outcome =>
      continueValue outcome fun rightValue =>
        .output (.value (leftValue + rightValue))
  | .twiceFirstReturned cell, outcome =>
      continueValue outcome fun value => .twiceDemandSecond cell value
  | .twiceSecondReturned firstValue, outcome =>
      continueValue outcome fun secondValue =>
        .output (.value (firstValue + secondValue))
  | .resampleFirstReturned source, outcome =>
      continueValue outcome fun value => .resampleFresh source value
  | .resampleSecondReturned firstValue, outcome =>
      continueValue outcome fun secondValue =>
        .output (.value (firstValue + secondValue))
  | .sumAllocated, outcome => .output outcome
  | .fibLeftAllocated _, outcome => .output outcome
  | .fibRightAllocated _, outcome => .output outcome
  | .twiceAllocated, outcome => .output outcome
  | .resampleAllocated, outcome => .output outcome
  | .resampleFreshAllocated _, outcome => .output outcome

def afterAllocation : Resume → CellId → Local
  | .sumAllocated, cell => .sumDemand cell
  | .fibLeftAllocated right, left =>
      .fibAllocateRight left right
  | .fibRightAllocated left, right =>
      .fibDemandLeft left right
  | .twiceAllocated, cell => .twiceDemandFirst cell
  | .resampleAllocated, cell => .resampleDemandFirst cell
  | .resampleFreshAllocated firstValue, fresh =>
      .resampleDemandSecond fresh firstValue
  | .sumReturned, _ => .output (.retryableFault (.domain 0))
  | .fibLeftReturned _, _ => .output (.retryableFault (.domain 0))
  | .fibRightReturned _, _ => .output (.retryableFault (.domain 0))
  | .twiceFirstReturned _, _ => .output (.retryableFault (.domain 0))
  | .twiceSecondReturned _, _ => .output (.retryableFault (.domain 0))
  | .resampleFirstReturned _, _ => .output (.retryableFault (.domain 0))
  | .resampleSecondReturned _, _ =>
      .output (.retryableFault (.domain 0))

def recursionSpec : Spec Origin Local Resume Rule Nat Nat Nat Nat where
  alternatives := alternatives
  action := action
  afterDemand := afterDemand
  afterAllocation := afterAllocation

def rootCell (lineage : LineageId := 1) : CellId :=
  { lineage := lineage, birth := [], slot := 0, generation := 0 }

def initialHeap (lineage : LineageId) (origin : Origin) :
    Heap Origin Nat Nat :=
  let root := rootCell lineage
  let record : CellRecord Origin Nat Nat :=
    { origin := origin, cache := .suspended }
  { current := fun cell => if cell = root then some record else none
    spine := [.allocate root origin] }

def initialWorld (origin : Origin) (lineage : LineageId := 1) :
    World Origin Rule Nat Nat Nat Nat where
  lineage := lineage
  path := []
  heap := initialHeap lineage origin
  receipts := ReceiptGraph.empty
  nextCell := 1
  nextEvaluator := 1

def initialMachine (origin : Origin) (lineage : LineageId := 1) :
    Machine Origin Local Resume Rule Nat Nat Nat Nat where
  world := initialWorld origin lineage
  control := .force (rootCell lineage) []

@[simp] theorem initial_lookup (origin : Origin) (lineage : LineageId) :
    (initialWorld origin lineage).heap.lookup (rootCell lineage) =
      some { origin := origin, cache := Cache.suspended } := by
  simp [initialWorld, initialHeap, rootCell, Heap.lookup]

/-- Completed answer bag after a bounded number of semantic machine steps. -/
def runAnswers (fuel : Nat) (origin : Origin) : List Outcome :=
  PrimeNeedReference.answers recursionSpec fuel (initialMachine origin)

/-- Work records of completed branches, used by the later linear-depth
theorem and its pinned runtime refinement. -/
def completedWork (fuel : Nat) (origin : Origin) : List Work :=
  (PrimeNeedReference.runFrontier recursionSpec fuel [initialMachine origin])
    |>.filterMap fun machine =>
      match machine.control with
      | .halted _ => some machine.work
      | _ => none

/-! ## Executable non-vacuity witnesses

The fuel constants are semantic-step budgets, not performance claims.  They
are deliberately generous so these witnesses remain stable while the machine
is refined by proven administrative-step equivalences.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 200000

example : runAnswers 80 (.sum 3) = [.value 3] := by
  decide

example : runAnswers 120 (.fib 3) = [.value 2] := by
  decide

/-- Same-cell call-time choice permits `2` and `4`, but never the mixed sum
`3`: both demands observe one cached branch outcome. -/
example :
    runAnswers 100 (.twice (.choose [1, 2])) = [.value 2, .value 4] := by
  decide

/-- Explicit resampling creates independent cells.  The middle result has
multiplicity two because two distinct branch occurrences produce it. -/
example :
    runAnswers 140 (.resampleTwice (.choose [1, 2])) =
      [.value 2, .value 3, .value 3, .value 4] := by
  decide

/-- Negative: ordinary sharing cannot manufacture the mixed result. -/
example :
    Produced.value 3 ∉ runAnswers 100 (.twice (.choose [1, 2])) := by
  decide

example : runAnswers 30 (.stable 7) = [.stableFault 7] := by
  decide

example :
    runAnswers 30 (.retryable 9) = [.retryableFault (.domain 9)] := by
  decide

example : runAnswers 40 (.effectThen 11 7) = [.value 7] := by
  decide

end Mettapedia.Languages.MeTTa.PrimeRecursionReference
