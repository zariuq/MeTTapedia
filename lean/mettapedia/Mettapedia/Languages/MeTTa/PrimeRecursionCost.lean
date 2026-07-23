import Mettapedia.Languages.MeTTa.PrimeRecursionReference
import Mettapedia.Languages.MeTTa.PrimeNeedExecutionMachine

/-!
# Exact work for the Prime recursive reference machine

This module connects a machine-free arithmetic cost specification directly to
finite paths of the rich Prime Need machine.  The load-bearing result is a
balanced macro-execution theorem: forcing `sum n` returns to an arbitrary
continuation stack, starting from arbitrary work counters, with an exact
closed-form work delta.

The heap invariant is about allocation safety, not a model of execution cost.
It states that every live cell belongs to the world's lineage and has a slot
below the next allocation slot.  This makes allocation success a theorem and
keeps the cost proof independent of the finite-map representation.
-/

namespace Mettapedia.Languages.MeTTa.PrimeRecursionCost

open PrimeNeedReference
open PrimeRecursionReference

abbrev RecWorld := World Origin Rule Nat Nat Nat Nat
abbrev RecMachine := Machine Origin Local Resume Rule Nat Nat Nat Nat

/-- Work performed from forcing a suspended `sum n` cell through returning
its value to the caller.  The final halt transition is intentionally absent. -/
def sumForceCost (n : Nat) : Work :=
  { transitions := 6 * n + 3
    heapLookups := 3 * n + 2
    heapUpdates := 3 * n + 2
    receiptAppends := 4 * n + 3
    allocations := n }

/-- Complete work from the initial `sum n` machine through its halted answer. -/
def sumCost (n : Nat) : Work :=
  { transitions := 6 * n + 4
    heapLookups := 3 * n + 2
    heapUpdates := 3 * n + 2
    receiptAppends := 4 * n + 3
    allocations := n }

def haltCost : Work := Work.operation 0 0 0 0

theorem sumCost_eq_force_add_halt (n : Nat) :
    sumCost n = (sumForceCost n).add haltCost := by
  simp [sumCost, sumForceCost, haltCost, Work.add, Work.operation]

/-- Every live cell is below the monotone next-allocation slot. -/
def HeapBounded (world : RecWorld) : Prop :=
  ∀ cell record,
    world.heap.lookup cell = some record →
      cell.lineage = world.lineage ∧ cell.slot < world.nextCell

namespace HeapBounded

theorem fresh_lookup_none
    {world : RecWorld} (bounded : HeapBounded world) (generation : Nat) :
    world.heap.lookup (world.freshCell generation) = none := by
  cases hLookup :
      world.heap.lookup (world.freshCell generation) with
  | none => rfl
  | some record =>
      have hBound := (bounded _ _ hLookup).2
      simp [World.freshCell] at hBound

theorem fork
    {world : RecWorld} (bounded : HeapBounded world) (branch : Nat) :
    HeapBounded (world.fork branch) := by
  simpa [HeapBounded, World.fork] using bounded

theorem record
    {world : RecWorld} (bounded : HeapBounded world)
    (payload : ReceiptPayload Origin Rule Nat Nat Nat Nat) :
    HeapBounded (world.record payload).1 := by
  simpa [HeapBounded, World.record, ReceiptGraph.append] using bounded

theorem recorded
    {world : RecWorld} (bounded : HeapBounded world)
    (payload : ReceiptPayload Origin Rule Nat Nat Nat Nat) :
    HeapBounded (PrimeNeedReference.recorded world payload) :=
  record bounded payload

theorem setKnownCache
    {world : RecWorld} (bounded : HeapBounded world)
    {cell : CellId} {record : CellRecord Origin Nat Nat}
    (hLookup : world.heap.lookup cell = some record)
    (state : Cache Nat Nat) :
    HeapBounded (world.setKnownCache cell record state) := by
  intro other otherRecord hOther
  by_cases hCell : other = cell
  · subst other
    exact bounded cell record hLookup
  · apply bounded other otherRecord
    rw [← Heap.setKnownCache_preserves_other
      world.heap record state hCell]
    exact hOther

theorem allocation_exists
    {world : RecWorld} (bounded : HeapBounded world)
    (origin : Origin) (generation : Nat := 0) :
    ∃ next cell, world.allocate? origin generation = some (next, cell) := by
  let cell := world.freshCell generation
  have hFresh : world.heap.lookup cell = none := by
    exact fresh_lookup_none bounded generation
  let heap : Heap Origin Nat Nat :=
    { current :=
        Function.update world.heap.current cell
          (some { origin := origin, cache := Cache.suspended })
      spine := .allocate cell origin :: world.heap.spine }
  let advanced : RecWorld :=
    { world with heap := heap, nextCell := world.nextCell + 1 }
  let next := (advanced.record (.allocate cell origin)).1
  exact ⟨next, cell, by
    simp [World.allocate?, Heap.allocate?, cell, hFresh, heap, advanced, next]⟩

theorem allocate
    {world next : RecWorld} (bounded : HeapBounded world)
    {origin : Origin} {generation : Nat} {cell : CellId}
    (hAllocate :
      world.allocate? origin generation = some (next, cell)) :
    HeapBounded next := by
  intro other otherRecord hOtherLookup
  have hNext := World.allocate?_nextCell hAllocate
  have hLineage := World.allocate?_lineage hAllocate
  by_cases hCell : other = cell
  · subst other
    have hFresh := World.allocate?_fresh_cell hAllocate
    rw [hFresh]
    constructor
    · simp [World.freshCell, hLineage]
    · simp [World.freshCell, hNext]
  · have hOldLookup :
        world.heap.lookup other = some otherRecord := by
      rw [← World.allocate?_preserves_other hAllocate hCell]
      exact hOtherLookup
    have hOldBound := bounded other otherRecord hOldLookup
    constructor
    · simpa [hLineage] using hOldBound.1
    · omega

end HeapBounded

theorem initial_heapBounded (origin : Origin) (lineage : LineageId := 1) :
    HeapBounded (initialWorld origin lineage) := by
  intro cell record hLookup
  change
    (if cell = rootCell lineage then
      some { origin := origin, cache := Cache.suspended }
    else none) = some record at hLookup
  split at hLookup
  · rename_i hCell
    subst cell
    simp [initialWorld, rootCell]
  · contradiction

/-- An entry cell is live, suspended with the requested origin, and belongs to
a collision-free heap.  The initial machine inhabits this predicate. -/
structure EntryInv (world : RecWorld) (cell : CellId)
    (origin : Origin) : Prop where
  bounded : HeapBounded world
  lookup :
    world.heap.lookup cell =
      some { origin := origin, cache := Cache.suspended }

theorem initial_entry (origin : Origin) (lineage : LineageId := 1) :
    EntryInv (initialWorld origin lineage) (rootCell lineage) origin where
  bounded := initial_heapBounded origin lineage
  lookup := initial_lookup origin lineage

/-- Existing live cells other than the evaluated target retain their
extensional heap observations.  Newly allocated cells are unconstrained. -/
def PreservesLiveOther
    (before after : RecWorld) (target : CellId) : Prop :=
  ∀ other record,
    other ≠ target →
    before.heap.lookup other = some record →
    after.heap.lookup other = some record

theorem singletonUniqueSteps
    {spec : Spec Origin Local Resume Rule Nat Nat Nat Nat}
    {machine next : RecMachine}
    (hStep : PrimeNeedReference.step spec machine = [next]) :
    UniqueSteps spec 1 machine next :=
  UniqueSteps.cons hStep (UniqueSteps.refl next)

/-- Balanced base case for the actual rich machine. -/
theorem sum_zero_macro
    (world : RecWorld) (cell : CellId) (stack : List (Frame Resume))
    (work : Work) (entry : EntryInv world cell (.sum 0)) :
    ∃ finalWorld,
      UniqueSteps recursionSpec 3
        { world := world, control := .force cell stack, work := work }
        { world := finalWorld
          control := .returned (.value 0) stack
          work := work.add (sumForceCost 0) } ∧
      HeapBounded finalWorld ∧
      finalWorld.heap.lookup cell =
        some { origin := .sum 0, cache := Cache.value 0 } ∧
      PreservesLiveOther world finalWorld cell ∧
      finalWorld.nextCell = world.nextCell ∧
      finalWorld.lineage = world.lineage := by
  let record : CellRecord Origin Nat Nat :=
    { origin := .sum 0, cache := .suspended }
  let owner := world.nextEvaluator
  let base : RecWorld := { world with nextEvaluator := owner + 1 }
  let evaluatingWorld : RecWorld :=
    let selected :=
      (base.fork 0).setKnownCache cell record (.evaluating owner)
    let selected := PrimeNeedReference.recorded selected (.evaluate cell owner)
    PrimeNeedReference.recorded selected (.chooseRule cell .sumZero)
  let evaluatingRecord : CellRecord Origin Nat Nat :=
    { origin := .sum 0, cache := .evaluating owner }
  let start : RecMachine :=
    { world := world, control := .force cell stack, work := work }
  let selected : RecMachine :=
    { world := evaluatingWorld
      control := .run (.output (.value 0)) (.commit cell owner :: stack)
      work := work.bump 1 1 2 0 }
  let produced : RecMachine :=
    { world := evaluatingWorld
      control := .returned (.value 0) (.commit cell owner :: stack)
      work := (work.bump 1 1 2 0).bump 0 0 0 0 }
  let finalWorld : RecWorld :=
    let cached :=
      evaluatingWorld.setKnownCache cell evaluatingRecord (.value 0)
    PrimeNeedReference.recorded cached (.observe cell (.value 0))
  let finished : RecMachine :=
    { world := finalWorld
      control := .returned (.value 0) stack
      work := work.add (sumForceCost 0) }
  have hEvaluating :
      evaluatingWorld.heap.lookup cell = some evaluatingRecord := by
    change
      ((base.fork 0).heap.setKnownCache cell record (.evaluating owner)).lookup
          cell =
        some evaluatingRecord
    simp [record, evaluatingRecord]
  have hStart : start =
      { world := world, control := .force cell stack, work := work } := rfl
  have hStep1 : PrimeNeedReference.step recursionSpec start = [selected] := by
    simp [start, selected, PrimeNeedReference.step, recursionSpec,
      alternatives, entry.lookup, branchAlternatives, evaluatingWorld,
      owner, base, record, PrimeNeedReference.recorded, World.record,
      ReceiptGraph.append, PrimeNeedReference.finished]
  have hStep2 :
      PrimeNeedReference.step recursionSpec selected = [produced] := by
    simp [selected, produced, PrimeNeedReference.step, recursionSpec, action,
      PrimeNeedReference.finished]
  have hStep3 :
      PrimeNeedReference.step recursionSpec produced = [finished] := by
    simp [produced, finished, finalWorld, PrimeNeedReference.step,
      hEvaluating, evaluatingRecord, owner, PrimeNeedReference.recorded,
      World.record, ReceiptGraph.append, PrimeNeedReference.finished,
      sumForceCost, Work.add, Work.bump]
  have hExecution : UniqueSteps recursionSpec 3 start finished := by
    exact UniqueSteps.trans recursionSpec (singletonUniqueSteps hStep1)
      (UniqueSteps.trans recursionSpec (singletonUniqueSteps hStep2)
        (singletonUniqueSteps hStep3))
  have hBaseBounded : HeapBounded base := by
    intro other otherRecord hOther
    exact entry.bounded other otherRecord hOther
  have hEvaluatingBounded : HeapBounded evaluatingWorld := by
    apply HeapBounded.recorded
    apply HeapBounded.recorded
    apply HeapBounded.setKnownCache
      (HeapBounded.fork hBaseBounded 0)
    change world.heap.lookup cell = some record
    simpa [record] using entry.lookup
  have hFinalBounded : HeapBounded finalWorld := by
    apply HeapBounded.recorded
    exact HeapBounded.setKnownCache hEvaluatingBounded hEvaluating (.value 0)
  refine ⟨finalWorld, ?_, hFinalBounded, ?_, ?_, rfl, rfl⟩
  · simpa [hStart, finished] using hExecution
  · change
      (evaluatingWorld.heap.setKnownCache cell evaluatingRecord
          (.value 0)).lookup cell =
        some { origin := .sum 0, cache := Cache.value 0 }
    simp [evaluatingRecord]
  · intro other otherRecord hOther hLookup
    simp [finalWorld, evaluatingWorld, base, record,
      PrimeNeedReference.recorded, World.record, ReceiptGraph.append,
      World.setKnownCache, Heap.setKnownCache, Heap.lookup, hOther]
    exact hLookup

/-- Forcing `sum n` is a balanced execution over the actual rich transition
system.  It is uniform in the continuation stack and the starting work
counters, and it returns an exact machine-free work delta. -/
theorem sum_macro
    (n : Nat) (world : RecWorld) (cell : CellId)
    (stack : List (Frame Resume)) (work : Work)
    (entry : EntryInv world cell (.sum n)) :
    ∃ finalWorld,
      UniqueSteps recursionSpec (6 * n + 3)
        { world := world, control := .force cell stack, work := work }
        { world := finalWorld
          control := .returned (.value n) stack
          work := work.add (sumForceCost n) } ∧
      HeapBounded finalWorld ∧
      finalWorld.heap.lookup cell =
        some { origin := .sum n, cache := Cache.value n } ∧
      PreservesLiveOther world finalWorld cell ∧
      finalWorld.nextCell = world.nextCell + n ∧
      finalWorld.lineage = world.lineage := by
  induction n generalizing world cell stack work with
  | zero =>
      simpa using sum_zero_macro world cell stack work entry
  | succ n ih =>
      let record : CellRecord Origin Nat Nat :=
        { origin := .sum (n + 1), cache := .suspended }
      let owner := world.nextEvaluator
      let base : RecWorld := { world with nextEvaluator := owner + 1 }
      let evaluatingWorld : RecWorld :=
        let selected :=
          (base.fork 0).setKnownCache cell record (.evaluating owner)
        let selected :=
          PrimeNeedReference.recorded selected (.evaluate cell owner)
        PrimeNeedReference.recorded selected (.chooseRule cell .sumSucc)
      let evaluatingRecord : CellRecord Origin Nat Nat :=
        { origin := .sum (n + 1), cache := .evaluating owner }
      let start : RecMachine :=
        { world := world, control := .force cell stack, work := work }
      let selected : RecMachine :=
        { world := evaluatingWorld
          control := .run (.sumAllocate n) (.commit cell owner :: stack)
          work := work.bump 1 1 2 0 }
      have hBaseBounded : HeapBounded base := by
        intro other otherRecord hOther
        exact entry.bounded other otherRecord hOther
      have hEvaluating :
          evaluatingWorld.heap.lookup cell = some evaluatingRecord := by
        change
          ((base.fork 0).heap.setKnownCache cell record
              (.evaluating owner)).lookup cell =
            some evaluatingRecord
        simp [record, evaluatingRecord]
      have hEvaluatingBounded : HeapBounded evaluatingWorld := by
        apply HeapBounded.recorded
        apply HeapBounded.recorded
        apply HeapBounded.setKnownCache
          (HeapBounded.fork hBaseBounded 0)
        change world.heap.lookup cell = some record
        simpa [record, Nat.succ_eq_add_one] using entry.lookup
      obtain ⟨childWorld, child, hAllocate⟩ :=
        HeapBounded.allocation_exists hEvaluatingBounded (.sum n) 0
      let allocated : RecMachine :=
        { world := childWorld
          control := .run (.sumDemand child) (.commit cell owner :: stack)
          work := (work.bump 1 1 2 0).bump 1 1 1 1 }
      let childStart : RecMachine :=
        { world := childWorld
          control :=
            .force child
              (.resume .sumReturned :: .commit cell owner :: stack)
          work := ((work.bump 1 1 2 0).bump 1 1 1 1).bump 0 0 0 0 }
      have hStep1 :
          PrimeNeedReference.step recursionSpec start = [selected] := by
        simp [start, selected, PrimeNeedReference.step, recursionSpec,
          alternatives, entry.lookup, branchAlternatives, evaluatingWorld,
          owner, base, record, PrimeNeedReference.recorded, World.record,
          ReceiptGraph.append, PrimeNeedReference.finished]
      have hStep2 :
          PrimeNeedReference.step recursionSpec selected = [allocated] := by
        simp [selected, allocated, PrimeNeedReference.step, recursionSpec,
          action, afterAllocation, hAllocate, PrimeNeedReference.finished]
      have hStep3 :
          PrimeNeedReference.step recursionSpec allocated = [childStart] := by
        simp [allocated, childStart, PrimeNeedReference.step, recursionSpec,
          action, PrimeNeedReference.finished]
      have hChildEntry : EntryInv childWorld child (.sum n) :=
        { bounded := HeapBounded.allocate hEvaluatingBounded hAllocate
          lookup := World.allocate?_lookup_same hAllocate }
      obtain
          ⟨childFinalWorld, hChildSteps, hChildBounded, hChildCached,
            hChildPreserves, hChildNext, hChildLineage⟩ :=
        ih childWorld child
          (.resume .sumReturned :: .commit cell owner :: stack)
          childStart.work hChildEntry
      have hParentBound :=
        (entry.bounded cell record (by
          simpa [record, Nat.succ_eq_add_one] using entry.lookup)).2
      have hChildFresh := World.allocate?_fresh_cell hAllocate
      have hChildSlot : child.slot = world.nextCell := by
        rw [hChildFresh]
        rfl
      have hParentNeChild : cell ≠ child := by
        intro hEqual
        have hSlots := congrArg CellId.slot hEqual
        rw [hChildSlot] at hSlots
        omega
      have hParentAllocated :
          childWorld.heap.lookup cell = some evaluatingRecord := by
        rw [World.allocate?_preserves_other hAllocate hParentNeChild]
        exact hEvaluating
      have hParentFinal :
          childFinalWorld.heap.lookup cell = some evaluatingRecord :=
        hChildPreserves cell evaluatingRecord hParentNeChild hParentAllocated
      let resumed : RecMachine :=
        { world := childFinalWorld
          control :=
            .run (.output (.value (n + 1))) (.commit cell owner :: stack)
          work := (childStart.work.add (sumForceCost n)).bump 0 0 0 0 }
      let produced : RecMachine :=
        { world := childFinalWorld
          control :=
            .returned (.value (n + 1)) (.commit cell owner :: stack)
          work :=
            ((childStart.work.add (sumForceCost n)).bump 0 0 0 0).bump
              0 0 0 0 }
      let finalWorld : RecWorld :=
        let cached :=
          childFinalWorld.setKnownCache cell evaluatingRecord (.value (n + 1))
        PrimeNeedReference.recorded cached (.observe cell (.value (n + 1)))
      let finished : RecMachine :=
        { world := finalWorld
          control := .returned (.value (n + 1)) stack
          work := work.add (sumForceCost (n + 1)) }
      have hStep4 :
          PrimeNeedReference.step recursionSpec
            { world := childFinalWorld
              control :=
                .returned (.value n)
                  (.resume .sumReturned :: .commit cell owner :: stack)
              work := childStart.work.add (sumForceCost n) } =
            [resumed] := by
        simp only [PrimeNeedReference.step, recursionSpec]
        rw [afterDemand_sum_value]
        rfl
      have hStep5 :
          PrimeNeedReference.step recursionSpec resumed = [produced] := by
        simp [resumed, produced, PrimeNeedReference.step, recursionSpec,
          action, PrimeNeedReference.finished]
      have hStep6 :
          PrimeNeedReference.step recursionSpec produced = [finished] := by
        simp [produced, finished, finalWorld, PrimeNeedReference.step,
          hParentFinal, evaluatingRecord, owner,
          PrimeNeedReference.recorded, World.record, ReceiptGraph.append,
          PrimeNeedReference.finished, childStart, sumForceCost, Work.add,
          Work.bump]
        omega
      have hPrefix :
          UniqueSteps recursionSpec 3 start childStart := by
        exact UniqueSteps.trans recursionSpec (singletonUniqueSteps hStep1)
          (UniqueSteps.trans recursionSpec (singletonUniqueSteps hStep2)
            (singletonUniqueSteps hStep3))
      have hSuffix :
          UniqueSteps recursionSpec 3
            { world := childFinalWorld
              control :=
                .returned (.value n)
                  (.resume .sumReturned :: .commit cell owner :: stack)
              work := childStart.work.add (sumForceCost n) }
            finished := by
        exact UniqueSteps.trans recursionSpec (singletonUniqueSteps hStep4)
          (UniqueSteps.trans recursionSpec (singletonUniqueSteps hStep5)
            (singletonUniqueSteps hStep6))
      have hExecution :
          UniqueSteps recursionSpec (6 * (n + 1) + 3) start finished := by
        have combined :=
          UniqueSteps.trans recursionSpec hPrefix
            (UniqueSteps.trans recursionSpec hChildSteps hSuffix)
        have hLength :
            3 + (6 * n + 3 + 3) = 6 * (n + 1) + 3 := by
          omega
        rw [hLength] at combined
        exact combined
      have hFinalBounded : HeapBounded finalWorld := by
        apply HeapBounded.recorded
        exact
          HeapBounded.setKnownCache hChildBounded hParentFinal (.value (n + 1))
      refine ⟨finalWorld, ?_, hFinalBounded, ?_, ?_, ?_, ?_⟩
      · simpa [start, finished] using hExecution
      · change
          (childFinalWorld.heap.setKnownCache cell evaluatingRecord
              (.value (n + 1))).lookup cell =
            some { origin := .sum (n + 1), cache := Cache.value (n + 1) }
        simp [evaluatingRecord]
      · intro other otherRecord hOther hOtherLookup
        have hOtherBound := (entry.bounded other otherRecord hOtherLookup).2
        have hOtherNeChild : other ≠ child := by
          intro hEqual
          have hSlots := congrArg CellId.slot hEqual
          rw [hChildSlot] at hSlots
          omega
        have hOtherEvaluating :
            evaluatingWorld.heap.lookup other = some otherRecord := by
          simp [evaluatingWorld, base, record,
            PrimeNeedReference.recorded, World.record, ReceiptGraph.append,
            World.setKnownCache, Heap.setKnownCache, Heap.lookup, hOther]
          exact hOtherLookup
        have hOtherAllocated :
            childWorld.heap.lookup other = some otherRecord := by
          rw [World.allocate?_preserves_other hAllocate hOtherNeChild]
          exact hOtherEvaluating
        have hOtherChildFinal :
            childFinalWorld.heap.lookup other = some otherRecord :=
          hChildPreserves other otherRecord hOtherNeChild hOtherAllocated
        change
          (childFinalWorld.heap.setKnownCache cell evaluatingRecord
              (.value (n + 1))).lookup other =
            some otherRecord
        rw [Heap.setKnownCache_preserves_other _ _ _ hOther]
        exact hOtherChildFinal
      · change childFinalWorld.nextCell = world.nextCell + (n + 1)
        rw [hChildNext, World.allocate?_nextCell hAllocate]
        change world.nextCell + 1 + n = world.nextCell + (n + 1)
        omega
      · change childFinalWorld.lineage = world.lineage
        rw [hChildLineage, World.allocate?_lineage hAllocate]
        rfl

/-- The closed initial machine reaches one halted answer with the exact
machine-free work vector. -/
theorem sum_initial_unique (n : Nat) :
    ∃ finalWorld,
      UniqueSteps recursionSpec (6 * n + 4)
        (initialMachine (.sum n))
        { world := finalWorld
          control := .halted (.value n)
          work := sumCost n } ∧
      HeapBounded finalWorld ∧
      finalWorld.heap.lookup (rootCell 1) =
        some { origin := .sum n, cache := Cache.value n } := by
  obtain
      ⟨returnWorld, hMacro, hBounded, hCached, _, _, _⟩ :=
    sum_macro n (initialWorld (.sum n) 1) (rootCell 1) [] {}
      (initial_entry (.sum n) 1)
  let returned : RecMachine :=
    { world := returnWorld
      control := .returned (.value n) []
      work := sumForceCost n }
  let halted : RecMachine :=
    { world := returnWorld
      control := .halted (.value n)
      work := sumCost n }
  have hMacro' :
      UniqueSteps recursionSpec (6 * n + 3)
        (initialMachine (.sum n)) returned := by
    simpa [initialMachine, returned] using hMacro
  have hAdd :
      (sumForceCost n).add (Work.operation 0 0 0 0) = sumCost n := by
    simpa [haltCost] using (sumCost_eq_force_add_halt n).symm
  have hHalt :
      PrimeNeedReference.step recursionSpec returned = [halted] := by
    simp [returned, halted, PrimeNeedReference.step,
      PrimeNeedReference.finished, hAdd]
  have hExecution :
      UniqueSteps recursionSpec (6 * n + 4)
        (initialMachine (.sum n)) halted := by
    have combined :=
      UniqueSteps.trans recursionSpec hMacro'
        (singletonUniqueSteps hHalt)
    have hLength : 6 * n + 3 + 1 = 6 * n + 4 := by omega
    rw [hLength] at combined
    exact combined
  exact ⟨returnWorld, hExecution, hBounded, hCached⟩

/-- Exact semantic frontier after the closed-form number of steps. -/
theorem runFrontier_sum_exact (n : Nat) :
    ∃ finalWorld,
      PrimeNeedReference.runFrontier recursionSpec (6 * n + 4)
          [initialMachine (.sum n)] =
        [{ world := finalWorld
           control := .halted (.value n)
           work := sumCost n }] := by
  obtain ⟨finalWorld, execution, _, _⟩ := sum_initial_unique n
  exact
    ⟨finalWorld,
      UniqueSteps.runFrontier_eq recursionSpec execution⟩

/-- The executable completed-work observer is welded to the closed form for
every recursion depth, not merely checked at concrete examples. -/
theorem completedWork_sum_exact (n : Nat) :
    completedWork (6 * n + 4) (.sum n) = [sumCost n] := by
  obtain ⟨finalWorld, hRun⟩ := runFrontier_sum_exact n
  simp [completedWork, hRun]

theorem runAnswers_sum_exact (n : Nat) :
    runAnswers (6 * n + 4) (.sum n) = [.value n] := by
  obtain ⟨finalWorld, hRun⟩ := runFrontier_sum_exact n
  simp [runAnswers, PrimeNeedReference.answers, hRun,
    PrimeNeedReference.haltedOutcome]

/-- The independently defined receipt-erased execution machine inherits the
same exact halted frontier and work vector by the proved erasure refinement. -/
theorem core_runFrontier_sum_exact (n : Nat) :
    ∃ finalWorld,
      PrimeNeedExecution.runFrontier recursionSpec (6 * n + 4)
          [PrimeNeedExecution.eraseMachine (initialMachine (.sum n))] =
        [PrimeNeedExecution.eraseMachine
          ({ world := finalWorld
             control := .halted (.value n)
             work := sumCost n } : RecMachine)] := by
  obtain ⟨finalWorld, hRich⟩ := runFrontier_sum_exact n
  have hCommutes :=
    PrimeNeedExecution.runFrontier_commutes recursionSpec (6 * n + 4)
      [initialMachine (.sum n)]
  rw [hRich] at hCommutes
  exact ⟨finalWorld, hCommutes.symm⟩

theorem core_answers_sum_exact (n : Nat) :
    PrimeNeedExecution.answers recursionSpec (6 * n + 4)
        (PrimeNeedExecution.eraseMachine (initialMachine (.sum n))) =
      [.value n] := by
  rw [PrimeNeedExecution.answers_commute]
  exact runAnswers_sum_exact n

end Mettapedia.Languages.MeTTa.PrimeRecursionCost
