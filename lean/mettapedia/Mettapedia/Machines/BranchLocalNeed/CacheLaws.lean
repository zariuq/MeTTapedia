import Mettapedia.Machines.BranchLocalNeed.ReferenceSemantics
import Mettapedia.Machines.RevisionDependencySet

/-!
# reference Need cell lifecycle laws

This module proves the obligation layer that the canary file
`PrimeCandidates.DemandObligations.lean` explicitly defers: the heap-machine
properties of reference's call-by-need evaluation.  The host machine is
`NeedReference` (its `step`/`Steps`/`runFrontier` are unchanged here);
this file adds no new machine, only laws about the existing one.

The central artifact is `HeapCellStep`: for every small-step successor
`next ∈ step spec machine`, every cell descends through exactly one of a
small number of transitions.  All headline laws are corollaries of that
single case analysis:

* **Forced once** (`steps_preserve_completed`,
  `forced_once_consistent_observations`): `value` and `stableFault` caches
  have no non-identity out-transition, so a completed cell is observed,
  never re-executed, anywhere it is forced later in the same lineage.
* **Black-hole honesty** (`force_evaluating_step`,
  `force_evaluating_no_answer`, `commit_retryable_restores_suspended`):
  forcing an in-progress cell
  yields a retryable black-hole receipt, never a value; retryable
  outcomes reset the cache to `suspended` on commit, so a black-hole is
  never masqueraded as a cached answer.
* **Call-time choice** (`forced_once_consistent_observations`,
  `resample_fresh_generation`): within one lineage every observation of a
  completed cell returns the same outcome; a genuinely fresh demand is
  only possible through `resample`, which allocates a provably distinct
  next-generation cell.
* **Production attribution** (`production_not_repeated_on_path`): an owner-matched
  commit and a cached delivery are classified from their actual source instruction.
  The original transition supplies the receipt and heap effects; one authentic
  path cannot produce a completed cell again. Sibling paths remain separate.
* **Sibling isolation** (`sibling_fresh_distinct`): a cell freshly
  allocated in one sibling fork carries that sibling's birth path and is
  provably distinct from the other sibling's fresh cells.

## Non-claims

* These are theorems about the **reference machine**, not about compiled
  C transitions; the C-side link is the separately documented refinement
  gap.
* `Work` accounting is inherited unchanged; nothing here is a cost
  model beyond what the reference machine already counts.
-/

namespace Mettapedia.Machines.BranchLocalNeed.NeedCacheLaws

open NeedReference

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect :
  Type*}

/-- A completed cache holds a terminated outcome: a value or a stable
fault.  These are exactly the cell states the native runtime memoizes. -/
inductive Cache.Completed : Cache Value StableFault → Prop where
  | value (v : Value) : Cache.Completed (.value v)
  | stableFault (f : StableFault) : Cache.Completed (.stableFault f)

/-- **The cell lifecycle.**  For one small step and any cell, the cell's
record changes in at most one of these five ways (and otherwise keeps its
record bit-for-bit):

* `untouched` — the record is unchanged;
* `allocate` — a previously absent cell appears, `suspended`;
* `beginEval` — a `suspended` cell becomes `evaluating` under an owner;
* `commit` / `commitFault` — an `evaluating` cell completes to a `value`
  or a `stableFault`;
* `reset` — an `evaluating` cell falls back to `suspended` after a
  retryable outcome.

Reading the constructors amounts to reading the machine's write
discipline.  There is deliberately **no** transition out of `value` or
`stableFault` (the raw material of the forced-once law), none *into*
`suspended` except from `evaluating` (a retry is the only way back), and
none that rewrites an origin (a cell keeps the term it was born with). -/
inductive HeapCellStep :
    Option (CellRecord Origin Value StableFault) →
    Option (CellRecord Origin Value StableFault) → Prop where
  | untouched (rec : Option (CellRecord Origin Value StableFault)) :
      HeapCellStep rec rec
  | allocate (origin : Origin) :
      HeapCellStep none (some ⟨origin, .suspended⟩)
  | beginEval (origin : Origin) (owner : EvaluatorId) :
      HeapCellStep
        (some ⟨origin, .suspended⟩) (some ⟨origin, .evaluating owner⟩)
  | commit (origin : Origin) (owner : EvaluatorId) (v : Value) :
      HeapCellStep
        (some ⟨origin, .evaluating owner⟩) (some ⟨origin, .value v⟩)
  | commitFault (origin : Origin) (owner : EvaluatorId)
      (f : StableFault) :
      HeapCellStep
        (some ⟨origin, .evaluating owner⟩) (some ⟨origin, .stableFault f⟩)
  | reset (origin : Origin) (owner : EvaluatorId) :
      HeapCellStep
        (some ⟨origin, .evaluating owner⟩) (some ⟨origin, .suspended⟩)

/-- A completed record is an endpoint of the lifecycle: the only step
available from it is `untouched`. -/
theorem HeapCellStep.completed_untouched
    {before after : Option (CellRecord Origin Value StableFault)}
    {record : CellRecord Origin Value StableFault}
    (hStep : HeapCellStep before after)
    (hBefore : before = some record)
    (hCompleted : Cache.Completed record.cache) :
    after = some record := by
  cases hStep with
  | untouched rec => exact hBefore
  | allocate origin => simp at hBefore
  | beginEval origin owner =>
      exfalso
      rw [Option.some.injEq] at hBefore
      rw [← hBefore] at hCompleted
      cases hCompleted
  | commit origin owner v =>
      exfalso
      rw [Option.some.injEq] at hBefore
      rw [← hBefore] at hCompleted
      cases hCompleted
  | commitFault origin owner f =>
      exfalso
      rw [Option.some.injEq] at hBefore
      rw [← hBefore] at hCompleted
      cases hCompleted
  | reset origin owner =>
      exfalso
      rw [Option.some.injEq] at hBefore
      rw [← hBefore] at hCompleted
      cases hCompleted

/-! ## Envionment discipline of the step constructors -/

/-- Recording a receipt changes neither heap nor path. -/
@[simp] theorem recorded_heap
    (world :
      World Origin Rule Value StableFault RetryableFault Effect)
    (payload :
      ReceiptPayload Origin Rule Value StableFault RetryableFault
        Effect) :
    (recorded world payload).heap = world.heap :=
  rfl

/-- Recording a receipt changes neither heap nor path. -/
@[simp] theorem recorded_path
    (world :
      World Origin Rule Value StableFault RetryableFault Effect)
    (payload :
      ReceiptPayload Origin Rule Value StableFault RetryableFault
        Effect) :
    (recorded world payload).path = world.path :=
  rfl

/-- A retry wraps the retry receipt around whatever world it is given;
the heap it carries is exactly that world's heap. -/
@[simp] theorem retryMachine_world_eq
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (reason : RetryReason RetryableFault)
    (stack : List (Frame Resume))
    (lookups updates receipts allocations : Nat) :
    (retryMachine machine world cell reason stack
          lookups updates receipts allocations).world =
      recorded world (.retry cell reason) := by
  simp [retryMachine, finished]

/-- The control returned by a retry step is the wrapped retryable fault
annotated with its reason. -/
@[simp] theorem retryMachine_control
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (reason : RetryReason RetryableFault)
    (stack : List (Frame Resume))
    (lookups updates receipts allocations : Nat) :
    (retryMachine machine world cell reason stack
          lookups updates receipts allocations).control =
      .returned (.retryableFault reason) stack := by
  simp [retryMachine, finished]

/-! ## Branch-offspring characterisation -/

section BranchAlternatives

variable
  {machine :
    Machine Origin Local Resume Rule Value StableFault RetryableFault
      Effect}
  {base : World Origin Rule Value StableFault RetryableFault Effect}
  {cell : CellId} {record : CellRecord Origin Value StableFault}
  {owner : EvaluatorId} {stack : List (Frame Resume)}
  {start : Nat} {alternatives : List (Rule × Local)}
  {candidate :
    Machine Origin Local Resume Rule Value StableFault RetryableFault
      Effect}

/-- Every `branchAlternatives` candidate marks the forced cell as
`evaluating` under the branch owner: that cell's new record is exactly
the old record with the cache flipped, nothing else. -/
theorem branchAlternatives_lookup_cell
    (hCandidate :
      candidate ∈
        branchAlternatives machine base cell record owner stack start
          alternatives) :
    candidate.world.heap.lookup cell =
      some { record with cache := Cache.evaluating owner } := by
  induction alternatives generalizing start candidate with
  | nil => simp [branchAlternatives] at hCandidate
  | cons head tail ih =>
      simp only [branchAlternatives, List.mem_cons] at hCandidate
      rcases hCandidate with hHead | hTail
      · subst hHead
        simp [finished, recorded, World.record, World.setKnownCache,
          World.fork]
      · exact ih hTail

/-- Branch candidates never move any cell other than the forced one:
their heap at `other` is the base world's heap. -/
theorem branchAlternatives_lookup_other
    (hCandidate :
      candidate ∈
        branchAlternatives machine base cell record owner stack start
          alternatives)
    {other : CellId} (hOther : other ≠ cell) :
    candidate.world.heap.lookup other = base.heap.lookup other := by
  induction alternatives generalizing start candidate with
  | nil => simp [branchAlternatives] at hCandidate
  | cons head tail ih =>
      simp only [branchAlternatives, List.mem_cons] at hCandidate
      rcases hCandidate with hHead | hTail
      · subst hHead
        simp_all [finished, recorded, World.record,
          World.setKnownCache, World.fork,
          Heap.setKnownCache_preserves_other]
      · exact ih hTail

/-- Branch candidates fork the base world by some branch index; their
world path extends the base path by exactly that one index. -/
theorem branchAlternatives_path
    (hCandidate :
      candidate ∈
        branchAlternatives machine base cell record owner stack start
          alternatives) :
    ∃ index : Nat, candidate.world.path = base.path ++ [index] := by
  induction alternatives generalizing start candidate with
  | nil => simp [branchAlternatives] at hCandidate
  | cons head tail ih =>
      simp only [branchAlternatives, List.mem_cons] at hCandidate
      rcases hCandidate with hHead | hTail
      · subst hHead
        exact
          ⟨start, by
            simp [finished, recorded, World.record,
              World.setKnownCache, World.fork]⟩
      · exact ih hTail

end BranchAlternatives

/-! ## The lifecycle of one step -/

/-- A cell whose heap is unchanged moves only by `untouched`. -/
theorem cellMove_of_heap_eq
    {machine next :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect}
    (hEq : next.world.heap = machine.world.heap) (cell : CellId) :
    HeapCellStep (machine.world.heap.lookup cell)
      (next.world.heap.lookup
        cell) := by
  rw [hEq]
  exact .untouched _

/-- Successful allocation certifies the fresh slot was empty: allocation
is fail-closed, so a success can only be read off an empty current
entry. -/
theorem allocate_fresh_absent
    {world next : World Origin Rule Value StableFault RetryableFault
      Effect}
    {origin : Origin} {generation : Nat} {cell : CellId}
    (h : world.allocate? origin generation = some (next, cell)) :
    world.heap.lookup cell = none := by
  have hFresh : cell = world.freshCell generation :=
    World.allocate?_fresh_cell h
  subst hFresh
  cases hAlloc :
    world.heap.allocate? (world.freshCell generation) origin with
  | none => simp [World.allocate?, hAlloc] at h
  | some _ =>
      cases hL : world.heap.lookup (world.freshCell generation) with
      | none => rfl
      | some record => simp [Heap.allocate?, hL] at hAlloc

/-- `finished` returns the world it was given. -/
@[simp] theorem finished_world
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (control : Control Local Resume Value StableFault RetryableFault)
    (lookups updates receipts allocations : Nat) :
    (finished machine world control
        lookups updates receipts allocations).world =
      world :=
  rfl

/-- `finished` returns the control it was given. -/
@[simp] theorem finished_control
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (control : Control Local Resume Value StableFault RetryableFault)
    (lookups updates receipts allocations : Nat) :
    (finished machine world control
        lookups updates receipts allocations).control =
      control :=
  rfl

/-- A world-level cache update leaves the path untouched. -/
@[simp] theorem World.setKnownCache_path
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (state : Cache Value StableFault) :
    (world.setKnownCache cell record state).path = world.path :=
  rfl

/-- A world-level cache update is a heap-level cache update, and nothing
else. -/
@[simp] theorem World.setKnownCache_heap
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (state : Cache Value StableFault) :
    (world.setKnownCache cell record state).heap =
      world.heap.setKnownCache cell record state :=
  rfl

/-- **Lifecycle of one step.**  Every cell of the heap descends through
`HeapCellStep` when the machine takes one small step.  This is the only
place the machine's write cases are enumerated; every law in this module
is a corollary. -/
theorem step_cellMove
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (machine next :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (hNext : next ∈ step spec machine) (cell : CellId) :
    HeapCellStep (machine.world.heap.lookup cell)
      (next.world.heap.lookup cell) := by
  rcases machine with ⟨world, control, work⟩
  cases control with
  | halted outcome =>
      simp [step] at hNext
  | force forcedCell stack =>
      cases hL : world.heap.lookup forcedCell with
      | none =>
          simp only [step, hL, List.mem_singleton] at hNext
          subst next
          exact cellMove_of_heap_eq (by simp) cell
      | some record =>
          obtain ⟨o, c⟩ := record
          cases c with
          | suspended =>
              cases hAlts : spec.alternatives o with
              | nil =>
                  simp only [step, hL, hAlts, List.mem_singleton] at hNext
                  subst next
                  exact cellMove_of_heap_eq (by simp) cell
              | cons head tail =>
                  simp only [step, hL, hAlts] at hNext
                  by_cases hSame : cell = forcedCell
                  · subst cell
                    rw [hL, branchAlternatives_lookup_cell hNext]
                    exact .beginEval o world.nextEvaluator
                  · rw [branchAlternatives_lookup_other hNext hSame]
                    exact .untouched _
          | evaluating owner =>
              simp only [step, hL, List.mem_singleton] at hNext
              subst next
              exact cellMove_of_heap_eq (by simp) cell
          | value value =>
              simp only [step, hL, List.mem_singleton] at hNext
              subst next
              exact cellMove_of_heap_eq (by simp) cell
          | stableFault fault =>
              simp only [step, hL, List.mem_singleton] at hNext
              subst next
              exact cellMove_of_heap_eq (by simp) cell
  | run state stack =>
      cases hAction : spec.action state with
      | done outcome =>
          simp only [step, hAction, List.mem_singleton] at hNext
          subst next
          exact cellMove_of_heap_eq (by simp) cell
      | demand forcedCell resume =>
          simp only [step, hAction, List.mem_singleton] at hNext
          subst next
          exact cellMove_of_heap_eq (by simp) cell
      | allocate origin resume =>
          cases hAlloc : world.allocate? origin with
          | none =>
              simp only [step, hAction, hAlloc, List.mem_singleton] at hNext
              subst next
              exact cellMove_of_heap_eq (by simp) cell
          | some worldFresh =>
              obtain ⟨worldNext, fresh⟩ := worldFresh
              simp only [step, hAction, hAlloc, List.mem_singleton] at hNext
              subst next
              by_cases hSame : cell = fresh
              · subst fresh
                rw [allocate_fresh_absent hAlloc]
                show
                  HeapCellStep none (worldNext.heap.lookup cell)
                rw [World.allocate?_lookup_same hAlloc]
                exact .allocate origin
              · show
                  HeapCellStep (world.heap.lookup cell)
                    (worldNext.heap.lookup cell)
                rw [World.allocate?_preserves_other hAlloc hSame]
                exact .untouched _
      | resample source resume =>
          cases hSource : world.heap.lookup source with
          | none =>
              simp only [step, hAction, hSource, List.mem_singleton] at hNext
              subst next
              exact cellMove_of_heap_eq (by simp) cell
          | some sourceRecord =>
              cases hAlloc :
                  world.allocate? sourceRecord.origin
                    (source.generation + 1) with
              | none =>
                  simp only [step, hAction, hSource, hAlloc,
                    List.mem_singleton] at hNext
                  subst next
                  exact cellMove_of_heap_eq (by simp) cell
              | some worldFresh =>
                  obtain ⟨worldNext, fresh⟩ := worldFresh
                  simp only [step, hAction, hSource, hAlloc,
                    List.mem_singleton] at hNext
                  subst next
                  by_cases hSame : cell = fresh
                  · subst fresh
                    rw [allocate_fresh_absent hAlloc]
                    show
                      HeapCellStep none (worldNext.heap.lookup cell)
                    rw [World.allocate?_lookup_same hAlloc]
                    exact .allocate sourceRecord.origin
                  · show
                      HeapCellStep (world.heap.lookup cell)
                        (worldNext.heap.lookup cell)
                    rw [World.allocate?_preserves_other hAlloc hSame]
                    exact .untouched _
      | perform effect nextLocal =>
          simp only [step, hAction, List.mem_singleton] at hNext
          subst next
          exact cellMove_of_heap_eq (by simp [recorded_heap]) cell
  | returned outcome stack =>
      cases stack with
      | nil =>
          simp only [step, List.mem_singleton] at hNext
          subst next
          exact cellMove_of_heap_eq (by simp) cell
      | cons frame rest =>
          cases frame with
          | resume token =>
              simp only [step, List.mem_singleton] at hNext
              subst next
              exact cellMove_of_heap_eq (by simp) cell
          | commit commitCell owner =>
              cases hL : world.heap.lookup commitCell with
              | none =>
                  simp only [step, hL, List.mem_singleton] at hNext
                  subst next
                  exact
                    cellMove_of_heap_eq (by simp) cell
              | some record =>
                  obtain ⟨o, c⟩ := record
                  cases c with
                  | evaluating actual =>
                      by_cases hOwner : actual = owner
                      · cases outcome with
                        | value v =>
                            simp only [step, hL, dif_pos hOwner,
                              List.mem_singleton] at hNext
                            subst next
                            by_cases hSame : cell = commitCell
                            · subst cell
                              rw [hL]
                              show HeapCellStep _
                                ((world.heap.setKnownCache commitCell
                                    ⟨o, .evaluating actual⟩
                                    (.value v)).lookup
                                  commitCell)
                              rw [Heap.setKnownCache_lookup_same]
                              exact .commit o actual v
                            · show HeapCellStep _
                                ((world.heap.setKnownCache commitCell
                                    ⟨o, .evaluating actual⟩
                                    (.value v)).lookup
                                  cell)
                              rw
                                [Heap.setKnownCache_preserves_other
                                  _ _ _ hSame]
                              exact .untouched _
                        | stableFault f =>
                            simp only [step, hL, dif_pos hOwner,
                              List.mem_singleton] at hNext
                            subst next
                            by_cases hSame : cell = commitCell
                            · subst cell
                              rw [hL]
                              show HeapCellStep _
                                ((world.heap.setKnownCache commitCell
                                    ⟨o, .evaluating actual⟩
                                    (.stableFault f)).lookup
                                  commitCell)
                              rw [Heap.setKnownCache_lookup_same]
                              exact .commitFault o actual f
                            · show HeapCellStep _
                                ((world.heap.setKnownCache commitCell
                                    ⟨o, .evaluating actual⟩
                                    (.stableFault f)).lookup
                                  cell)
                              rw
                                [Heap.setKnownCache_preserves_other
                                  _ _ _ hSame]
                              exact .untouched _
                        | retryableFault reason =>
                            simp only [step, hL, dif_pos hOwner,
                              List.mem_singleton] at hNext
                            subst next
                            by_cases hSame : cell = commitCell
                            · subst cell
                              rw [hL]
                              show HeapCellStep _
                                ((world.heap.setKnownCache commitCell
                                    ⟨o, .evaluating actual⟩
                                    .suspended).lookup
                                  commitCell)
                              rw [Heap.setKnownCache_lookup_same]
                              exact .reset o actual
                            · show HeapCellStep _
                                ((world.heap.setKnownCache commitCell
                                    ⟨o, .evaluating actual⟩
                                    .suspended).lookup
                                  cell)
                              rw
                                [Heap.setKnownCache_preserves_other
                                  _ _ _ hSame]
                              exact .untouched _
                      · simp only [step, hL, dif_neg hOwner,
                          List.mem_singleton] at hNext
                        subst next
                        exact
                          cellMove_of_heap_eq (by simp) cell
                  | _ =>
                      simp only [step, hL, List.mem_singleton] at hNext
                      subst next
                      exact
                        cellMove_of_heap_eq (by simp) cell

/-! ## The four laws -/

/-- **Forced once, one step.**  A completed record survives a small step
unchanged — the machine never rewrites a value or a stable fault. -/
theorem step_preserves_completed
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (machine next :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (hNext : next ∈ step spec machine)
    {cell : CellId} {record : CellRecord Origin Value StableFault}
    (hLookup : machine.world.heap.lookup cell = some record)
    (hCompleted : Cache.Completed record.cache) :
    next.world.heap.lookup cell = some record := by
  have hMove := step_cellMove spec machine next hNext cell
  exact hMove.completed_untouched hLookup hCompleted

/-- **Forced once.**  Along any execution path, a completed cell is
observed with the same record forever after: finished work is never
re-run and never overwritten. -/
theorem steps_preserve_completed
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    {length : Nat} {initial final :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect}
    (execution : Steps spec length initial final)
    {cell : CellId} {record : CellRecord Origin Value StableFault}
    (hLookup : initial.world.heap.lookup cell = some record)
    (hCompleted : Cache.Completed record.cache) :
    final.world.heap.lookup cell = some record := by
  induction execution with
  | refl => exact hLookup
  | cons hNext _ ih =>
      exact
        ih
          (step_preserves_completed spec _ _ (hNext.mem spec) hLookup
            hCompleted)

/-- **Forced once, observation form.**  Two observation outcomes read off
a completed cell anywhere along an execution agree — there is no
re-sampling of completed work inside a lineage. -/
theorem forced_once_consistent_observations
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    {length : Nat} {initial final :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect}
    (execution : Steps spec length initial final)
    {cell : CellId} {record₁ record₂ :
      CellRecord Origin Value StableFault}
    (hInitial : initial.world.heap.lookup cell = some record₁)
    (hCompleted : Cache.Completed record₁.cache)
    (hFinal : final.world.heap.lookup cell = some record₂) :
    record₂ = record₁ := by
  have hSurvives :=
    steps_preserve_completed spec execution hInitial hCompleted
  rw [hSurvives] at hFinal
  injection hFinal with hEq
  exact hEq.symm

/-- **Origin permanence, one step.**  A machine step never rewrites a
cell's origin: records that exist before and after the step share their
origin.  (Born-with-origin is enforced by allocation; this says it is
never mutated.) -/
theorem step_preserves_origin
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (machine next :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (hNext : next ∈ step spec machine)
    {cell : CellId} {recordBefore recordAfter :
      CellRecord Origin Value StableFault}
    (hBefore : machine.world.heap.lookup cell = some recordBefore)
    (hAfter : next.world.heap.lookup cell = some recordAfter) :
    recordAfter.origin = recordBefore.origin := by
  have hMove := step_cellMove spec machine next hNext cell
  rw [hBefore, hAfter] at hMove
  cases hMove with
  | untouched rec => rfl
  | beginEval o owner => rfl
  | commit o owner v => rfl
  | commitFault o owner f => rfl
  | reset o owner => rfl

/-- **Black-hole honesty, step shape.**  Forcing a cell that is already
being evaluated has exactly one successor and it is the retry wrapped
with the `blackhole` reason — the heap is untouched. -/
theorem force_evaluating_step
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    {cell : CellId} {stack : List (Frame Resume)}
    {origin : Origin} {owner : EvaluatorId}
    (hControl : machine.control = .force cell stack)
    (hLookup :
      machine.world.heap.lookup cell =
        some ⟨origin, Cache.evaluating owner⟩) :
    step spec machine =
      [retryMachine machine machine.world cell (.blackhole cell) stack
        1 0 0 0] := by
  simp [step, hControl, hLookup]

/-- **Black-hole honesty.**  Forcing a cell already under evaluation
returns a `blackhole` retry, never an answer: the successor control is
`.returned (.retryableFault (.blackhole cell)) _` and the heap lookup of
the forced cell is unchanged (no poisoning of the cache). -/
theorem force_evaluating_no_answer
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (machine next :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (hNext : next ∈ step spec machine)
    {cell : CellId} {stack : List (Frame Resume)}
    {origin : Origin} {owner : EvaluatorId}
    (hControl : machine.control = .force cell stack)
    (hLookup :
      machine.world.heap.lookup cell =
        some ⟨origin, Cache.evaluating owner⟩) :
    next.control = .returned (.retryableFault (.blackhole cell)) stack ∧
      next.world.heap.lookup cell = some ⟨origin, .evaluating owner⟩ := by
  rw [force_evaluating_step spec machine hControl hLookup] at hNext
  rw [List.mem_singleton] at hNext
  subst hNext
  refine ⟨by simp, ?_⟩
  change machine.world.heap.lookup cell = _
  exact hLookup

/-- **Retry restores the cache.**  Committing a retryable outcome returns
the cell to `suspended`: black-holes and other retryable failures are
never cached as if they were resolved answers. -/
theorem commit_retryable_restores_suspended
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    {cell : CellId} {owner : EvaluatorId}
    {reason : RetryReason RetryableFault} {rest : List (Frame Resume)}
    {origin : Origin}
    (hControl : machine.control =
      .returned (.retryableFault reason) (.commit cell owner :: rest))
    (hLookup :
      machine.world.heap.lookup cell =
        some ⟨origin, Cache.evaluating owner⟩) :
    step spec machine =
      [retryMachine machine
        (machine.world.setKnownCache cell ⟨origin, .evaluating owner⟩
          .suspended)
        cell reason rest 1 1 0 0] := by
  simp [step, hControl, hLookup]

/-- The cell that absorbs a retryable commit lands in `suspended` — the
heap-level content of `commit_retryable_restores_suspended`. -/
theorem commit_retryable_cache_suspended
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (machine next :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (hNext : next ∈ step spec machine)
    {cell : CellId} {owner : EvaluatorId}
    {reason : RetryReason RetryableFault} {rest : List (Frame Resume)}
    {origin : Origin}
    (hControl : machine.control =
      .returned (.retryableFault reason) (.commit cell owner :: rest))
    (hLookup :
      machine.world.heap.lookup cell =
        some ⟨origin, Cache.evaluating owner⟩) :
    next.world.heap.lookup cell = some ⟨origin, Cache.suspended⟩ := by
  rw [commit_retryable_restores_suspended spec machine hControl hLookup]
    at hNext
  rw [List.mem_singleton] at hNext
  subst next
  simp [World.setKnownCache, Heap.setKnownCache,
    Heap.lookup]

/-- **Call-time choice is about allocation identity.**  A resample
allocates the next-generation fresh cell; it is never the cell it was
sampled from, because generations advance. -/
theorem resample_fresh_generation
    {world next : World Origin Rule Value StableFault RetryableFault
      Effect}
    {origin : Origin} {generation : Nat} {cell : CellId}
    (h : world.allocate? origin (generation + 1) = some (next, cell)) :
    cell.generation = generation + 1 :=
  World.allocate?_fresh_generation h

/-- **Sibling allocation pins.**  Cells freshly allocated in distinct
sibling forks have different births, hence are different cells: forcing a
cell in one sibling can never accidentally resolve the sibling's
freshly-allocated cell. -/
theorem sibling_fresh_distinct
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    {left right : Nat} (h : left ≠ right) (generation : Nat) :
    (world.fork left).freshCell generation ≠
      (world.fork right).freshCell generation :=
  World.freshCell_sibling_ne world h generation

/-! ## Call-time choice: completed demand is deterministic -/

/-- **Cached observation, step shape.**  Forcing a cell whose cache
already holds a value has exactly one successor: the observation receipt
and the value returned to the current stack.  No branching, no second
evaluation. -/
theorem force_cached_value_step
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    {cell : CellId} {stack : List (Frame Resume)}
    {origin : Origin} {v : Value}
    (hControl : machine.control = .force cell stack)
    (hLookup :
      machine.world.heap.lookup cell = some ⟨origin, Cache.value v⟩) :
    step spec machine =
      [finished machine
        (recorded machine.world (.observe cell (.value v)))
        (.returned (.value v) stack) 1 0 1 0] := by
  simp [step, hControl, hLookup]

/-- **Shared demand is deterministic.**  Within one lineage, a cell that
already completed as `v` is forced to the same `v` on every later
demand: the second reader cannot re-sample.  This is the machine-level
statement of call-time choice: the choice was made at first force, and
sharing is by cell identity, not by repeated evaluation. -/
theorem forced_once_deterministic_observation
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    {length : Nat} {initial final :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect}
    (execution : Steps spec length initial final)
    {cell : CellId} {origin : Origin} {v : Value}
    (hComplete : initial.world.heap.lookup cell = some ⟨origin, .value v⟩)
    {stack : List (Frame Resume)}
    (hForce : final.control = .force cell stack) :
    step spec final =
      [finished final
        (recorded final.world (.observe cell (.value v)))
        (.returned (.value v) stack) 1 0 1 0] := by
  have hFinal : final.world.heap.lookup cell = some ⟨origin, .value v⟩ :=
    steps_preserve_completed spec execution hComplete (.value v)
  exact force_cached_value_step spec final hForce hFinal

/-! ## Path monotonicity and lineage births -/

/-- Allocating a fresh cell leaves the world's path untouched. -/
theorem World.allocate?_path
    {world next : World Origin Rule Value StableFault RetryableFault
      Effect}
    {origin : Origin} {generation : Nat} {cell : CellId}
    (h : world.allocate? origin generation = some (next, cell)) :
    next.path = world.path := by
  let candidate := world.freshCell generation
  change
    (match world.heap.allocate? candidate origin with
      | none => none
      | some heap =>
          let advanced :=
            { world with heap := heap, nextCell := world.nextCell + 1 }
          let recorded := advanced.record (.allocate candidate origin)
          some (recorded.1, candidate)) =
      some (next, cell) at h
  split at h
  · contradiction
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    simp [World.record]

/-- A path extends along a step: worlds only grow downward through
forks. -/
def PathExtends (shorter longer : WorldPath) : Prop :=
  ∃ suffix, longer = shorter ++ suffix

theorem PathExtends.refl (p : WorldPath) : PathExtends p p :=
  ⟨[], by simp⟩

theorem PathExtends.trans {a b c : WorldPath} (hab : PathExtends a b)
    (hbc : PathExtends b c) : PathExtends a c := by
  obtain ⟨s1, h1⟩ := hab
  obtain ⟨s2, h2⟩ := hbc
  exact ⟨s1 ++ s2, by rw [h2, h1, List.append_assoc]⟩

/-- **Paths only extend.**  A small step either keeps the world path or
forks one level down. -/
theorem step_path_extends
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (machine next :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (hNext : next ∈ step spec machine) :
    PathExtends machine.world.path next.world.path := by
  rcases machine with ⟨world, control, work⟩
  cases control with
  | halted outcome => simp [step] at hNext
  | force forcedCell stack =>
      cases hL : world.heap.lookup forcedCell with
      | none =>
          simp only [step, hL, List.mem_singleton] at hNext
          subst next
          exact ⟨[], by simp [retryMachine]⟩
      | some record =>
          obtain ⟨o, c⟩ := record
          cases c with
          | suspended =>
              cases hAlts : spec.alternatives o with
              | nil =>
                  simp only [step, hL, hAlts, List.mem_singleton] at hNext
                  subst next
                  exact ⟨[], by simp⟩
              | cons head tail =>
                  simp only [step, hL, hAlts] at hNext
                  obtain ⟨index, hPath⟩ := branchAlternatives_path hNext
                  exact ⟨[index], by simpa using hPath⟩
          | evaluating owner =>
              simp only [step, hL, List.mem_singleton] at hNext
              subst next
              exact ⟨[], by simp⟩
          | value value =>
              simp only [step, hL, List.mem_singleton] at hNext
              subst next
              exact ⟨[], by simp⟩
          | stableFault fault =>
              simp only [step, hL, List.mem_singleton] at hNext
              subst next
              exact ⟨[], by simp⟩
  | run state stack =>
      cases hAction : spec.action state with
      | done outcome =>
          simp only [step, hAction, List.mem_singleton] at hNext
          subst next
          exact ⟨[], by simp⟩
      | demand forcedCell resume =>
          simp only [step, hAction, List.mem_singleton] at hNext
          subst next
          exact ⟨[], by simp⟩
      | allocate origin resume =>
          cases hAlloc : world.allocate? origin with
          | none =>
              simp only [step, hAction, hAlloc, List.mem_singleton] at hNext
              subst next
              exact ⟨[], by simp⟩
          | some worldFresh =>
              obtain ⟨worldNext, fresh⟩ := worldFresh
              simp only [step, hAction, hAlloc, List.mem_singleton] at hNext
              subst next
              refine ⟨[], ?_⟩
              show worldNext.path = world.path ++ []
              rw [World.allocate?_path hAlloc]
              simp
      | resample source resume =>
          cases hSource : world.heap.lookup source with
          | none =>
              simp only [step, hAction, hSource, List.mem_singleton] at hNext
              subst next
              exact ⟨[], by simp⟩
          | some sourceRecord =>
              cases hAlloc :
                  world.allocate? sourceRecord.origin
                    (source.generation + 1) with
              | none =>
                  simp only [step, hAction, hSource, hAlloc,
                    List.mem_singleton] at hNext
                  subst next
                  exact ⟨[], by simp⟩
              | some worldFresh =>
                  obtain ⟨worldNext, fresh⟩ := worldFresh
                  simp only [step, hAction, hSource, hAlloc,
                    List.mem_singleton] at hNext
                  subst next
                  refine ⟨[], ?_⟩
                  show worldNext.path = world.path ++ []
                  rw [World.allocate?_path hAlloc]
                  simp
      | perform effect nextLocal =>
          simp only [step, hAction, List.mem_singleton] at hNext
          subst next
          exact ⟨[], by simp⟩
  | returned outcome stack =>
      cases stack with
      | nil =>
          simp only [step, List.mem_singleton] at hNext
          subst next
          exact ⟨[], by simp⟩
      | cons frame rest =>
          cases frame with
          | resume token =>
              simp only [step, List.mem_singleton] at hNext
              subst next
              exact ⟨[], by simp⟩
          | commit commitCell owner =>
              cases hL : world.heap.lookup commitCell with
              | none =>
                  simp only [step, hL, List.mem_singleton] at hNext
                  subst next
                  exact ⟨[], by simp⟩
              | some record =>
                  obtain ⟨o, c⟩ := record
                  cases c with
                  | evaluating actual =>
                      by_cases hOwner : actual = owner
                      · cases outcome with
                        | value v =>
                            simp only [step, hL, dif_pos hOwner,
                              List.mem_singleton] at hNext
                            subst next
                            exact ⟨[], by simp⟩
                        | stableFault f =>
                            simp only [step, hL, dif_pos hOwner,
                              List.mem_singleton] at hNext
                            subst next
                            exact ⟨[], by simp⟩
                        | retryableFault reason =>
                            simp only [step, hL, dif_pos hOwner,
                              List.mem_singleton] at hNext
                            subst next
                            exact ⟨[], by simp⟩
                      · simp only [step, hL, dif_neg hOwner,
                          List.mem_singleton] at hNext
                        subst next
                        exact ⟨[], by simp⟩
                  | _ =>
                      simp only [step, hL, List.mem_singleton] at hNext
                      subst next
                      exact ⟨[], by simp⟩

/-- **Paths only extend, transitively.** -/
theorem steps_path_extends
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    {length : Nat} {initial final :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect}
    (execution : Steps spec length initial final) :
    PathExtends initial.world.path final.world.path := by
  induction execution with
  | refl => exact PathExtends.refl _
  | cons hNext _ ih =>
      exact
        (step_path_extends spec _ _ (hNext.mem spec)).trans ih

/-- **New cells are born at the allocating machine's location.**  A cell
machine's current world path. -/
theorem step_new_cell_birth
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (machine next :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (hNext : next ∈ step spec machine)
    {cell : CellId}
    (hAbsent : machine.world.heap.lookup cell = none)
    (hPresent : (next.world.heap.lookup cell).isSome) :
    cell.birth = machine.world.path := by
  rcases machine with ⟨world, control, work⟩
  cases control with
  | halted outcome => simp [step] at hNext
  | force forcedCell stack =>
      cases hL : world.heap.lookup forcedCell with
      | none =>
          simp only [step, hL, List.mem_singleton] at hNext
          subst next
          simp [hAbsent] at hPresent
      | some record =>
          obtain ⟨o, c⟩ := record
          cases c with
          | suspended =>
              cases hAlts : spec.alternatives o with
              | nil =>
                  simp only [step, hL, hAlts, List.mem_singleton] at hNext
                  subst next
                  simp [hAbsent] at hPresent
              | cons head tail =>
                  simp only [step, hL, hAlts] at hNext
                  by_cases hSame : cell = forcedCell
                  · subst cell
                    simp [hL] at hAbsent
                  · rw [branchAlternatives_lookup_other hNext hSame]
                      at hPresent
                    rw [hAbsent] at hPresent
                    simp at hPresent
          | evaluating owner =>
              simp only [step, hL, List.mem_singleton] at hNext
              subst next
              simp [hAbsent] at hPresent
          | value value =>
              simp only [step, hL, List.mem_singleton] at hNext
              subst next
              simp [hAbsent] at hPresent
          | stableFault fault =>
              simp only [step, hL, List.mem_singleton] at hNext
              subst next
              simp [hAbsent] at hPresent
  | run state stack =>
      cases hAction : spec.action state with
      | done outcome =>
          simp only [step, hAction, List.mem_singleton] at hNext
          subst next
          simp [hAbsent] at hPresent
      | demand forcedCell resume =>
          simp only [step, hAction, List.mem_singleton] at hNext
          subst next
          simp [hAbsent] at hPresent
      | allocate origin resume =>
          cases hAlloc : world.allocate? origin with
          | none =>
              simp only [step, hAction, hAlloc, List.mem_singleton] at hNext
              subst next
              simp [hAbsent] at hPresent
          | some worldFresh =>
              obtain ⟨worldNext, fresh⟩ := worldFresh
              simp only [step, hAction, hAlloc, List.mem_singleton] at hNext
              subst next
              by_cases hSame : cell = fresh
              · subst fresh
                have hFresh := World.allocate?_fresh_cell hAlloc
                rw [hFresh]
                rfl
              · simp only [finished_world] at hPresent
                rw
                  [World.allocate?_preserves_other hAlloc hSame] at hPresent
                rw [hAbsent] at hPresent
                simp at hPresent
      | resample source resume =>
          cases hSource : world.heap.lookup source with
          | none =>
              simp only [step, hAction, hSource, List.mem_singleton] at hNext
              subst next
              simp [hAbsent] at hPresent
          | some sourceRecord =>
              cases hAlloc :
                  world.allocate? sourceRecord.origin
                    (source.generation + 1) with
              | none =>
                  simp only [step, hAction, hSource, hAlloc,
                    List.mem_singleton] at hNext
                  subst next
                  simp [hAbsent] at hPresent
              | some worldFresh =>
                  obtain ⟨worldNext, fresh⟩ := worldFresh
                  simp only [step, hAction, hSource, hAlloc,
                    List.mem_singleton] at hNext
                  subst next
                  by_cases hSame : cell = fresh
                  · subst fresh
                    have hFresh := World.allocate?_fresh_cell hAlloc
                    rw [hFresh]
                    rfl
                  · simp only [finished_world, recorded_heap] at hPresent
                    rw [World.allocate?_preserves_other hAlloc hSame]
                      at hPresent
                    rw [hAbsent] at hPresent
                    simp at hPresent
      | perform effect nextLocal =>
          simp only [step, hAction, List.mem_singleton] at hNext
          subst next
          simp [hAbsent] at hPresent
  | returned outcome stack =>
      cases stack with
      | nil =>
          simp only [step, List.mem_singleton] at hNext
          subst next
          simp [hAbsent] at hPresent
      | cons frame rest =>
          cases frame with
          | resume token =>
              simp only [step, List.mem_singleton] at hNext
              subst next
              simp [hAbsent] at hPresent
          | commit commitCell owner =>
              cases hL : world.heap.lookup commitCell with
              | none =>
                  simp only [step, hL, List.mem_singleton] at hNext
                  subst next
                  simp [hAbsent] at hPresent
              | some record =>
                  obtain ⟨o, c⟩ := record
                  cases c with
                  | evaluating actual =>
                      by_cases hOwner : actual = owner
                      · cases outcome with
                        | value v =>
                            simp only [step, hL, dif_pos hOwner,
                              List.mem_singleton] at hNext
                            subst next
                            by_cases hSame : cell = commitCell
                            · subst cell
                              rw [hL] at hAbsent
                              simp at hAbsent
                            · simp only [finished_world, recorded_heap,
                                World.setKnownCache_heap] at hPresent
                              rw [Heap.setKnownCache_preserves_other _ _ _
                                  hSame] at hPresent
                              rw [hAbsent] at hPresent
                              simp at hPresent
                        | stableFault f =>
                            simp only [step, hL, dif_pos hOwner,
                              List.mem_singleton] at hNext
                            subst next
                            by_cases hSame : cell = commitCell
                            · subst cell
                              rw [hL] at hAbsent
                              simp at hAbsent
                            · simp only [finished_world, recorded_heap,
                                World.setKnownCache_heap] at hPresent
                              rw [Heap.setKnownCache_preserves_other _ _ _
                                  hSame] at hPresent
                              rw [hAbsent] at hPresent
                              simp at hPresent
                        | retryableFault reason =>
                            simp only [step, hL, dif_pos hOwner,
                              List.mem_singleton] at hNext
                            subst next
                            by_cases hSame : cell = commitCell
                            · subst cell
                              rw [hL] at hAbsent
                              simp at hAbsent
                            · simp only [retryMachine_world_eq,
                                recorded_heap,
                                World.setKnownCache_heap] at hPresent
                              rw [Heap.setKnownCache_preserves_other _ _ _
                                  hSame] at hPresent
                              rw [hAbsent] at hPresent
                              simp at hPresent
                      · simp only [step, hL, dif_neg hOwner,
                          List.mem_singleton] at hNext
                        subst next
                        simp [hAbsent] at hPresent
                  | suspended =>
                      simp only [step, hL, List.mem_singleton] at hNext
                      subst next
                      simp [hAbsent] at hPresent
                  | value value =>
                      simp only [step, hL, List.mem_singleton] at hNext
                      subst next
                      simp [hAbsent] at hPresent
                  | stableFault fault =>
                      simp only [step, hL, List.mem_singleton] at hNext
                      subst next
                      simp [hAbsent] at hPresent

/-- **Lineage births stay below the lineage.**  Every fresh cell's birth
is at or below the starting machine's path. -/
theorem steps_new_cells_extend_path
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    {length : Nat} {initial final :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect}
    (execution : Steps spec length initial final)
    {cell : CellId}
    (hAbsent : initial.world.heap.lookup cell = none)
    (hPresent : (final.world.heap.lookup cell).isSome) :
    ∃ suffix, cell.birth = initial.world.path ++ suffix := by
  induction execution with
  | refl =>
      rw [hAbsent] at hPresent
      simp at hPresent
  | @cons _ machine next final hNext _ ih =>
      cases hNextLookup : next.world.heap.lookup cell with
      | none =>
          obtain ⟨suffix, hBirth⟩ := ih hNextLookup hPresent
          obtain ⟨s1, hExt⟩ := step_path_extends spec _ _
            (hNext.mem spec)
          exact ⟨s1 ++ suffix, by rw [hBirth, hExt, List.append_assoc]⟩
      | some rec =>
          refine ⟨[], ?_⟩
          rw [List.append_nil]
          exact
            step_new_cell_birth spec machine next (hNext.mem spec) hAbsent
              (by simp [hNextLookup])

/-- **Sibling isolation.**  A cell born strictly inside the left sibling
can never appear in a heap of the right sibling's lineage: its birth
would have to extend two incomparable prefixes at once. -/
theorem sibling_lineage_absent
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    {length : Nat} {initial final :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect}
    (execution : Steps spec length initial final)
    {p : WorldPath} {left right : Nat} (hBranch : left ≠ right)
    (hPath : initial.world.path = p ++ [right])
    {cell : CellId}
    (hBirth : ∃ s, cell.birth = p ++ [left] ++ s)
    (hFresh : initial.world.heap.lookup cell = none) :
    final.world.heap.lookup cell = none := by
  cases hFinal : final.world.heap.lookup cell with
  | none => rfl
  | some rec =>
      exfalso
      have hExtend :=
        steps_new_cells_extend_path spec execution hFresh (by simp [hFinal])
      obtain ⟨s₂, hS₂⟩ := hExtend
      obtain ⟨s₁, hS₁⟩ := hBirth
      rw [hPath] at hS₂
      have hCross : p ++ [left] ++ s₁ = p ++ [right] ++ s₂ :=
        hS₁.symm.trans hS₂
      have hCross' : p ++ ([left] ++ s₁) = p ++ ([right] ++ s₂) := by
        simpa [List.append_assoc] using hCross
      have hHead : [left] ++ s₁ = [right] ++ s₂ :=
        List.append_cancel_left hCross'
      have hEq : left = right ∧ s₁ = s₂ := by simpa using hHead
      exact hBranch hEq.1

/-- Forked offspring share the base heap; a cell allocated strictly after
the fork point on one branch is absent from that base heap and therefore
from every alternate sibling lineage.  Corollary form of
`sibling_lineage_absent` for forked births. -/
theorem sibling_isolation
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    {length : Nat} {initial final :
      Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect}
    (execution : Steps spec length initial final)
    {p : WorldPath} {left right : Nat} (hBranch : left ≠ right)
    (hPath : initial.world.path = p ++ [right])
    {cell : CellId} {s : WorldPath}
    (hBirth : cell.birth = p ++ [left] ++ s)
    (hFresh : initial.world.heap.lookup cell = none) :
    final.world.heap.lookup cell = none :=
  sibling_lineage_absent spec execution hBranch hPath ⟨s, hBirth⟩ hFresh


/-! ## Independent cache deltas and retained history -/

/-- The actual cache writes instantiate the common finite-map commutation
law. This compares the resulting maps, without discarding either update
history or claiming a join of choice worlds. -/
theorem independent_cache_writes_commute_as_maps
    (heap : Heap Origin Value StableFault) (first second : CellId)
    (firstRecord secondRecord : CellRecord Origin Value StableFault)
    (firstState secondState : Cache Value StableFault) (different : first ≠ second) :
    ((heap.setKnownCache first firstRecord firstState).setKnownCache
        second secondRecord secondState).current =
      ((heap.setKnownCache second secondRecord secondState).setKnownCache
        first firstRecord firstState).current := by
  exact BindingPublication.applyWrites_commute heap.current
    [(first, { firstRecord with cache := firstState })]
    [(second, { secondRecord with cache := secondState })]
    (by simpa using different.symm)

/-- A captured cache read remains publishable exactly when it was before,
if both actual writes are outside its consulted cells. This establishes the
read component of a delta contract, not the ownership of either writer. -/
theorem independent_cache_writes_preserve_captured_reads
    {Origin Value StableFault : Type}
    [DecidableEq Origin] [DecidableEq Value] [DecidableEq StableFault]
    (view : CapturedReadView CellId (Option (CellRecord Origin Value StableFault)))
    (heap : Heap Origin Value StableFault) (first second : CellId)
    (firstRecord secondRecord : CellRecord Origin Value StableFault)
    (firstState secondState : Cache Value StableFault)
    (outside : List.Disjoint view.consulted [first, second]) :
    view.CanPublish
        ⟨((heap.setKnownCache first firstRecord firstState).setKnownCache
          second secondRecord secondState).current⟩ ↔
      view.CanPublish ⟨heap.current⟩ := by
  exact CapturedReadView.canPublish_applyWrites_iff view ⟨heap.current⟩
    [(first, { firstRecord with cache := firstState }),
      (second, { secondRecord with cache := secondState })]
    (by simpa using outside)

/-- Independent maps do not make retained snapshots identical. Both
histories remain distinct, so an ancestry-only merge cannot use map equality
as proof of snapshot authority. -/
theorem independent_cache_writes_have_different_spines
    (heap : Heap Origin Value StableFault) (first second : CellId)
    (firstRecord secondRecord : CellRecord Origin Value StableFault)
    (firstState secondState : Cache Value StableFault) (different : first ≠ second) :
    ((heap.setKnownCache first firstRecord firstState).setKnownCache
        second secondRecord secondState).spine ≠
      ((heap.setKnownCache second secondRecord secondState).setKnownCache
        first firstRecord firstState).spine := by
  intro same
  have heads := (List.cons.inj same).1
  have cells : second = first := (HeapUpdate.cache.inj heads).1
  exact different cells.symm

/-! ## Production and delivery attribution -/

/-- Completing a cache and reading an already completed cache have different
roles even when their existing receipt payloads agree. -/
inductive CompletedReceiptKind where
  | production
  | delivery
deriving DecidableEq, Repr

structure CompletedReceipt (Value StableFault RetryableFault : Type*) where
  kind : CompletedReceiptKind
  cell : CellId
  id : ReceiptId
  outcome : Produced Value StableFault RetryableFault
deriving DecidableEq, Repr

def completedReceipt
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (kind : CompletedReceiptKind) (cell : CellId)
    (outcome : Produced Value StableFault RetryableFault) :
    CompletedReceipt Value StableFault RetryableFault :=
  ⟨kind, cell, ⟨machine.world.path, machine.world.receipts.nextSerial⟩, outcome⟩

/-- Classify the existing source instruction. The cache owner is checked
before attributing a production; retryable outcomes never produce a cache. -/
def completedReceipt?
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Option (CompletedReceipt Value StableFault RetryableFault) :=
  match machine.control with
  | .force cell _ =>
      match machine.world.heap.lookup cell with
      | some record =>
          match record.cache with
          | .value value => some (completedReceipt machine .delivery cell (.value value))
          | .stableFault fault =>
              some (completedReceipt machine .delivery cell (.stableFault fault))
          | _ => none
      | none => none
  | .returned outcome (.commit cell owner :: _) =>
      match machine.world.heap.lookup cell with
      | some record =>
          match record.cache with
          | .evaluating actual =>
              if actual = owner then
                match outcome with
                | .value value => some (completedReceipt machine .production cell (.value value))
                | .stableFault fault =>
                    some (completedReceipt machine .production cell (.stableFault fault))
                | .retryableFault _ => none
              else none
          | _ => none
      | none => none
  | _ => none

/-- Independent lifecycle evidence for the four completed-cache events.
It refers to the source control and heap, rather than the classifier. -/
inductive CompletedReceiptWitness
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    CompletedReceipt Value StableFault RetryableFault → Prop where
  | deliveryValue (cell : CellId) (stack : List (Frame Resume)) (origin : Origin) (value : Value)
      (control : machine.control = .force cell stack)
      (cached : machine.world.heap.lookup cell = some ⟨origin, .value value⟩) :
      CompletedReceiptWitness machine (completedReceipt machine .delivery cell (.value value))
  | deliveryFault (cell : CellId) (stack : List (Frame Resume))
      (origin : Origin) (fault : StableFault)
      (control : machine.control = .force cell stack)
      (cached : machine.world.heap.lookup cell = some ⟨origin, .stableFault fault⟩) :
      CompletedReceiptWitness machine (completedReceipt machine .delivery cell (.stableFault fault))
  | productionValue (cell : CellId) (owner : EvaluatorId) (rest : List (Frame Resume))
      (origin : Origin) (value : Value)
      (control : machine.control = .returned (.value value) (.commit cell owner :: rest))
      (owned : machine.world.heap.lookup cell = some ⟨origin, .evaluating owner⟩) :
      CompletedReceiptWitness machine (completedReceipt machine .production cell (.value value))
  | productionFault (cell : CellId) (owner : EvaluatorId) (rest : List (Frame Resume))
      (origin : Origin) (fault : StableFault)
      (control : machine.control = .returned (.stableFault fault) (.commit cell owner :: rest))
      (owned : machine.world.heap.lookup cell = some ⟨origin, .evaluating owner⟩) :
      CompletedReceiptWitness machine (completedReceipt machine .production cell (.stableFault fault))

theorem CompletedReceiptWitness.classified
    {machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {receipt : CompletedReceipt Value StableFault RetryableFault}
    (witness : CompletedReceiptWitness machine receipt) :
    completedReceipt? machine = some receipt := by
  cases witness <;> simp_all [completedReceipt?]

theorem completedReceipt?_witness
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (receipt : CompletedReceipt Value StableFault RetryableFault)
    (classified : completedReceipt? machine = some receipt) :
    CompletedReceiptWitness machine receipt := by
  rcases machine with ⟨world, control, work⟩
  cases control with
  | halted outcome => simp [completedReceipt?] at classified
  | run state stack => simp [completedReceipt?] at classified
  | force cell stack =>
      cases found : world.heap.lookup cell with
      | none => simp [completedReceipt?, found] at classified
      | some record =>
          rcases record with ⟨origin, cache⟩
          cases cache with
          | suspended => simp [completedReceipt?, found] at classified
          | evaluating owner => simp [completedReceipt?, found] at classified
          | value value =>
              simp only [completedReceipt?, found, Option.some.injEq] at classified
              subst receipt
              exact .deliveryValue cell stack origin value rfl found
          | stableFault fault =>
              simp only [completedReceipt?, found, Option.some.injEq] at classified
              subst receipt
              exact .deliveryFault cell stack origin fault rfl found
  | returned outcome stack =>
      cases stack with
      | nil => simp [completedReceipt?] at classified
      | cons frame rest =>
          cases frame with
          | resume token => simp [completedReceipt?] at classified
          | commit cell owner =>
              cases found : world.heap.lookup cell with
              | none => simp [completedReceipt?, found] at classified
              | some record =>
                  rcases record with ⟨origin, cache⟩
                  cases cache with
                  | suspended => simp [completedReceipt?, found] at classified
                  | value value => simp [completedReceipt?, found] at classified
                  | stableFault fault => simp [completedReceipt?, found] at classified
                  | evaluating actual =>
                      by_cases same : actual = owner
                      · subst actual
                        cases outcome with
                        | retryableFault reason => simp [completedReceipt?, found] at classified
                        | value value =>
                            simp [completedReceipt?, found] at classified
                            subst receipt
                            exact .productionValue cell owner rest origin value rfl found
                        | stableFault fault =>
                            simp [completedReceipt?, found] at classified
                            subst receipt
                            exact .productionFault cell owner rest origin fault rfl found
                      · simp [completedReceipt?, found, same] at classified

theorem completedReceipt?_iff
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (receipt : CompletedReceipt Value StableFault RetryableFault) :
    completedReceipt? machine = some receipt ↔ CompletedReceiptWitness machine receipt :=
  ⟨completedReceipt?_witness machine receipt, CompletedReceiptWitness.classified⟩

/-- Each classified event is an actual append by the unchanged reference
transition. Its fresh position and all previous nodes are retained. -/
theorem CompletedReceiptWitness.step_receipt
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {machine next : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {receipt : CompletedReceipt Value StableFault RetryableFault}
    (witness : CompletedReceiptWitness machine receipt) (successor : next ∈ step spec machine) :
    next.world.receipts.nodes =
      ⟨receipt.id, machine.world.receipts.roots, .observe receipt.cell receipt.outcome⟩ ::
        machine.world.receipts.nodes ∧
      next.world.receipts.roots = [receipt.id] ∧
      next.world.receipts.nextSerial = machine.world.receipts.nextSerial + 1 := by
  cases witness <;>
    simp_all [step, finished, recorded, World.record, World.setKnownCache,
      ReceiptGraph.append, completedReceipt]

theorem completedReceipt?_step_receipt
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {machine next : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {receipt : CompletedReceipt Value StableFault RetryableFault}
    (classified : completedReceipt? machine = some receipt) (successor : next ∈ step spec machine) :
    next.world.receipts.nodes =
      ⟨receipt.id, machine.world.receipts.roots, .observe receipt.cell receipt.outcome⟩ ::
        machine.world.receipts.nodes ∧
      next.world.receipts.roots = [receipt.id] ∧
      next.world.receipts.nextSerial = machine.world.receipts.nextSerial + 1 :=
  (completedReceipt?_witness machine receipt classified).step_receipt spec successor

/-- Cache reads retain the complete heap, rather than constructing another
production with the same answer. -/
theorem CompletedReceiptWitness.delivery_heap
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {machine next : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {receipt : CompletedReceipt Value StableFault RetryableFault}
    (witness : CompletedReceiptWitness machine receipt) (successor : next ∈ step spec machine)
    (delivery : receipt.kind = .delivery) : next.world.heap = machine.world.heap := by
  cases witness <;>
    simp_all [completedReceipt, step, finished, recorded, World.record, ReceiptGraph.append]

/-- A production is the actual owner-matched cache replacement. The source
record and all other cells are retained by the existing update primitive. -/
theorem CompletedReceiptWitness.production_heap
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {machine next : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {receipt : CompletedReceipt Value StableFault RetryableFault}
    (witness : CompletedReceiptWitness machine receipt) (successor : next ∈ step spec machine)
    (production : receipt.kind = .production) :
    ∃ (record : CellRecord Origin Value StableFault) (owner : EvaluatorId),
      machine.world.heap.lookup receipt.cell = some record ∧
      record.cache = .evaluating owner ∧
      next.world.heap = machine.world.heap.setKnownCache receipt.cell record
        (match receipt.outcome with
          | .value value => .value value
          | .stableFault fault => .stableFault fault
          | .retryableFault _ => .suspended) := by
  cases witness <;>
    simp_all [completedReceipt, step, finished, recorded, World.record, World.setKnownCache,
      ReceiptGraph.append]

theorem CompletedReceiptWitness.production_completes_cache
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {machine next : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {receipt : CompletedReceipt Value StableFault RetryableFault}
    (witness : CompletedReceiptWitness machine receipt) (successor : next ∈ step spec machine)
    (production : receipt.kind = .production) :
    ∃ record : CellRecord Origin Value StableFault,
      next.world.heap.lookup receipt.cell = some record ∧ Cache.Completed record.cache := by
  cases witness with
  | deliveryValue => simp [completedReceipt] at production
  | deliveryFault => simp [completedReceipt] at production
  | productionValue cell owner rest origin value control owned =>
      simp [step, control, owned] at successor
      subst next
      refine ⟨⟨origin, .value value⟩, ?_, .value value⟩
      simp [finished, recorded, World.record, World.setKnownCache, ReceiptGraph.append,
        completedReceipt]
  | productionFault cell owner rest origin fault control owned =>
      simp [step, control, owned] at successor
      subst next
      refine ⟨⟨origin, .stableFault fault⟩, ?_, .stableFault fault⟩
      simp [finished, recorded, World.record, World.setKnownCache, ReceiptGraph.append,
        completedReceipt]

theorem CompletedReceiptWitness.stable_outcome
    {machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {receipt : CompletedReceipt Value StableFault RetryableFault}
    (witness : CompletedReceiptWitness machine receipt) :
    (∃ value, receipt.outcome = .value value) ∨
      (∃ fault, receipt.outcome = .stableFault fault) := by
  cases witness <;> simp [completedReceipt]

/-- Structural graph validity supplies event freshness, not production
authentication. The lifecycle witness supplies that separate attribution. -/
theorem CompletedReceiptWitness.fresh
    {machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {receipt : CompletedReceipt Value StableFault RetryableFault}
    (witness : CompletedReceiptWitness machine receipt) (valid : machine.world.receipts.Valid) :
    receipt.id ∉ machine.world.receipts.toCausalReceipt.known [] := by
  cases witness <;>
    exact ReceiptGraph.fresh_receipt_id _ valid.1 _

/-- The classifier cannot label another production of a completed cell. -/
theorem completed_cache_forbids_production
    {machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {cell : CellId} {record : CellRecord Origin Value StableFault}
    (cached : machine.world.heap.lookup cell = some record) (completed : Cache.Completed record.cache)
    {receipt : CompletedReceipt Value StableFault RetryableFault}
    (classified : completedReceipt? machine = some receipt) (same : receipt.cell = cell) :
    receipt.kind ≠ .production := by
  have witness := completedReceipt?_witness machine receipt classified
  cases witness <;> simp only [completedReceipt] at same ⊢
  · simp
  · simp
  · subst cell
    rename_i owned
    rw [owned, Option.some.injEq] at cached
    subst record
    cases completed
  · subst cell
    rename_i owned
    rw [owned, Option.some.injEq] at cached
    subst record
    cases completed

/-- Forced-once preservation also preserves the production attribution
boundary through arbitrary authentic execution paths. -/
theorem steps_completed_cache_forbids_production
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {length : Nat}
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : Steps spec length initial final)
    {cell : CellId} {record : CellRecord Origin Value StableFault}
    (cached : initial.world.heap.lookup cell = some record) (completed : Cache.Completed record.cache)
    {receipt : CompletedReceipt Value StableFault RetryableFault}
    (classified : completedReceipt? final = some receipt) (same : receipt.cell = cell) :
    receipt.kind ≠ .production :=
  completed_cache_forbids_production
    (steps_preserve_completed spec execution cached completed) completed classified same

/-- A single authentic execution path cannot produce the same cell again
after a successful production. Sibling paths are separate hypotheses. -/
theorem production_not_repeated_on_path
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {machine next later : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {first second : CompletedReceipt Value StableFault RetryableFault}
    (produced : CompletedReceiptWitness machine first) (successor : next ∈ step spec machine)
    (production : first.kind = .production) {length : Nat}
    (execution : Steps spec length next later)
    (classified : completedReceipt? later = some second) (same : second.cell = first.cell) :
    second.kind ≠ .production := by
  obtain ⟨record, cached, completed⟩ := produced.production_completes_cache spec successor production
  exact steps_completed_cache_forbids_production spec execution cached completed classified same

namespace CompletedReceiptControls

private def cell : CellId := ⟨1, [], 0, 0⟩

private def world (cache : Cache Nat Unit) : World Unit Unit Nat Unit Unit Unit :=
  { lineage := 1
    path := []
    heap := {
      current := fun queried => if queried = cell then some ⟨(), cache⟩ else none
      spine := [.cache cell cache, .allocate cell ()] }
    receipts := ReceiptGraph.empty
    nextCell := 1
    nextEvaluator := 4 }

def spec : Spec Unit Nat Nat Unit Nat Unit Unit Unit where
  alternatives _ := []
  action state := if state < 2 then .demand cell (state + 1) else .done (.value 21)
  afterDemand token _ := token
  afterAllocation token _ := token

def start : Machine Unit Nat Nat Unit Nat Unit Unit Unit :=
  ⟨world (.evaluating 3), .returned (.value 21) [.commit cell 3, .resume 0], {}⟩

private def withControl (control : Control Nat Nat Nat Unit Unit) :
    Machine Unit Nat Nat Unit Nat Unit Unit Unit :=
  { start with control := control }

private def suspendedDemand : Machine Unit Nat Nat Unit Nat Unit Unit Unit :=
  { start with world := world .suspended, control := .force cell [] }

private def lateDelivery : Machine Unit Nat Nat Unit Nat Unit Unit Unit :=
  { start with world := world (.value 21), control := .force cell [] }

private def siblingProduction (branch : Nat) : Machine Unit Nat Nat Unit Nat Unit Unit Unit :=
  { start with world := start.world.fork branch }

private def receiptAt (fuel : Nat) : Option (CompletedReceipt Nat Unit Unit) :=
  ((runFrontier spec fuel [start])[0]?).bind completedReceipt?

/-- One actual commit followed by two actual cache demands. Equal values
remain three distinct events; the latter two are deliveries. -/
theorem one_production_two_deliveries :
    (receiptAt 0).map (fun receipt => (receipt.kind, receipt.id, receipt.outcome)) =
      some (.production, ⟨[], 0⟩, .value 21) ∧
    (receiptAt 3).map (fun receipt => (receipt.kind, receipt.id, receipt.outcome)) =
      some (.delivery, ⟨[], 1⟩, .value 21) ∧
    (receiptAt 6).map (fun receipt => (receipt.kind, receipt.id, receipt.outcome)) =
      some (.delivery, ⟨[], 2⟩, .value 21) := by decide

theorem duplicated_delivery_id_refused :
    (receiptAt 3).map CompletedReceipt.id ≠ (receiptAt 6).map CompletedReceipt.id := by decide

theorem wrong_owner_does_not_produce :
    completedReceipt? (withControl (.returned (.value 21) [.commit cell 4])) = none :=
  by decide

theorem retryable_outcome_does_not_produce :
    completedReceipt? (withControl
      (.returned (.retryableFault (.domain ())) [.commit cell 3])) = none := by decide

theorem stable_fault_is_production :
    (completedReceipt? (withControl (.returned (.stableFault ()) [.commit cell 3]))).map
      (fun receipt => (receipt.kind, receipt.outcome)) = some (.production, .stableFault ()) :=
  by decide

theorem evaluating_demand_is_not_delivery :
    completedReceipt? (withControl (.force cell [])) = none := by decide

theorem suspended_demand_is_not_delivery :
    completedReceipt? suspendedDemand = none :=
  by decide

/-- The same inherited cell can complete separately in two sibling worlds.
The forced-once law is path-local, not a global deduplication by cell name. -/
theorem sibling_productions_remain_distinct :
    (completedReceipt? (siblingProduction 0)).map CompletedReceipt.id = some ⟨[0], 0⟩ ∧
    (completedReceipt? (siblingProduction 1)).map CompletedReceipt.id = some ⟨[1], 0⟩ ∧
    (completedReceipt? (siblingProduction 0)).map CompletedReceipt.id ≠
      (completedReceipt? (siblingProduction 1)).map CompletedReceipt.id := by decide

/-- A late cached read is a delivery even when no production receipt was
captured in its initial graph. Its earlier producer is a boundary obligation. -/
theorem late_delivery_does_not_invent_production :
    lateDelivery.world.receipts.nodes = [] ∧
      (completedReceipt? lateDelivery).map CompletedReceipt.kind = some .delivery := by decide

/-- Existing payload graphs can collide between a commit and a late read.
The actual source transition, not payload equality, supplies the role. -/
theorem observed_payload_does_not_determine_role :
    (runFrontier spec 1 [start]).map (fun machine => machine.world.receipts) =
      (runFrontier spec 1 [lateDelivery]).map (fun machine => machine.world.receipts) ∧
    (completedReceipt? start).map CompletedReceipt.kind ≠
      (completedReceipt? lateDelivery).map CompletedReceipt.kind := by decide

end CompletedReceiptControls


/-! ## Axiom audits -/

#print axioms step_cellMove
#print axioms steps_preserve_completed
#print axioms forced_once_consistent_observations
#print axioms force_evaluating_step
#print axioms force_evaluating_no_answer
#print axioms commit_retryable_restores_suspended
#print axioms commit_retryable_cache_suspended
#print axioms forced_once_deterministic_observation
#print axioms step_path_extends
#print axioms steps_new_cells_extend_path
#print axioms sibling_lineage_absent

end Mettapedia.Machines.BranchLocalNeed.NeedCacheLaws
