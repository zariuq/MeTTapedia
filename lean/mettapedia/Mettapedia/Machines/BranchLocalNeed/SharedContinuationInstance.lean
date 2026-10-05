import Mettapedia.Machines.SharedContinuation
import Mettapedia.Machines.BranchLocalNeed.ExecutionMachine

/-!
# The branch-local need machine as a shared-continuation program

The receipt-erased need machine of `NeedExecution` is an instance of
`SharedContinuation.Program`; neither interface is changed.

* Return frames are the need machine's own frames: update frames
  `Frame.commit cell owner` and resume tokens `Frame.resume token`. A task's
  return list is the need control stack, verbatim.
* A task context is a branch-local world with its work account, so each rule
  alternative carries its own world.
* Rule alternatives are frontier tasks, in rule order and with multiplicity.
* `resume` returns through a frame: an update frame checks ownership and writes
  the cache (or resets it after a retryable fault); a resume token continues the
  demanding state with `Spec.afterDemand`.
* A demand is a call whose return frame is its resume token. Allocation,
  resampling, effects and completion are tail calls with one alternative.

## Encoding choices

* Work is carried in the context and bumped exactly as by `NeedExecution.step`.
  Publishing an answer cannot change the context, so the work of the halting
  transition (one transition, nothing else) is added back by `answerMachine`.
* `inspect` reads the control only, while whether a force pushes an update frame,
  and which owner the frame names, depend on the world. A force is therefore a
  tail call to `lookup`; for a suspended cell with rules its single alternative
  is a `claim` control carrying the record and the owner, in the unchanged
  context, and the claim then pushes the update frame and branches. That
  dispatch decodes to the same need state (`claim_step_silent`), so one need
  transition costs one or two shared steps (`cost`).
* Some such step is unavoidable when the control encoding ignores the world:
  one shared step has the same effect on the return list in every context
  (`step_returns_context_free`), while a need force pushes a frame in one world
  and none in another (`Demo.no_lockstep_force`).

## Results

* `step_exact`: after `cost` shared steps the pending tasks and the published
  answers are unchanged, and the newly published answers followed by the new
  tasks decode to exactly `NeedExecution.step` of the head task.
* `machines_step_exact`: the shared reference step is thus the depth-first
  schedule `expandFirst` of the need machine on decoded frontiers.
* `Completes.runFrontier`, `completes_of_runFrontier`: completed depth-first
  runs are exactly completed bounded breadth-first runs `NeedExecution.runFrontier`.
* `runFrontier_eq_of_program`, `program_of_runFrontier`, `answers_eq_of_program`,
  `program_of_answers`: completed shared runs and completed bounded need runs
  agree on the halted machines, with their worlds, outcomes, work, order and
  duplicates, and in particular on `NeedExecution.answers`.
* `arena_answers_eq_of_program`: the arena realization publishes the same
  answers, by the generic `SharedContinuation.decode_checkedStep`.
* `returnCohort_need_steps`: delivery to retained sites in one selected world
  agrees with the independent need step, with complete return stacks and
  duplicate sites. A successful owned commit preserves that world's cache;
  a mismatched owner returns a retryable fault.

## Not covered

* Unfinished runs are related only transition by transition: the shared run
  follows the depth-first schedule, `runFrontier` the breadth-first one.
* Receipts are erased; `NeedExecution.step_commutes` relates them.
* Native realization: constant-time arena access, retirement of need frames,
  physical producer/subscriber delivery and native code are separate obligations.
* `SharedContinuation.Program` is stated in `Type`, so the instance covers need
  machines whose parameters live in `Type`.
-/

/- Proof notes: `NeedReference` and `NeedExecution` export the same names
(`step`, `isHalted`, ...), so `NeedReference` is opened selectively. Nested
matches of the need step need `dsimp only` before the next `cases`, and its
private helpers are closed by `rfl`. -/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.NeedContinuation

open NeedReference (CellId CellRecord Control EvaluatorId Frame Produced RetryReason Spec Work)
open NeedExecution (CoreWorld CoreMachine)
open SharedContinuation (Instruction Program Task State)

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type}

/-! ## The program -/

/-- A task context: the branch-local world and its work account. -/
structure Context (Origin Rule Value StableFault RetryableFault Effect : Type) where
  world : CoreWorld Origin Rule Value StableFault RetryableFault Effect
  work : Work

/-- Need control without its stack; the stack is the task's return list.
`claim` is a `force` that has read a suspended cell with rules: it carries the
looked-up record and the owner that the update frame will name. -/
inductive Mode (Origin Local Value StableFault RetryableFault : Type) where
  | force (cell : CellId)
  | claim (cell : CellId) (owner : EvaluatorId)
      (record : CellRecord Origin Value StableFault)
  | run (state : Local)
  | returned (outcome : Produced Value StableFault RetryableFault)

/-- Callees. `lookup` reads a cell, `rules` branches over its rule
occurrences, `action` performs one local action. -/
inductive Call (Origin Local Value StableFault : Type) where
  | lookup (cell : CellId)
  | rules (cell : CellId) (owner : EvaluatorId)
      (record : CellRecord Origin Value StableFault)
  | action (state : Local)

abbrev NeedTask (Origin Local Resume Rule Value StableFault RetryableFault Effect : Type) :=
  Task (Context Origin Rule Value StableFault RetryableFault Effect)
    (Mode Origin Local Value StableFault RetryableFault) (Frame Resume)

abbrev NeedState (Origin Local Resume Rule Value StableFault RetryableFault Effect : Type) :=
  State (Context Origin Rule Value StableFault RetryableFault Effect)
    (Mode Origin Local Value StableFault RetryableFault) (Frame Resume)
    (Produced Value StableFault RetryableFault)

namespace Context

variable (context : Context Origin Rule Value StableFault RetryableFault Effect)

/-- The configuration reached by one accounted need transition. -/
def transit (world : CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (mode : Mode Origin Local Value StableFault RetryableFault)
    (lookups updates receipts allocations : Nat) :
    Context Origin Rule Value StableFault RetryableFault Effect ×
      Mode Origin Local Value StableFault RetryableFault :=
  (⟨world, context.work.bump lookups updates receipts allocations⟩, mode)

/-- A machine-owned retry, published as a retryable outcome. Its receipt append
is still counted, although the receipt node itself is erased. -/
def retry (world : CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (reason : RetryReason RetryableFault)
    (lookups updates priorReceipts allocations : Nat) :
    Context Origin Rule Value StableFault RetryableFault Effect ×
      Mode Origin Local Value StableFault RetryableFault :=
  context.transit world (.returned (.retryableFault reason))
    lookups updates (priorReceipts + 1) allocations

end Context

section Program

variable (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)

/-- Reading a cell. A cached outcome or a machine fault is returned at once;
a suspended cell with rules becomes a `claim`, leaving the context unchanged. -/
def lookupBranches (context : Context Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) :
    List (Context Origin Rule Value StableFault RetryableFault Effect ×
      Mode Origin Local Value StableFault RetryableFault) :=
  match context.world.heap.lookup cell with
  | none => [context.retry context.world (.outOfScope cell) 1 0 0 0]
  | some record =>
      match record.cache with
      | .value value =>
          [context.transit context.world (.returned (.value value)) 1 0 1 0]
      | .stableFault fault =>
          [context.transit context.world (.returned (.stableFault fault)) 1 0 1 0]
      | .evaluating _ => [context.retry context.world (.blackhole cell) 1 0 0 0]
      | .suspended =>
          match spec.alternatives record.origin with
          | [] =>
              [context.retry
                { context.world with nextEvaluator := context.world.nextEvaluator + 1 }
                (.noRule cell) 1 0 1 0]
          | _ :: _ => [(context, .claim cell context.world.nextEvaluator record)]

/-- One alternative per rule occurrence, in order, each in its own fork of the
world with the cell marked as evaluated by `owner`. -/
def ruleBranches (context : Context Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (owner : EvaluatorId) (record : CellRecord Origin Value StableFault) :
    Nat → List (Rule × Local) →
      List (Context Origin Rule Value StableFault RetryableFault Effect ×
        Mode Origin Local Value StableFault RetryableFault)
  | _, [] => []
  | index, (_, state) :: rest =>
      context.transit
          (CoreWorld.setKnownCache
            (CoreWorld.fork { context.world with nextEvaluator := owner + 1 } index)
            cell record (.evaluating owner))
          (.run state) 1 1 2 0 ::
        ruleBranches context cell owner record (index + 1) rest

/-- One local action. A demand only enters the forced cell here; its resume
token is the return frame pushed by `inspect`. -/
def actionBranches (context : Context Origin Rule Value StableFault RetryableFault Effect)
    (state : Local) :
    List (Context Origin Rule Value StableFault RetryableFault Effect ×
      Mode Origin Local Value StableFault RetryableFault) :=
  match spec.action state with
  | .done outcome => [context.transit context.world (.returned outcome) 0 0 0 0]
  | .demand cell _ => [context.transit context.world (.force cell) 0 0 0 0]
  | .allocate origin resume =>
      match context.world.allocate? origin with
      | none =>
          [context.retry context.world
            (.allocationCollision (context.world.freshCell 0)) 1 0 0 0]
      | some (world, cell) =>
          [context.transit world (.run (spec.afterAllocation resume cell)) 1 1 1 1]
  | .resample source resume =>
      match context.world.heap.lookup source with
      | none => [context.retry context.world (.outOfScope source) 1 0 0 0]
      | some sourceRecord =>
          match context.world.allocate? sourceRecord.origin (source.generation + 1) with
          | none =>
              [context.retry context.world
                (.allocationCollision (context.world.freshCell (source.generation + 1)))
                2 0 0 0]
          | some (world, fresh) =>
              [context.transit world (.run (spec.afterAllocation resume fresh)) 2 1 2 1]
  | .perform _ next => [context.transit context.world (.run next) 0 0 1 0]

/-- Returning through a frame. A resume token continues the demanding state;
an update frame checks ownership and writes the cache. -/
def resume (context : Context Origin Rule Value StableFault RetryableFault Effect) :
    Frame Resume → Produced Value StableFault RetryableFault →
      Context Origin Rule Value StableFault RetryableFault Effect ×
        Mode Origin Local Value StableFault RetryableFault
  | .resume token, outcome =>
      context.transit context.world (.run (spec.afterDemand token outcome)) 0 0 0 0
  | .commit cell owner, outcome =>
      match context.world.heap.lookup cell with
      | none => context.retry context.world (.outOfScope cell) 1 0 0 0
      | some record =>
          match record.cache with
          | .evaluating actual =>
              if actual = owner then
                match outcome with
                | .value value =>
                    context.transit (context.world.setKnownCache cell record (.value value))
                      (.returned (.value value)) 1 1 1 0
                | .stableFault fault =>
                    context.transit
                      (context.world.setKnownCache cell record (.stableFault fault))
                      (.returned (.stableFault fault)) 1 1 1 0
                | .retryableFault reason =>
                    context.retry (context.world.setKnownCache cell record .suspended)
                      reason 1 1 0 0
              else context.retry context.world (.ownershipLost cell owner actual) 1 0 0 0
          | _ => context.retry context.world (.ownershipLost cell owner 0) 1 0 0 0

/-- Dispatch reads the control only. -/
def inspect :
    Mode Origin Local Value StableFault RetryableFault →
      Instruction (Call Origin Local Value StableFault) (Frame Resume)
        (Produced Value StableFault RetryableFault)
  | .force cell => .tail (.lookup cell)
  | .claim cell owner record => .call (.rules cell owner record) (.commit cell owner)
  | .run state =>
      match spec.action state with
      | .demand _ token => .call (.action state) (.resume token)
      | _ => .tail (.action state)
  | .returned outcome => .ret outcome

def branches (context : Context Origin Rule Value StableFault RetryableFault Effect) :
    Call Origin Local Value StableFault →
      List (Context Origin Rule Value StableFault RetryableFault Effect ×
        Mode Origin Local Value StableFault RetryableFault)
  | .lookup cell => lookupBranches spec context cell
  | .rules cell owner record =>
      ruleBranches context cell owner record 0 (spec.alternatives record.origin)
  | .action state => actionBranches spec context state

/-- The receipt-erased need machine as a shared-continuation program. -/
def program :
    Program (Context Origin Rule Value StableFault RetryableFault Effect)
      (Mode Origin Local Value StableFault RetryableFault)
      (Call Origin Local Value StableFault) (Frame Resume)
      (Produced Value StableFault RetryableFault) where
  inspect := inspect spec
  branches := branches spec
  resume := resume spec

end Program

/-! ## Decoding -/

namespace Mode

/-- Reattach the return list as the need machine's control stack. A claim is
still the force it came from. -/
def attach : Mode Origin Local Value StableFault RetryableFault → List (Frame Resume) →
    Control Local Resume Value StableFault RetryableFault
  | .force cell, stack => .force cell stack
  | .claim cell _ _, stack => .force cell stack
  | .run state, stack => .run state stack
  | .returned outcome, stack => .returned outcome stack

def isClaim : Mode Origin Local Value StableFault RetryableFault → Bool
  | .claim .. => true
  | _ => false

end Mode

def taskMachine (task : NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect where
  world := task.context.world
  control := task.control.attach task.returns
  work := task.context.work

/-- A published answer is the halted machine; emission is the halting
transition, whose one-transition work increment is restored here. -/
def answerMachine
    (answer : Context Origin Rule Value StableFault RetryableFault Effect ×
      Produced Value StableFault RetryableFault) :
    CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect where
  world := answer.1.world
  control := .halted answer.2
  work := answer.1.work.bump 0 0 0 0

/-- The need frontier denoted by a shared state: published answers first, then
the pending tasks, in order. -/
def machines (state : NeedState Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect) :=
  state.emitted.map answerMachine ++ state.frontier.map taskMachine

/-! ## One need transition -/

section Simulation

variable (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)

/-- Shared steps spent on the need transition of a task: a force that claims a
suspended cell spends one extra dispatch, which leaves the context unchanged. -/
def cost (task : NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Nat :=
  match task.control with
  | .force cell =>
      match task.context.world.heap.lookup cell with
      | some record =>
          match record.cache with
          | .suspended => if (spec.alternatives record.origin).isEmpty then 1 else 2
          | _ => 1
      | none => 1
  | _ => 1

/-- Return list after a local action: a demand pushes its resume token. -/
def runReturns (state : Local) (stack : List (Frame Resume)) : List (Frame Resume) :=
  match spec.action state with
  | .demand _ token => .resume token :: stack
  | _ => stack

variable (context : Context Origin Rule Value StableFault RetryableFault Effect)
  (stack : List (Frame Resume))
  (rest : List (NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect))
  (emitted : List (Context Origin Rule Value StableFault RetryableFault Effect ×
    Produced Value StableFault RetryableFault))

theorem step_force (cell : CellId) :
    SharedContinuation.step (program spec)
        ⟨⟨context, .force cell, stack⟩ :: rest, emitted⟩ =
      ⟨(lookupBranches spec context cell).map (fun next => ⟨next.1, next.2, stack⟩) ++ rest,
        emitted⟩ := rfl

theorem step_claim (cell : CellId) (owner : EvaluatorId)
    (record : CellRecord Origin Value StableFault) :
    SharedContinuation.step (program spec)
        ⟨⟨context, .claim cell owner record, stack⟩ :: rest, emitted⟩ =
      ⟨(ruleBranches context cell owner record 0 (spec.alternatives record.origin)).map
          (fun next => ⟨next.1, next.2, .commit cell owner :: stack⟩) ++ rest, emitted⟩ := rfl

theorem step_run (state : Local) :
    SharedContinuation.step (program spec) ⟨⟨context, .run state, stack⟩ :: rest, emitted⟩ =
      ⟨(actionBranches spec context state).map
          (fun next => ⟨next.1, next.2, runReturns spec state stack⟩) ++ rest, emitted⟩ := by
  simp only [SharedContinuation.step, program, inspect, runReturns]
  cases spec.action state <;> rfl

theorem step_returned_nil (outcome : Produced Value StableFault RetryableFault) :
    SharedContinuation.step (program spec)
        ⟨⟨context, .returned outcome, []⟩ :: rest, emitted⟩ =
      ⟨rest, emitted ++ [(context, outcome)]⟩ := rfl

theorem step_returned_cons (outcome : Produced Value StableFault RetryableFault)
    (frame : Frame Resume) (pending : List (Frame Resume)) :
    SharedContinuation.step (program spec)
        ⟨⟨context, .returned outcome, frame :: pending⟩ :: rest, emitted⟩ =
      ⟨⟨(resume spec context frame outcome).1, (resume spec context frame outcome).2,
          pending⟩ :: rest, emitted⟩ := rfl

/-! Need-side equations. -/

theorem need_step_run (state : Local) :
    NeedExecution.step spec (taskMachine ⟨context, .run state, stack⟩) =
      (actionBranches spec context state).map
        (fun next => taskMachine ⟨next.1, next.2, runReturns spec state stack⟩) := by
  simp only [taskMachine, Mode.attach, NeedExecution.step, actionBranches, runReturns]
  cases spec.action state with
  | done outcome => rfl
  | demand cell token => rfl
  | allocate origin token =>
      dsimp only
      cases context.world.allocate? origin with
      | none => rfl
      | some result => rfl
  | resample source token =>
      dsimp only
      cases context.world.heap.lookup source with
      | none => rfl
      | some sourceRecord =>
          dsimp only
          cases context.world.allocate? sourceRecord.origin (source.generation + 1) with
          | none => rfl
          | some result => rfl
  | perform effect next => rfl

theorem need_step_returned_cons (outcome : Produced Value StableFault RetryableFault)
    (frame : Frame Resume) (pending : List (Frame Resume)) :
    NeedExecution.step spec (taskMachine ⟨context, .returned outcome, frame :: pending⟩) =
      [taskMachine ⟨(resume spec context frame outcome).1,
        (resume spec context frame outcome).2, pending⟩] := by
  cases frame with
  | resume token => rfl
  | commit cell owner =>
      simp only [taskMachine, Mode.attach, NeedExecution.step, resume]
      cases context.world.heap.lookup cell with
      | none => rfl
      | some record =>
          dsimp only
          cases record.cache with
          | evaluating actual =>
              dsimp only
              by_cases hOwner : actual = owner
              · cases outcome <;> simp [hOwner] <;> rfl
              · simp [hOwner]; rfl
          | suspended => rfl
          | value value => rfl
          | stableFault fault => rfl

/-- The rule alternatives, reattached under the update frame, are exactly the
need machine's ordered branch worlds. -/
theorem ruleBranches_map (cell : CellId) (owner : EvaluatorId)
    (record : CellRecord Origin Value StableFault) (index : Nat)
    (alternatives : List (Rule × Local)) :
    (ruleBranches context cell owner record index alternatives).map
        (fun next => taskMachine ⟨next.1, next.2, .commit cell owner :: stack⟩) =
      NeedExecution.branchAlternatives (taskMachine ⟨context, .force cell, stack⟩)
        { context.world with nextEvaluator := owner + 1 } cell record owner stack
        index alternatives := by
  induction alternatives generalizing index with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨rule, state⟩
      simp only [ruleBranches, NeedExecution.branchAlternatives, List.map_cons]
      exact congrArg₂ List.cons rfl (ih (index + 1))

theorem lookupBranches_claim (cell : CellId) (record : CellRecord Origin Value StableFault)
    (hLookup : context.world.heap.lookup cell = some record)
    (hCache : record.cache = .suspended) (hRules : spec.alternatives record.origin ≠ []) :
    lookupBranches spec context cell =
      [(context, .claim cell context.world.nextEvaluator record)] := by
  obtain ⟨head, tail, hAlternatives⟩ := List.exists_cons_of_ne_nil hRules
  simp only [lookupBranches, hLookup, hCache, hAlternatives]

theorem cost_force_eq_two (cell : CellId) (record : CellRecord Origin Value StableFault)
    (hLookup : context.world.heap.lookup cell = some record)
    (hCache : record.cache = .suspended) (hRules : spec.alternatives record.origin ≠ []) :
    cost spec ⟨context, .force cell, stack⟩ = 2 := by
  simp [cost, hLookup, hCache, hRules]

/-- Unless a force claims a cell, it costs one shared step. -/
theorem claim_of_cost_ne_one (cell : CellId)
    (hCost : cost spec ⟨context, .force cell, stack⟩ ≠ 1) :
    ∃ record, context.world.heap.lookup cell = some record ∧
      record.cache = .suspended ∧ spec.alternatives record.origin ≠ [] := by
  simp only [cost] at hCost
  cases hLookup : context.world.heap.lookup cell with
  | none => simp [hLookup] at hCost
  | some record =>
      refine ⟨record, rfl, ?_⟩
      simp only [hLookup] at hCost
      cases hCache : record.cache with
      | suspended =>
          refine ⟨rfl, ?_⟩
          intro hNil
          simp [hCache, hNil] at hCost
      | evaluating owner => simp [hCache] at hCost
      | value value => simp [hCache] at hCost
      | stableFault fault => simp [hCache] at hCost

theorem need_step_force (cell : CellId) (hCost : cost spec ⟨context, .force cell, stack⟩ = 1) :
    NeedExecution.step spec (taskMachine ⟨context, .force cell, stack⟩) =
      (lookupBranches spec context cell).map
        (fun next => taskMachine ⟨next.1, next.2, stack⟩) := by
  simp only [cost] at hCost
  simp only [taskMachine, Mode.attach, NeedExecution.step, lookupBranches]
  cases hLookup : context.world.heap.lookup cell with
  | none => rfl
  | some record =>
      simp only [hLookup] at hCost
      dsimp only
      cases hCache : record.cache with
      | suspended =>
          simp only [hCache] at hCost
          dsimp only
          cases hAlternatives : spec.alternatives record.origin with
          | nil => rfl
          | cons head tail => simp [hAlternatives] at hCost
      | evaluating owner => rfl
      | value value => rfl
      | stableFault fault => rfl

theorem need_step_claim (cell : CellId) (record : CellRecord Origin Value StableFault)
    (hLookup : context.world.heap.lookup cell = some record)
    (hCache : record.cache = .suspended) (hRules : spec.alternatives record.origin ≠ []) :
    NeedExecution.step spec (taskMachine ⟨context, .force cell, stack⟩) =
      (ruleBranches context cell context.world.nextEvaluator record 0
          (spec.alternatives record.origin)).map
        (fun next =>
          taskMachine ⟨next.1, next.2, .commit cell context.world.nextEvaluator :: stack⟩) := by
  rw [ruleBranches_map]
  obtain ⟨head, tail, hAlternatives⟩ := List.exists_cons_of_ne_nil hRules
  simp only [taskMachine, Mode.attach, NeedExecution.step, hLookup, hCache, hAlternatives]

/-! Only a lookup of a suspended cell with rules produces a claim. -/

theorem resume_not_claim (frame : Frame Resume)
    (outcome : Produced Value StableFault RetryableFault) :
    (resume spec context frame outcome).2.isClaim = false := by
  cases frame with
  | resume token => rfl
  | commit cell owner =>
      simp only [resume]
      cases context.world.heap.lookup cell with
      | none => rfl
      | some record =>
          dsimp only
          cases record.cache with
          | evaluating actual =>
              dsimp only
              split
              · cases outcome <;> rfl
              · rfl
          | suspended => rfl
          | value value => rfl
          | stableFault fault => rfl

theorem actionBranches_not_claim (state : Local) :
    ∀ next ∈ actionBranches spec context state, next.2.isClaim = false := by
  simp only [actionBranches]
  cases spec.action state with
  | done outcome => simp [Context.transit, Mode.isClaim]
  | demand cell token => simp [Context.transit, Mode.isClaim]
  | allocate origin token =>
      dsimp only
      cases context.world.allocate? origin with
      | none => simp [Context.retry, Context.transit, Mode.isClaim]
      | some result =>
          rcases result with ⟨world, cell⟩
          simp [Context.transit, Mode.isClaim]
  | resample source token =>
      dsimp only
      cases context.world.heap.lookup source with
      | none => simp [Context.retry, Context.transit, Mode.isClaim]
      | some sourceRecord =>
          dsimp only
          cases context.world.allocate? sourceRecord.origin (source.generation + 1) with
          | none => simp [Context.retry, Context.transit, Mode.isClaim]
          | some result =>
              rcases result with ⟨world, fresh⟩
              simp [Context.transit, Mode.isClaim]
  | perform effect next => simp [Context.transit, Mode.isClaim]

theorem ruleBranches_not_claim (cell : CellId) (owner : EvaluatorId)
    (record : CellRecord Origin Value StableFault) (index : Nat)
    (alternatives : List (Rule × Local)) :
    ∀ next ∈ ruleBranches context cell owner record index alternatives,
      next.2.isClaim = false := by
  induction alternatives generalizing index with
  | nil => simp [ruleBranches]
  | cons head tail ih =>
      rcases head with ⟨rule, state⟩
      simp only [ruleBranches, List.mem_cons]
      rintro next (rfl | hNext)
      · rfl
      · exact ih (index + 1) next hNext

theorem lookupBranches_not_claim (cell : CellId)
    (hCost : cost spec ⟨context, .force cell, stack⟩ = 1) :
    ∀ next ∈ lookupBranches spec context cell, next.2.isClaim = false := by
  simp only [cost] at hCost
  simp only [lookupBranches]
  cases hLookup : context.world.heap.lookup cell with
  | none => simp [Context.retry, Context.transit, Mode.isClaim]
  | some record =>
      simp only [hLookup] at hCost
      dsimp only
      cases hCache : record.cache with
      | suspended =>
          simp only [hCache] at hCost
          dsimp only
          cases hAlternatives : spec.alternatives record.origin with
          | nil => simp [Context.retry, Context.transit, Mode.isClaim]
          | cons head tail => simp [hAlternatives] at hCost
      | evaluating owner => simp [Context.retry, Context.transit, Mode.isClaim]
      | value value => simp [Context.transit, Mode.isClaim]
      | stableFault fault => simp [Context.transit, Mode.isClaim]

end Simulation

section Exact

variable (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)

/-- **One need transition.** For a head task that is not an intermediate claim,
`cost` shared steps leave the pending frontier and the published prefix
untouched; the answers they publish followed by the tasks they create are
exactly the need machine's successors of that task, in order and with
multiplicity, and none of the new tasks is a claim. -/
theorem step_exact
    (task : NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (rest : List (NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect))
    (emitted : List (Context Origin Rule Value StableFault RetryableFault Effect ×
      Produced Value StableFault RetryableFault))
    (settled : task.control.isClaim = false) :
    ∃ published fresh,
      (SharedContinuation.step (program spec))^[cost spec task] ⟨task :: rest, emitted⟩ =
          ⟨fresh ++ rest, emitted ++ published⟩ ∧
        (∀ next ∈ fresh, next.control.isClaim = false) ∧
        published.map answerMachine ++ fresh.map taskMachine =
          NeedExecution.step spec (taskMachine task) := by
  rcases task with ⟨context, mode, stack⟩
  cases mode with
  | claim cell owner record => simp [Mode.isClaim] at settled
  | returned outcome =>
      cases stack with
      | nil => exact ⟨[(context, outcome)], [], rfl, by simp, rfl⟩
      | cons frame pending =>
          refine ⟨[], [⟨(resume spec context frame outcome).1,
            (resume spec context frame outcome).2, pending⟩], ?_, ?_, ?_⟩
          · rw [List.append_nil]
            rfl
          · simpa using resume_not_claim spec context frame outcome
          · simp [need_step_returned_cons]
  | run state =>
      refine ⟨[], (actionBranches spec context state).map
        (fun next => ⟨next.1, next.2, runReturns spec state stack⟩), ?_, ?_, ?_⟩
      · rw [List.append_nil]
        exact step_run spec context stack rest emitted state
      · simp only [List.mem_map]
        rintro _ ⟨next, hNext, rfl⟩
        exact actionBranches_not_claim spec context state next hNext
      · simp [need_step_run, List.map_map]
  | force cell =>
      by_cases hCost : cost spec ⟨context, .force cell, stack⟩ = 1
      · rw [hCost]
        refine ⟨[], (lookupBranches spec context cell).map
          (fun next => ⟨next.1, next.2, stack⟩), ?_, ?_, ?_⟩
        · rw [List.append_nil]
          exact step_force spec context stack rest emitted cell
        · simp only [List.mem_map]
          rintro _ ⟨next, hNext, rfl⟩
          exact lookupBranches_not_claim spec context stack cell hCost next hNext
        · simp [need_step_force spec context stack cell hCost, List.map_map]
      · obtain ⟨record, hLookup, hCache, hRules⟩ :=
          claim_of_cost_ne_one spec context stack cell hCost
        rw [cost_force_eq_two spec context stack cell record hLookup hCache hRules]
        refine ⟨[], (ruleBranches context cell context.world.nextEvaluator record 0
            (spec.alternatives record.origin)).map
          (fun next => ⟨next.1, next.2, .commit cell context.world.nextEvaluator :: stack⟩),
          ?_, ?_, ?_⟩
        · rw [List.append_nil]
          show SharedContinuation.step (program spec)
            (SharedContinuation.step (program spec) _) = _
          rw [step_force, lookupBranches_claim spec context cell record hLookup hCache hRules]
          exact step_claim spec context stack rest emitted cell _ record
        · simp only [List.mem_map]
          rintro _ ⟨next, hNext, rfl⟩
          exact ruleBranches_not_claim context cell _ record 0 _ next hNext
        · simp [need_step_claim spec context stack cell record hLookup hCache hRules,
            List.map_map]

end Exact

/-! ## Depth-first and breadth-first schedules of the need machine -/

section Schedules

variable (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)

open NeedExecution (isHalted)

theorem need_step_halted
    {machine : CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (halted : isHalted machine = true) :
    NeedExecution.step spec machine = [] := by
  rcases machine with ⟨world, control, work⟩
  cases control <;> first | rfl | simp [isHalted] at halted

/-- The need machine never drops a running branch: a rule-less cell and a
lost update are published retryable outcomes, not exhaustion. -/
theorem need_step_ne_nil
    {machine : CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (running : isHalted machine = false) :
    NeedExecution.step spec machine ≠ [] := by
  rcases machine with ⟨world, control, work⟩
  cases control with
  | halted outcome => simp [isHalted] at running
  | force cell stack =>
      simp only [NeedExecution.step]
      cases world.heap.lookup cell with
      | none => simp
      | some record =>
          dsimp only
          cases record.cache with
          | suspended =>
              dsimp only
              cases spec.alternatives record.origin with
              | nil => simp
              | cons head tail =>
                  rcases head with ⟨rule, state⟩
                  simp [NeedExecution.branchAlternatives]
          | evaluating owner => simp
          | value value => simp
          | stableFault fault => simp
  | run state stack =>
      simp only [NeedExecution.step]
      cases spec.action state with
      | done outcome => simp
      | demand cell token => simp
      | allocate origin token =>
          dsimp only
          cases world.allocate? origin with
          | none => simp
          | some result =>
              rcases result with ⟨next, cell⟩
              simp
      | resample source token =>
          dsimp only
          cases world.heap.lookup source with
          | none => simp
          | some sourceRecord =>
              dsimp only
              cases world.allocate? sourceRecord.origin (source.generation + 1) with
              | none => simp
              | some result =>
                  rcases result with ⟨next, fresh⟩
                  simp
      | perform effect next => simp
  | returned outcome stack =>
      simp only [NeedExecution.step]
      cases stack with
      | nil => simp
      | cons frame rest =>
          cases frame with
          | resume token => simp
          | commit cell owner =>
              dsimp only
              cases world.heap.lookup cell with
              | none => simp
              | some record =>
                  dsimp only
                  cases record.cache with
                  | evaluating actual =>
                      dsimp only
                      split
                      · cases outcome <;> simp
                      · simp
                  | suspended => simp
                  | value value => simp
                  | stableFault fault => simp

theorem advance_of_halted
    {machine : CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (halted : isHalted machine = true) :
    NeedExecution.advance spec machine = [machine] := by
  simp [NeedExecution.advance, need_step_halted spec halted]

theorem advance_of_running
    {machine : CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (running : isHalted machine = false) :
    NeedExecution.advance spec machine = NeedExecution.step spec machine := by
  unfold NeedExecution.advance
  cases hStep : NeedExecution.step spec machine with
  | nil => exact absurd hStep (need_step_ne_nil spec running)
  | cons head tail => rfl

theorem flatMap_advance_of_all_halted
    {states :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (halted : states.all isHalted = true) :
    states.flatMap (NeedExecution.advance spec) = states := by
  induction states with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.all_cons, Bool.and_eq_true] at halted
      simp [advance_of_halted spec halted.1, ih halted.2]

theorem runFrontier_of_all_halted (fuel : Nat)
    {states :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (halted : states.all isHalted = true) :
    NeedExecution.runFrontier spec fuel states = states := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [NeedExecution.runFrontier, halted]

/-- A round of the breadth-first schedule leaves halted machines in place, so
the early exit of `runFrontier` is only an optimization. -/
theorem runFrontier_succ (fuel : Nat)
    (states :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    NeedExecution.runFrontier spec (fuel + 1) states =
      NeedExecution.runFrontier spec fuel (states.flatMap (NeedExecution.advance spec)) := by
  by_cases halted : states.all isHalted = true
  · rw [flatMap_advance_of_all_halted spec halted, runFrontier_of_all_halted spec _ halted,
      runFrontier_of_all_halted spec _ halted]
  · simp [NeedExecution.runFrontier, halted]

/-- The breadth-first schedule acts on the machines of a frontier independently. -/
theorem runFrontier_append (fuel : Nat)
    (left right :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    NeedExecution.runFrontier spec fuel (left ++ right) =
      NeedExecution.runFrontier spec fuel left ++ NeedExecution.runFrontier spec fuel right := by
  induction fuel generalizing left right with
  | zero => rfl
  | succ fuel ih => simp only [runFrontier_succ, List.flatMap_append, ih]

theorem runFrontier_succ_of_all_halted (fuel : Nat)
    (states :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect))
    (halted : (NeedExecution.runFrontier spec fuel states).all isHalted = true) :
    NeedExecution.runFrontier spec (fuel + 1) states =
      NeedExecution.runFrontier spec fuel states := by
  induction fuel generalizing states with
  | zero => exact runFrontier_of_all_halted spec 1 halted
  | succ fuel ih =>
      rw [runFrontier_succ] at halted
      rw [runFrontier_succ, runFrontier_succ spec fuel states]
      exact ih _ halted

/-- Once every machine has halted, more fuel changes nothing. -/
theorem runFrontier_stable {fuel more : Nat}
    {states :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (halted : (NeedExecution.runFrontier spec fuel states).all isHalted = true)
    (bound : fuel ≤ more) :
    NeedExecution.runFrontier spec more states = NeedExecution.runFrontier spec fuel states := by
  induction more, bound using Nat.le_induction with
  | base => rfl
  | succ more _ ih =>
      rw [runFrontier_succ_of_all_halted spec more states (ih ▸ halted), ih]

/-- The depth-first schedule: expand the leftmost running machine. -/
def expandFirst :
    List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect) →
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)
  | [] => []
  | machine :: rest =>
      if isHalted machine then machine :: expandFirst rest
      else NeedExecution.step spec machine ++ rest

theorem expandFirst_append_of_all_halted
    {left :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (halted : left.all isHalted = true)
    (right :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    expandFirst spec (left ++ right) = left ++ expandFirst spec right := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.all_cons, Bool.and_eq_true] at halted
      simp [expandFirst, halted.1, ih halted.2]

theorem expandFirst_append_of_running
    {left :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (running : left.all isHalted = false)
    (right :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    expandFirst spec (left ++ right) = expandFirst spec left ++ right := by
  induction left with
  | nil => simp at running
  | cons head tail ih =>
      by_cases halted : isHalted head = true
      · simp only [List.all_cons, halted, Bool.true_and] at running
        simp [expandFirst, halted, ih running]
      · simp [expandFirst, halted]

theorem expandFirst_of_all_halted
    {states :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (halted : states.all isHalted = true) :
    expandFirst spec states = states := by
  simpa [expandFirst] using expandFirst_append_of_all_halted spec halted []

/-- `Completes spec states final count`: the depth-first schedule started at
`states` halts every machine after exactly `count` expansions, at `final`. -/
inductive Completes :
    List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect) →
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect) →
        Nat → Prop
  | halted {states} (halted : states.all isHalted = true) : Completes states states 0
  | expand {states final count} (running : states.all isHalted = false)
      (next : Completes (expandFirst spec states) final count) :
      Completes states final (count + 1)

namespace Completes

variable {spec}

theorem all_halted
    {states final :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    {count : Nat} (run : Completes spec states final count) :
    final.all isHalted = true := by
  induction run with
  | halted halted => exact halted
  | expand _ _ ih => exact ih

theorem iterate
    {states final :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    {count : Nat} (run : Completes spec states final count) :
    (expandFirst spec)^[count] states = final := by
  induction run with
  | halted => rfl
  | expand _ _ ih => rw [Function.iterate_succ_apply, ih]

/-- Depth-first runs of consecutive frontier segments compose. -/
theorem append
    {left left' right right' :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    {count count' : Nat}
    (first : Completes spec left left' count) (second : Completes spec right right' count') :
    Completes spec (left ++ right) (left' ++ right') (count + count') := by
  induction first with
  | @halted left halted =>
      rw [Nat.zero_add]
      induction second with
      | halted halted' => exact .halted (by simp [halted, halted'])
      | @expand right right' count' running _ ih =>
          refine .expand (by simp [halted, running]) ?_
          rw [expandFirst_append_of_all_halted spec halted]
          exact ih
  | @expand left left' count running _ ih =>
      rw [Nat.add_right_comm]
      refine .expand (by simp [running]) ?_
      rw [expandFirst_append_of_running spec running]
      exact ih

end Completes

theorem exists_first_running
    {states :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (running : states.all isHalted = false) :
    ∃ halts machine rest, states = halts ++ machine :: rest ∧
      halts.all isHalted = true ∧ isHalted machine = false := by
  induction states with
  | nil => simp at running
  | cons head tail ih =>
      by_cases halted : isHalted head = true
      · simp only [List.all_cons, halted, Bool.true_and] at running
        obtain ⟨halts, machine, rest, rfl, hHalts, hMachine⟩ := ih running
        exact ⟨head :: halts, machine, rest, rfl, by simp [halted, hHalts], hMachine⟩
      · exact ⟨[], head, tail, rfl, rfl, by simpa using halted⟩

/-- A completed depth-first run is the bounded breadth-first run with the same
number of rounds as expansions. -/
theorem Completes.runFrontier
    {states final :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    {count : Nat} (run : Completes spec states final count) :
    NeedExecution.runFrontier spec count states = final := by
  induction run with
  | halted => rfl
  | @expand states final count running next ih =>
      obtain ⟨halts, machine, rest, rfl, hHalts, hMachine⟩ := exists_first_running running
      have expanded : expandFirst spec (halts ++ machine :: rest) =
          halts ++ (NeedExecution.step spec machine ++ rest) := by
        rw [expandFirst_append_of_all_halted spec hHalts]
        simp [expandFirst, hMachine]
      rw [expanded, runFrontier_append, runFrontier_append,
        runFrontier_of_all_halted spec _ hHalts] at ih
      have restHalted : (NeedExecution.runFrontier spec count rest).all isHalted = true := by
        have := next.all_halted
        rw [← ih] at this
        simp only [List.all_append, Bool.and_eq_true] at this
        exact this.2.2
      rw [runFrontier_succ, List.flatMap_append, flatMap_advance_of_all_halted spec hHalts,
        List.flatMap_cons, advance_of_running spec hMachine, runFrontier_append,
        runFrontier_append, runFrontier_of_all_halted spec _ hHalts, ← runFrontier_succ,
        runFrontier_succ_of_all_halted spec count rest restHalted, ih]

/-- Every completed bounded breadth-first run is reached by the depth-first
schedule. -/
theorem completes_of_runFrontier (fuel : Nat)
    (states :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect))
    (halted : (NeedExecution.runFrontier spec fuel states).all isHalted = true) :
    ∃ count, Completes spec states (NeedExecution.runFrontier spec fuel states) count := by
  induction fuel generalizing states with
  | zero => exact ⟨0, .halted halted⟩
  | succ fuel ih =>
      induction states with
      | nil =>
          rw [runFrontier_of_all_halted spec _ rfl]
          exact ⟨0, .halted rfl⟩
      | cons machine rest ihRest =>
          have split : NeedExecution.runFrontier spec (fuel + 1) (machine :: rest) =
              NeedExecution.runFrontier spec (fuel + 1) [machine] ++
                NeedExecution.runFrontier spec (fuel + 1) rest :=
            runFrontier_append spec (fuel + 1) [machine] rest
          rw [split] at halted ⊢
          simp only [List.all_append, Bool.and_eq_true] at halted
          obtain ⟨restCount, restRun⟩ := ihRest halted.2
          have headRun : ∃ count, Completes spec [machine]
              (NeedExecution.runFrontier spec (fuel + 1) [machine]) count := by
            by_cases hMachine : isHalted machine = true
            · rw [runFrontier_of_all_halted spec _ (by simp [hMachine])]
              exact ⟨0, .halted (by simp [hMachine])⟩
            · have running : isHalted machine = false := by simpa using hMachine
              have unfolded : NeedExecution.runFrontier spec (fuel + 1) [machine] =
                  NeedExecution.runFrontier spec fuel (NeedExecution.step spec machine) := by
                rw [runFrontier_succ]
                simp [advance_of_running spec running]
              rw [unfolded] at halted ⊢
              obtain ⟨count, run⟩ := ih _ halted.1
              refine ⟨count + 1, .expand (by simp [running]) ?_⟩
              simpa [expandFirst, running] using run
          obtain ⟨headCount, headRun⟩ := headRun
          exact ⟨headCount + restCount, headRun.append restRun⟩

end Schedules

/-! ## Shared runs are depth-first need runs -/

section Runs

variable (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)

open NeedExecution (isHalted)

/-- No pending task is an intermediate claim. Encoded need machines are
settled, and each completed need transition returns to a settled state. -/
def Settled (state : NeedState Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Prop :=
  ∀ task ∈ state.frontier, task.control.isClaim = false

theorem taskMachine_running
    (task : NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    isHalted (taskMachine task) = false := by
  rcases task with ⟨context, mode, stack⟩
  cases mode <;> rfl

theorem machines_all_halted_iff
    (state : NeedState Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (machines state).all isHalted = true ↔ state.frontier = [] := by
  rcases state with ⟨frontier, emitted⟩
  cases frontier with
  | nil => simp [machines, answerMachine, isHalted]
  | cons task rest => simp [machines, taskMachine_running]

theorem cost_pos_le_two
    (task : NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    1 ≤ cost spec task ∧ cost spec task ≤ 2 := by
  rcases task with ⟨context, mode, stack⟩
  cases mode with
  | force cell =>
      by_cases hCost : cost spec ⟨context, .force cell, stack⟩ = 1
      · omega
      · obtain ⟨record, hLookup, hCache, hRules⟩ :=
          claim_of_cost_ne_one spec context stack cell hCost
        rw [cost_force_eq_two spec context stack cell record hLookup hCache hRules]
        omega
  | claim cell owner record => simp [cost]
  | run state => simp [cost]
  | returned outcome => simp [cost]

/-- One need transition of the depth-first schedule, in `cost` shared steps. -/
theorem machines_step_exact
    (state : NeedState Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (settled : Settled state)
    (task : NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (rest : List (NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect))
    (hFrontier : state.frontier = task :: rest) :
    Settled ((SharedContinuation.step (program spec))^[cost spec task] state) ∧
      machines ((SharedContinuation.step (program spec))^[cost spec task] state) =
        expandFirst spec (machines state) := by
  rcases state with ⟨frontier, emitted⟩
  simp only at hFrontier
  subst hFrontier
  obtain ⟨published, fresh, hRun, hFresh, hSuccessors⟩ :=
    step_exact spec task rest emitted (settled task (by simp))
  rw [hRun]
  refine ⟨?_, ?_⟩
  · intro next hNext
    rcases List.mem_append.mp hNext with hNext | hNext
    · exact hFresh next hNext
    · exact settled next (by simp [hNext])
  · have answered :
        (emitted.map (answerMachine (Local := Local) (Resume := Resume))).all isHalted = true := by
      simp [answerMachine, isHalted]
    simp only [machines, List.map_append, List.map_cons]
    rw [expandFirst_append_of_all_halted spec answered]
    simp only [expandFirst, taskMachine_running, Bool.false_eq_true, ↓reduceIte,
      ← hSuccessors, List.append_assoc]

/-- The claim dispatch is invisible at the need level and keeps the task pending. -/
theorem claim_step_silent
    (task : NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (rest : List (NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect))
    (emitted : List (Context Origin Rule Value StableFault RetryableFault Effect ×
      Produced Value StableFault RetryableFault))
    (hCost : cost spec task = 2) :
    machines (SharedContinuation.step (program spec) ⟨task :: rest, emitted⟩) =
        machines ⟨task :: rest, emitted⟩ ∧
      (SharedContinuation.step (program spec) ⟨task :: rest, emitted⟩).frontier ≠ [] := by
  rcases task with ⟨context, mode, stack⟩
  cases mode with
  | force cell =>
      obtain ⟨record, hLookup, hCache, hRules⟩ :=
        claim_of_cost_ne_one spec context stack cell (by omega)
      rw [step_force, lookupBranches_claim spec context cell record hLookup hCache hRules]
      exact ⟨rfl, by simp⟩
  | claim cell owner record => simp [cost] at hCost
  | run state => simp [cost] at hCost
  | returned outcome => simp [cost] at hCost

theorem frontier_ne_nil_before_cost
    (task : NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (rest : List (NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect))
    (emitted : List (Context Origin Rule Value StableFault RetryableFault Effect ×
      Produced Value StableFault RetryableFault))
    (steps : Nat) (early : steps < cost spec task) :
    ((SharedContinuation.step (program spec))^[steps] ⟨task :: rest, emitted⟩).frontier ≠
      [] := by
  obtain ⟨_, atMostTwo⟩ := cost_pos_le_two spec task
  match steps, early with
  | 0, _ => simp
  | 1, early =>
      rw [Function.iterate_one]
      exact (claim_step_silent spec task rest emitted (by omega)).2
  | _ + 2, early => omega

theorem iterate_idle {Ctx Ctl Callee Frm Ans : Type} (P : Program Ctx Ctl Callee Frm Ans)
    (state : State Ctx Ctl Frm Ans) (idle : state.frontier = []) (steps : Nat) :
    (SharedContinuation.step P)^[steps] state = state := by
  apply Function.iterate_fixed
  rcases state with ⟨frontier, emitted⟩
  simp only at idle
  subst idle
  rfl

/-- A completed depth-first need run is reached by the shared run, with
between one and two shared steps per need transition. -/
theorem program_of_completes
    (state : NeedState Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (settled : Settled state)
    {final :
      List (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    {count : Nat} (run : Completes spec (machines state) final count) :
    ∃ steps, count ≤ steps ∧ steps ≤ 2 * count ∧
      ((SharedContinuation.step (program spec))^[steps] state).frontier = [] ∧
      machines ((SharedContinuation.step (program spec))^[steps] state) = final := by
  generalize hMachines : machines state = states at run
  induction run generalizing state with
  | halted halted =>
      subst hMachines
      exact ⟨0, le_rfl, by omega, (machines_all_halted_iff state).1 halted, rfl⟩
  | @expand states final count running next ih =>
      subst hMachines
      obtain ⟨task, rest, hFrontier⟩ : ∃ task rest, state.frontier = task :: rest := by
        cases hEmpty : state.frontier with
        | nil =>
            have := (machines_all_halted_iff state).2 hEmpty
            rw [this] at running
            exact absurd running (by decide)
        | cons task rest => exact ⟨task, rest, rfl⟩
      obtain ⟨settledNext, hNext⟩ := machines_step_exact spec state settled task rest hFrontier
      obtain ⟨steps, hLow, hHigh, hDone, hFinal⟩ := ih _ settledNext hNext
      obtain ⟨hPos, hLe⟩ := cost_pos_le_two spec task
      refine ⟨steps + cost spec task, by omega, by omega, ?_, ?_⟩
      · rw [Function.iterate_add_apply]
        exact hDone
      · rw [Function.iterate_add_apply]
        exact hFinal

/-- A shared run that has published everything is a completed depth-first need
run, with at most as many need transitions as shared steps. -/
theorem completes_of_program (steps : Nat)
    (state : NeedState Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (settled : Settled state)
    (done : ((SharedContinuation.step (program spec))^[steps] state).frontier = []) :
    ∃ count ≤ steps, Completes spec (machines state)
      (machines ((SharedContinuation.step (program spec))^[steps] state)) count := by
  induction steps using Nat.strong_induction_on generalizing state with
  | _ steps ih =>
      rcases state with ⟨frontier, emitted⟩
      cases frontier with
      | nil =>
          rw [iterate_idle _ _ rfl]
          exact ⟨0, Nat.zero_le _, .halted ((machines_all_halted_iff _).2 rfl)⟩
      | cons task rest =>
          obtain ⟨hPos, _⟩ := cost_pos_le_two spec task
          by_cases hSteps : cost spec task ≤ steps
          · obtain ⟨settledNext, hNext⟩ :=
              machines_step_exact spec ⟨task :: rest, emitted⟩ settled task rest rfl
            have split :
                (SharedContinuation.step (program spec))^[steps] ⟨task :: rest, emitted⟩ =
                  (SharedContinuation.step (program spec))^[steps - cost spec task]
                    ((SharedContinuation.step (program spec))^[cost spec task]
                      ⟨task :: rest, emitted⟩) := by
              rw [← Function.iterate_add_apply, Nat.sub_add_cancel hSteps]
            rw [split] at done ⊢
            obtain ⟨count, hCount, run⟩ :=
              ih (steps - cost spec task) (by omega) _ settledNext done
            rw [hNext] at run
            refine ⟨count + 1, by omega, .expand ?_ run⟩
            simp [machines, taskMachine_running]
          · exact absurd done
              (frontier_ne_nil_before_cost spec task rest emitted steps (by omega))

/-- **Completed shared runs are bounded need runs.** If the shared run has
published everything after `steps` steps, the need machine's breadth-first run
with fuel `steps` ends in exactly the published halted machines: same order,
worlds, outcomes, work counters and duplicates. -/
theorem runFrontier_eq_of_program (steps : Nat)
    (state : NeedState Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (settled : Settled state)
    (done : ((SharedContinuation.step (program spec))^[steps] state).frontier = []) :
    NeedExecution.runFrontier spec steps (machines state) =
      machines ((SharedContinuation.step (program spec))^[steps] state) := by
  obtain ⟨count, hCount, run⟩ := completes_of_program spec steps state settled done
  rw [runFrontier_stable spec (by rw [run.runFrontier]; exact run.all_halted) hCount,
    run.runFrontier]

/-- **Completed bounded need runs are shared runs.** -/
theorem program_of_runFrontier (fuel : Nat)
    (state : NeedState Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (settled : Settled state)
    (complete : (NeedExecution.runFrontier spec fuel (machines state)).all isHalted = true) :
    ∃ steps, ((SharedContinuation.step (program spec))^[steps] state).frontier = [] ∧
      machines ((SharedContinuation.step (program spec))^[steps] state) =
        NeedExecution.runFrontier spec fuel (machines state) := by
  obtain ⟨count, run⟩ := completes_of_runFrontier spec fuel (machines state) complete
  obtain ⟨steps, -, -, hDone, hFinal⟩ := program_of_completes spec state settled run
  exact ⟨steps, hDone, hFinal⟩

theorem filterMap_haltedOutcome_machines
    (state : NeedState Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (done : state.frontier = []) :
    (machines state).filterMap NeedExecution.haltedOutcome = state.emitted.map Prod.snd := by
  rcases state with ⟨frontier, emitted⟩
  simp only at done
  subst done
  induction emitted with
  | nil => rfl
  | cons answer emitted ih =>
      simpa [machines, answerMachine, NeedExecution.haltedOutcome] using ih

theorem settled_single
    (task : NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (settled : task.control.isClaim = false) :
    Settled (⟨[task], []⟩ :
      NeedState Origin Local Resume Rule Value StableFault RetryableFault Effect) := by
  intro next hNext
  simp only [List.mem_singleton] at hNext
  exact hNext ▸ settled

/-- **Answers.** When the shared run of a task has published everything after
`steps` steps, the need machine's answers with fuel `steps` are exactly the
published outcomes, in order and with multiplicity. -/
theorem answers_eq_of_program
    (task : NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (settled : task.control.isClaim = false) (steps : Nat)
    (done : ((SharedContinuation.step (program spec))^[steps] ⟨[task], []⟩).frontier = []) :
    NeedExecution.answers spec steps (taskMachine task) =
      ((SharedContinuation.step (program spec))^[steps] ⟨[task], []⟩).emitted.map Prod.snd := by
  unfold NeedExecution.answers
  rw [show [taskMachine task] = machines ⟨[task], []⟩ from rfl,
    runFrontier_eq_of_program spec steps _ (settled_single task settled) done,
    filterMap_haltedOutcome_machines _ done]

/-- Conversely, whenever the bounded need run of a task completes, the shared
run publishes exactly its answers. -/
theorem program_of_answers
    (task : NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (settled : task.control.isClaim = false) (fuel : Nat)
    (complete : (NeedExecution.runFrontier spec fuel [taskMachine task]).all isHalted = true) :
    ∃ steps, ((SharedContinuation.step (program spec))^[steps] ⟨[task], []⟩).frontier = [] ∧
      ((SharedContinuation.step (program spec))^[steps] ⟨[task], []⟩).emitted.map Prod.snd =
        NeedExecution.answers spec fuel (taskMachine task) := by
  obtain ⟨steps, hDone, hFinal⟩ :=
    program_of_runFrontier spec fuel ⟨[task], []⟩ (settled_single task settled) complete
  refine ⟨steps, hDone, ?_⟩
  unfold NeedExecution.answers
  rw [show [taskMachine task] = machines ⟨[task], []⟩ from rfl, ← hFinal,
    filterMap_haltedOutcome_machines _ hDone]

/-! ### Arena realization -/

theorem decode_checkedStep_iterate {Ctx Ctl Callee Frm Ans : Type}
    (P : Program Ctx Ctl Callee Frm Ans)
    (state : SharedContinuation.CheckedState Ctx Ctl Frm Ans) (steps : Nat) :
    ((SharedContinuation.checkedStep P)^[steps] state).1.decode =
      (SharedContinuation.step P)^[steps] state.1.decode := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih,
        SharedContinuation.decode_checkedStep]

/-- The arena realization publishes the need machine's answers. -/
theorem arena_answers_eq_of_program
    (task : NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (settled : task.control.isClaim = false) (steps : Nat)
    (done : ((SharedContinuation.checkedStep (program spec))^[steps]
      (SharedContinuation.encode ⟨[task], []⟩)).1.frontier = []) :
    NeedExecution.answers spec steps (taskMachine task) =
      ((SharedContinuation.checkedStep (program spec))^[steps]
        (SharedContinuation.encode ⟨[task], []⟩)).1.emitted.map Prod.snd := by
  have decoded := decode_checkedStep_iterate (program spec)
    (SharedContinuation.encode ⟨[task], []⟩) steps
  rw [SharedContinuation.decode_encode] at decoded
  have referenceDone :
      ((SharedContinuation.step (program spec))^[steps] ⟨[task], []⟩).frontier = [] := by
    rw [← decoded]
    simp [SharedContinuation.ArenaState.decode, done]
  rw [answers_eq_of_program spec task settled steps referenceDone, ← decoded]
  rfl

end Runs

/-! ## The frame effect of one shared step ignores the context -/

/-- `inspect` reads the control only, so one shared step pushes or pops the
same return frames whatever the task context is. -/
theorem step_returns_context_free {Ctx Ctl Callee Frm Ans : Type}
    (P : Program Ctx Ctl Callee Frm Ans) (first second : Ctx) (control : Ctl)
    (stack : List Frm) :
    ∀ left ∈ (SharedContinuation.step P ⟨[⟨first, control, stack⟩], []⟩).frontier,
      ∀ right ∈ (SharedContinuation.step P ⟨[⟨second, control, stack⟩], []⟩).frontier,
        left.returns = right.returns := by
  simp only [SharedContinuation.step]
  cases P.inspect control with
  | ret value =>
      cases stack with
      | nil => simp
      | cons frame pending => simp_all
  | fail => simp
  | call callee frame =>
      simp only [List.append_nil, List.mem_map]
      rintro _ ⟨_, _, rfl⟩ _ ⟨_, _, rfl⟩
      rfl
  | tail callee =>
      simp only [List.append_nil, List.mem_map]
      rintro _ ⟨_, _, rfl⟩ _ ⟨_, _, rfl⟩
      rfl

/-! ## Returning to retained sites in one branch -/

/-- One captured resume token with its complete pending return stack. -/
abbrev ReturnSite (Resume : Type) := Resume × List (Frame Resume)

/-- Resume each retained site in one selected branch world, preserving order and
multiplicity. This is a semantic delivery boundary, not a worker registry or a
merge of worlds. The caller supplies the actual outcome of a checked commit. -/
def returnCohort
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (context : Context Origin Rule Value StableFault RetryableFault Effect)
    (outcome : Produced Value StableFault RetryableFault)
    (sites : List (ReturnSite Resume)) :
    List (NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect) :=
  sites.foldr (fun site rest =>
    let next := resume spec context (.resume site.1) outcome
    ⟨next.1, next.2, site.2⟩ :: rest) []

/-- The delivered tasks, decoded, are exactly the independently defined need
steps of those same captured sites. -/
theorem returnCohort_need_steps
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (context : Context Origin Rule Value StableFault RetryableFault Effect)
    (outcome : Produced Value StableFault RetryableFault)
    (sites : List (ReturnSite Resume)) :
    (returnCohort spec context outcome sites).map taskMachine =
      sites.flatMap (fun site => NeedExecution.step spec
        (taskMachine ⟨context, .returned outcome, .resume site.1 :: site.2⟩)) := by
  induction sites with
  | nil => rfl
  | cons site sites ih =>
      change _ :: (returnCohort spec context outcome sites).map taskMachine =
        _ :: sites.flatMap (fun site => NeedExecution.step spec
          (taskMachine ⟨context, .returned outcome, .resume site.1 :: site.2⟩))
      rw [ih]
      rfl

theorem returnCohort_length
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (context : Context Origin Rule Value StableFault RetryableFault Effect)
    (outcome : Produced Value StableFault RetryableFault)
    (sites : List (ReturnSite Resume)) :
    (returnCohort spec context outcome sites).length = sites.length := by
  induction sites with
  | nil => rfl
  | cons site sites ih => simp only [returnCohort, List.foldr_cons, List.length_cons] at *; omega

theorem returnCohort_member
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (context : Context Origin Rule Value StableFault RetryableFault Effect)
    (outcome : Produced Value StableFault RetryableFault)
    (sites : List (ReturnSite Resume))
    (task : NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (member : task ∈ returnCohort spec context outcome sites) :
    ∃ site ∈ sites,
      task.context.world = context.world ∧
      task.control = .run (spec.afterDemand site.1 outcome) ∧
      task.returns = site.2 ∧
      task.context.work.transitions = context.work.transitions + 1 := by
  induction sites with
  | nil => simp [returnCohort] at member
  | cons site sites ih =>
      simp only [returnCohort, List.foldr_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨site, by simp, rfl, rfl, rfl, rfl⟩
      · obtain ⟨found, hfound, properties⟩ := ih member
        exact ⟨found, by simp [hfound], properties⟩

/-- A successful owned commit supplies the same cached value to every site in
this branch. It does not authorize delivery across incompatible worlds. -/
theorem committed_returnCohort_cache
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (context : Context Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (owner : EvaluatorId) (value : Value)
    (present : context.world.heap.lookup cell = some record)
    (owned : record.cache = .evaluating owner)
    (sites : List (ReturnSite Resume))
    (task : NeedTask Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (member : task ∈ returnCohort spec
      (resume spec context (.commit cell owner) (.value value)).1 (.value value) sites) :
    task.context.world.heap.lookup cell = some { record with cache := .value value } := by
  obtain ⟨site, _, sameWorld, _⟩ := returnCohort_member spec _ (.value value) sites task member
  rw [sameWorld]
  simp [resume, present, owned, Context.transit, CoreWorld.setKnownCache]

theorem mismatched_commit_is_not_value
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (context : Context Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (owner actual : EvaluatorId) (value : Value)
    (present : context.world.heap.lookup cell = some record)
    (owned : record.cache = .evaluating actual) (different : actual ≠ owner) :
    (resume spec context (.commit cell owner) (.value value)).2 =
      .returned (.retryableFault (.ownershipLost cell owner actual)) := by
  simp [resume, present, owned, different, Context.retry, Context.transit]

theorem returnCohort_append
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (context : Context Origin Rule Value StableFault RetryableFault Effect)
    (outcome : Produced Value StableFault RetryableFault)
    (first later : List (ReturnSite Resume)) :
    returnCohort spec context outcome (first ++ later) =
      returnCohort spec context outcome first ++ returnCohort spec context outcome later := by
  induction first with
  | nil => rfl
  | cons site sites ih =>
      change _ :: returnCohort spec context outcome (sites ++ later) =
        _ :: (returnCohort spec context outcome sites ++ returnCohort spec context outcome later)
      rw [ih]


/-! ## A two-demand example -/

namespace Demo

/-- Local states: demand the cell twice and add the two observations. -/
inductive Code where
  | twice
  | again (first : Nat)
  | total (sum : Nat)
  | body
  | propagate (outcome : Produced Nat Unit Unit)

/-- Resume tokens after the first and after the second demand. -/
inductive Token where
  | first
  | second (first : Nat)

def demoCell : CellId := ⟨0, [], 0, 0⟩

/-- The cell has one rule, which yields `21`; faults are passed on. -/
def demoSpec : Spec Unit Code Token Unit Nat Unit Unit Unit where
  alternatives _ := [((), .body)]
  action
    | .twice => .demand demoCell .first
    | .again first => .demand demoCell (.second first)
    | .total sum => .done (.value sum)
    | .body => .done (.value 21)
    | .propagate outcome => .done outcome
  afterDemand
    | .first, .value value => .again value
    | .second first, .value value => .total (first + value)
    | _, outcome => .propagate outcome
  afterAllocation _ _ := .total 0

/-- One suspended cell with a single rule. -/
def demoWorld : CoreWorld Unit Unit Nat Unit Unit Unit where
  lineage := 0
  path := []
  heap :=
    { current := Function.update (fun _ => none) demoCell (some ⟨(), .suspended⟩)
      spine := [.allocate demoCell ()] }
  nextCell := 1
  nextEvaluator := 0

def demoTask : NeedTask Unit Code Token Unit Nat Unit Unit Unit :=
  ⟨⟨demoWorld, {}⟩, .run .twice, []⟩

def demoRun (steps : Nat) : NeedState Unit Code Token Unit Nat Unit Unit Unit :=
  (SharedContinuation.step (program demoSpec))^[steps] ⟨[demoTask], []⟩

/-- The demand pushes its resume token; the first force of the cell costs two
shared steps. -/
example : (demoRun 1).frontier.map (·.returns) = [[.resume .first]] := rfl

example : (demoRun 1).frontier.map (cost demoSpec) = [2] := by decide

/-- The lookup reifies a claim, changing neither the context nor the returns. -/
example :
    (demoRun 2).frontier.map (fun task => (task.control.isClaim, task.returns.length)) =
      [(true, 1)] := by decide

/-- The claim pushes the update frame above the resume token, in the forked
branch world where owner `0` is evaluating the cell. -/
example :
    (demoRun 3).frontier.map (·.returns) = [[.commit demoCell 0, .resume .first]] := rfl

example :
    (demoRun 3).frontier.map
        (fun task => (task.context.world.path, task.context.world.heap.lookup demoCell)) =
      [([0], some ⟨(), .evaluating 0⟩)] := by decide

/-- Returning through the update frame writes the cache and pops the frame. -/
example :
    (demoRun 5).frontier.map
        (fun task => (task.context.world.heap.lookup demoCell, task.returns.length)) =
      [(some ⟨(), .value 21⟩, 1)] := by decide

/-- The second force of the same cell: one shared step, a cache hit, and no
frame pushed. -/
example : (demoRun 7).frontier.map (·.control) = [.force demoCell] := rfl

example : (demoRun 7).frontier.map (cost demoSpec) = [1] := by decide

example :
    (demoRun 8).frontier.map (fun task => (task.control, task.returns)) =
      [(.returned (.value 21), [.resume (.second 21)])] := rfl

/-- Eleven shared steps publish the single answer: ten need transitions and one
claim dispatch. -/
example : (demoRun 10).frontier.length = 1 := by decide

example : (demoRun 11).frontier = [] ∧ (demoRun 11).emitted.map Prod.snd = [.value 42] :=
  ⟨rfl, by decide⟩

example :
    (NeedExecution.runFrontier demoSpec 9 [taskMachine demoTask]).all
      NeedExecution.isHalted = false := by decide

example : NeedExecution.answers demoSpec 10 (taskMachine demoTask) = [.value 42] := by decide

/-- The general theorem, instantiated: no evaluation beyond the frontier check. -/
example :
    NeedExecution.answers demoSpec 11 (taskMachine demoTask) =
      (demoRun 11).emitted.map Prod.snd :=
  answers_eq_of_program demoSpec demoTask rfl 11 rfl

/-- The arena realization, run directly. -/
example :
    ((SharedContinuation.checkedStep (program demoSpec))^[11]
        (SharedContinuation.encode ⟨[demoTask], []⟩)).1.emitted.map Prod.snd =
      [.value 42] := by
  decide

/-! ### Retained return sites -/

private def cohortSites : List (ReturnSite Token) :=
  [(.first, [.resume (.second 0)]), (.second 7, []), (.first, [.resume (.second 0)])]

private def ownedReturnContext (branch : Nat) : Context Unit Unit Nat Unit Unit Unit :=
  ⟨(CoreWorld.fork { demoWorld with nextEvaluator := 1 } branch).setKnownCache
      demoCell ⟨(), .suspended⟩ (.evaluating 0), {}⟩

private def committedReturnContext (branch value : Nat) : Context Unit Unit Nat Unit Unit Unit :=
  (resume demoSpec (ownedReturnContext branch) (.commit demoCell 0) (.value value)).1

/-- Delivery keeps each site's captured token and complete pending return stack. -/
example :
    (returnCohort demoSpec (committedReturnContext 0 21) (.value 21) cohortSites).map
      (fun task => (task.control, task.returns)) =
    [(.run (.again 21), [.resume (.second 0)]), (.run (.total 28), []),
      (.run (.again 21), [.resume (.second 0)])] := rfl

/-- Equal sites remain two occurrences; their equality does not authorize deduplication. -/
example :
    (returnCohort demoSpec (committedReturnContext 0 21) (.value 21) cohortSites).length = 3 := rfl

/-- Both branches name the same cell. Their selected cache values and paths stay distinct. -/
example :
    (returnCohort demoSpec (committedReturnContext 0 21) (.value 21) cohortSites).map
      (fun task => (task.context.world.path, task.context.world.heap.lookup demoCell)) =
      [([0], some ⟨(), .value 21⟩), ([0], some ⟨(), .value 21⟩),
        ([0], some ⟨(), .value 21⟩)] ∧
    (returnCohort demoSpec (committedReturnContext 1 28) (.value 28) cohortSites).map
      (fun task => (task.context.world.path, task.context.world.heap.lookup demoCell)) =
      [([1], some ⟨(), .value 28⟩), ([1], some ⟨(), .value 28⟩),
        ([1], some ⟨(), .value 28⟩)] := ⟨rfl, rfl⟩

/-- A wrong owner produces a retryable outcome. Delivering that outcome propagates it. -/
example :
    (resume demoSpec (ownedReturnContext 0) (.commit demoCell 1) (.value 21)).2 =
      .returned (.retryableFault (.ownershipLost demoCell 1 0)) := rfl

example :
    (returnCohort demoSpec
      (resume demoSpec (ownedReturnContext 0) (.commit demoCell 1) (.value 21)).1
      (.retryableFault (.ownershipLost demoCell 1 0)) cohortSites).map (·.control) =
      [.run (.propagate (.retryableFault (.ownershipLost demoCell 1 0))),
        .run (.propagate (.retryableFault (.ownershipLost demoCell 1 0))),
        .run (.propagate (.retryableFault (.ownershipLost demoCell 1 0)))] := rfl

/-- A failed ownership check leaves the evaluating cache in its original world. -/
example :
    (resume demoSpec (ownedReturnContext 0) (.commit demoCell 1) (.value 21)).1.world.heap.lookup
      demoCell = some ⟨(), .evaluating 0⟩ := rfl


/-! ### Lock-step is impossible with a world-independent control -/

/-- The same force control in two worlds: a cached cell and a claimable one. -/
def cachedForce : CoreMachine Unit Code Token Unit Nat Unit Unit Unit :=
  ⟨{ demoWorld with
      heap := demoWorld.heap.setKnownCache demoCell ⟨(), .suspended⟩ (.value 21) },
    .force demoCell [], {}⟩

def claimingForce : CoreMachine Unit Code Token Unit Nat Unit Unit Unit :=
  ⟨demoWorld, .force demoCell [], {}⟩

/-- The stack of a need control; a halted machine has none. -/
def stackOf : Control Code Token Nat Unit Unit → List (Frame Token)
  | .force _ stack => stack
  | .run _ stack => stack
  | .returned _ stack => stack
  | .halted _ => []

theorem force_frames_depend_on_world :
    (NeedExecution.step demoSpec cachedForce).map (fun machine => stackOf machine.control) =
        [[]] ∧
      (NeedExecution.step demoSpec claimingForce).map
          (fun machine => stackOf machine.control) =
        [[.commit demoCell 0]] :=
  ⟨rfl, rfl⟩

/-- No shared program takes both force transitions in one step each while
keeping the need stack as its return list and encoding the common control
`force demoCell []` by one control, whatever the contexts. -/
theorem no_lockstep_force {Ctx Ctl Callee Ans : Type}
    (P : Program Ctx Ctl Callee (Frame Token) Ans) (control : Ctl) (cached claiming : Ctx) :
    ¬ ((SharedContinuation.step P ⟨[⟨cached, control, []⟩], []⟩).frontier.map
            (·.returns) =
          (NeedExecution.step demoSpec cachedForce).map
            (fun machine => stackOf machine.control) ∧
        (SharedContinuation.step P ⟨[⟨claiming, control, []⟩], []⟩).frontier.map
            (·.returns) =
          (NeedExecution.step demoSpec claimingForce).map
            (fun machine => stackOf machine.control)) := by
  rw [force_frames_depend_on_world.1, force_frames_depend_on_world.2]
  rintro ⟨hCached, hClaiming⟩
  have leftMember : ([] : List (Frame Token)) ∈
      (SharedContinuation.step P ⟨[⟨cached, control, []⟩], []⟩).frontier.map
        (·.returns) := by
    rw [hCached]
    simp
  have rightMember : [Frame.commit demoCell 0] ∈
      (SharedContinuation.step P ⟨[⟨claiming, control, []⟩], []⟩).frontier.map
        (·.returns) := by
    rw [hClaiming]
    simp
  obtain ⟨left, hLeft, hLeftReturns⟩ := List.mem_map.mp leftMember
  obtain ⟨right, hRight, hRightReturns⟩ := List.mem_map.mp rightMember
  have same := step_returns_context_free P cached claiming control [] left hLeft right hRight
  rw [hLeftReturns, hRightReturns] at same
  exact List.cons_ne_nil _ _ same.symm

end Demo

end Mettapedia.Machines.BranchLocalNeed.NeedContinuation
