import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Shared return continuations with branch-local contexts

A return continuation and a search alternative have different roles. A return
resumes a caller on each callee answer; an alternative retains a branch's own
context. This machine keeps both, including after an answer has been published.

The reference carries lists of return frames. The second representation stores
immutable frames once in a topologically ordered arena and puts roots on the
frontier. Its step function follows a root without expanding the saved stack.
Decoding is reserved for observation and representation transfer.

The list presentation of the arena specifies stable natural-number addresses;
it does not claim constant-time lookup. A native array is a further realization.
Contexts may contain store images, snapshots and ownership handles. Their native
validity and the semantics of `branches` and `resume` remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SharedContinuation

variable {Frame : Type}

/-- Newest node first. Root zero is the empty continuation; a newly allocated
node has address `older.length + 1`. Nodes only refer to older nodes. -/
abbrev Arena (Frame : Type) := List (Frame × Nat)

def Arena.Valid : Arena Frame → Prop
  | [] => True
  | (_, parent) :: older => Arena.Valid older ∧ parent ≤ older.length

def Arena.read : Arena Frame → Nat → Option (Frame × Nat)
  | [], _ => none
  | node :: older, root =>
      if root = older.length + 1 then some node else Arena.read older root

def Arena.expand : Arena Frame → Nat → List Frame
  | [], _ => []
  | (frame, parent) :: older, root =>
      if root = older.length + 1 then frame :: Arena.expand older parent
      else Arena.expand older root

@[simp] theorem Arena.read_zero (arena : Arena Frame) : arena.read 0 = none := by
  induction arena with
  | nil => rfl
  | cons node older ih => simp [read, ih]

@[simp] theorem Arena.expand_zero (arena : Arena Frame) : arena.expand 0 = [] := by
  induction arena with
  | nil => rfl
  | cons node older ih => simp [expand, ih]

theorem Arena.read_old (arena : Arena Frame) (frame : Frame) (parent root : Nat)
    (old : root ≤ arena.length) :
    Arena.read ((frame, parent) :: arena) root = arena.read root := by
  simp [read, show root ≠ arena.length + 1 by omega]

theorem Arena.expand_old (arena : Arena Frame) (frame : Frame) (parent root : Nat)
    (old : root ≤ arena.length) :
    Arena.expand ((frame, parent) :: arena) root = arena.expand root := by
  simp [expand, show root ≠ arena.length + 1 by omega]

theorem Arena.read_bounds (arena : Arena Frame) (valid : arena.Valid)
    {root parent : Nat} {frame : Frame} (found : arena.read root = some (frame, parent)) :
    0 < root ∧ root ≤ arena.length ∧ parent < root := by
  induction arena with
  | nil => simp [read] at found
  | cons node older ih =>
      rcases node with ⟨head, previous⟩
      rcases valid with ⟨valid, bound⟩
      by_cases atHead : root = older.length + 1
      · simp [read, atHead] at found
        rcases found with ⟨rfl, rfl⟩
        simp only [List.length_cons]
        omega
      · have foundOld : Arena.read older root = some (frame, parent) := by
          simpa [read, atHead] using found
        have := ih valid foundOld
        simp only [List.length_cons]
        omega

theorem Arena.read_exists (arena : Arena Frame) {root : Nat}
    (positive : 0 < root) (bound : root ≤ arena.length) :
    ∃ frame parent, arena.read root = some (frame, parent) := by
  induction arena with
  | nil => simp at bound; omega
  | cons node older ih =>
      by_cases atHead : root = older.length + 1
      · exact ⟨node.1, node.2, by simp [read, atHead]⟩
      · have := ih (by simp only [List.length_cons] at bound; omega)
        simpa [read, atHead] using this

theorem Arena.expand_read (arena : Arena Frame) (valid : arena.Valid)
    {root parent : Nat} {frame : Frame} (found : arena.read root = some (frame, parent)) :
    arena.expand root = frame :: arena.expand parent := by
  induction arena with
  | nil => simp [read] at found
  | cons node older ih =>
      rcases node with ⟨head, previous⟩
      rcases valid with ⟨valid, bound⟩
      by_cases atHead : root = older.length + 1
      · have same : head = frame ∧ previous = parent := by
          simpa [read, atHead] using found
        rcases same with ⟨rfl, rfl⟩
        rw [expand_old older head previous previous bound]
        simp [expand, atHead]
      · have foundOld : Arena.read older root = some (frame, parent) := by
          simpa [read, atHead] using found
        have bounds := read_bounds older valid foundOld
        rw [expand_old older head previous parent (by omega)]
        simpa [expand, atHead] using ih valid foundOld

/-- Reify a return stack into fresh nodes. This is a boundary conversion,
not an operation performed at each native step. -/
def Arena.save (arena : Arena Frame) : List Frame → Arena Frame × Nat
  | [] => (arena, 0)
  | frame :: rest =>
      let saved := arena.save rest
      ((frame, saved.2) :: saved.1, saved.1.length + 1)

theorem Arena.save_spec (arena : Arena Frame) (valid : arena.Valid) (frames : List Frame) :
    (arena.save frames).1.Valid ∧
    (arena.save frames).2 ≤ (arena.save frames).1.length ∧
    (arena.save frames).1.expand (arena.save frames).2 = frames ∧
    (arena.save frames).1.length = arena.length + frames.length ∧
    (∀ root, root ≤ arena.length →
      (arena.save frames).1.expand root = arena.expand root) := by
  induction frames with
  | nil => simp [save, valid]
  | cons frame rest ih =>
      rcases ih with ⟨hv, hb, he, hl, ho⟩
      simp only [save, List.length_cons]
      refine ⟨⟨hv, hb⟩, le_rfl, ?_, by omega, ?_⟩
      · simp [expand, he]
      · intro root bound
        rw [expand_old _ frame _ root (by omega)]
        exact ho root bound

theorem Arena.valid_drop (arena : Arena Frame) (valid : arena.Valid) (count : Nat) :
    Arena.Valid (arena.drop count) := by
  induction count generalizing arena with
  | zero => exact valid
  | succ count ih =>
      cases arena with
      | nil => trivial
      | cons node older => exact ih older valid.1

/-- A root below a region mark can only reach nodes below that mark. -/
theorem Arena.expand_drop (arena : Arena Frame) (count root : Nat)
    (bound : root ≤ (arena.drop count).length) :
    Arena.expand (arena.drop count) root = arena.expand root := by
  induction count generalizing arena with
  | zero => rfl
  | succ count ih =>
      cases arena with
      | nil => rfl
      | cons node older =>
          rcases node with ⟨frame, parent⟩
          have smaller : root ≤ older.length := by
            have reduced : root ≤ older.length - count := by
              simpa only [List.drop_succ_cons, List.length_drop] using bound
            exact reduced.trans (Nat.sub_le older.length count)
          rw [expand_old older frame parent root smaller]
          exact ih older bound

variable {Context Control Call Answer : Type}

/-- One semantic control boundary. A return is not a published answer until
the return stack is empty. Failure is only exhaustion of this alternative. -/
inductive Instruction (Call Frame Answer : Type) where
  | ret (value : Answer)
  | fail
  | call (callee : Call) (returnFrame : Frame)
  | tail (callee : Call)

/-- The same operational fragment is executed in both representations.
Context updates occur through these operations, never through an arena node. -/
structure Program (Context Control Call Frame Answer : Type) where
  inspect : Control → Instruction Call Frame Answer
  branches : Context → Call → List (Context × Control)
  resume : Context → Frame → Answer → Context × Control

structure Task (Context Control Frame : Type) where
  context : Context
  control : Control
  returns : List Frame

structure State (Context Control Frame Answer : Type) where
  frontier : List (Task Context Control Frame)
  emitted : List (Context × Answer)

def step (program : Program Context Control Call Frame Answer)
    (state : State Context Control Frame Answer) : State Context Control Frame Answer :=
  match state.frontier with
  | [] => state
  | task :: rest =>
      match program.inspect task.control with
      | .ret value =>
          match task.returns with
          | [] => ⟨rest, state.emitted ++ [(task.context, value)]⟩
          | frame :: pending =>
              let next := program.resume task.context frame value
              ⟨⟨next.1, next.2, pending⟩ :: rest, state.emitted⟩
      | .fail => ⟨rest, state.emitted⟩
      | .call callee frame =>
          ⟨(program.branches task.context callee).map (fun next =>
            ⟨next.1, next.2, frame :: task.returns⟩) ++ rest, state.emitted⟩
      | .tail callee =>
          ⟨(program.branches task.context callee).map (fun next =>
            ⟨next.1, next.2, task.returns⟩) ++ rest, state.emitted⟩

structure RootTask (Context Control : Type) where
  context : Context
  control : Control
  root : Nat

structure ArenaState (Context Control Frame Answer : Type) where
  arena : Arena Frame
  frontier : List (RootTask Context Control)
  emitted : List (Context × Answer)

def ArenaState.Valid (state : ArenaState Context Control Frame Answer) : Prop :=
  state.arena.Valid ∧ ∀ task ∈ state.frontier, task.root ≤ state.arena.length

def RootTask.decode (arena : Arena Frame) (task : RootTask Context Control) :
    Task Context Control Frame := ⟨task.context, task.control, arena.expand task.root⟩

def ArenaState.decode (state : ArenaState Context Control Frame Answer) :
    State Context Control Frame Answer :=
  ⟨state.frontier.map (RootTask.decode state.arena), state.emitted⟩

/-- Invalid addresses refuse execution (`none`); they are not interpreted as
logical failure or an empty answer collection. Well-formed states never refuse. -/
def arenaStep (program : Program Context Control Call Frame Answer)
    (state : ArenaState Context Control Frame Answer) :
    Option (ArenaState Context Control Frame Answer) :=
  match state.frontier with
  | [] => some state
  | task :: rest =>
      match program.inspect task.control with
      | .ret value =>
          if task.root = 0 then
            some ⟨state.arena, rest, state.emitted ++ [(task.context, value)]⟩
          else (state.arena.read task.root).map fun (frame, parent) =>
            let next := program.resume task.context frame value
            ⟨state.arena, ⟨next.1, next.2, parent⟩ :: rest, state.emitted⟩
      | .fail => some ⟨state.arena, rest, state.emitted⟩
      | .call callee frame =>
          some ⟨(frame, task.root) :: state.arena,
            (program.branches task.context callee).map (fun next =>
              ⟨next.1, next.2, state.arena.length + 1⟩) ++ rest, state.emitted⟩
      | .tail callee =>
          some ⟨state.arena, (program.branches task.context callee).map (fun next =>
            ⟨next.1, next.2, task.root⟩) ++ rest, state.emitted⟩

theorem decode_old_frontier (arena : Arena Frame) (frame : Frame) (parent : Nat)
    (frontier : List (RootTask Context Control))
    (bounded : ∀ task ∈ frontier, task.root ≤ arena.length) :
    frontier.map (RootTask.decode ((frame, parent) :: arena)) =
      frontier.map (RootTask.decode arena) := by
  apply List.map_congr_left
  intro task member
  simp only [RootTask.decode, Arena.expand_old arena frame parent task.root (bounded task member)]

/-- An arena step exists, retains well-formed roots and decodes to exactly one
reference step. This proves both preservation and no invention of behavior. -/
theorem arenaStep_exact (program : Program Context Control Call Frame Answer)
    (state : ArenaState Context Control Frame Answer) (valid : state.Valid) :
    ∃ next, arenaStep program state = some next ∧ next.Valid ∧
      next.decode = step program state.decode := by
  rcases state with ⟨arena, frontier, emitted⟩
  rcases valid with ⟨validArena, bounded⟩
  cases frontier with
  | nil => exact ⟨_, rfl, ⟨validArena, bounded⟩, rfl⟩
  | cons task rest =>
      have rootBound := bounded task (by simp)
      have restBound : ∀ task ∈ rest, task.root ≤ arena.length :=
        fun other member => bounded other (by simp [member])
      cases instruction : program.inspect task.control with
      | ret value =>
          by_cases empty : task.root = 0
          · refine ⟨⟨arena, rest, emitted ++ [(task.context, value)]⟩,
              by simp [arenaStep, instruction, empty],
              ⟨validArena, restBound⟩, ?_⟩
            simp [step, ArenaState.decode, RootTask.decode, instruction, empty]
          · obtain ⟨frame, parent, found⟩ := arena.read_exists (by omega) rootBound
            have bounds := arena.read_bounds validArena found
            refine ⟨⟨arena, ⟨(program.resume task.context frame value).1,
              (program.resume task.context frame value).2, parent⟩ :: rest, emitted⟩,
              by simp [arenaStep, instruction, empty, found], ?_, ?_⟩
            · refine ⟨validArena, ?_⟩
              intro other member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · dsimp; omega
              · exact restBound other member
            · simp [step, ArenaState.decode, RootTask.decode, instruction,
                arena.expand_read validArena found]
      | fail =>
          exact ⟨⟨arena, rest, emitted⟩, by simp [arenaStep, instruction], ⟨validArena, restBound⟩,
            by simp [step, ArenaState.decode, RootTask.decode, instruction]⟩
      | call callee frame =>
          refine ⟨⟨(frame, task.root) :: arena,
            (program.branches task.context callee).map (fun next =>
              ⟨next.1, next.2, arena.length + 1⟩) ++ rest, emitted⟩,
            by simp [arenaStep, instruction], ?_, ?_⟩
          · refine ⟨⟨validArena, rootBound⟩, ?_⟩
            intro other member
            simp only [List.mem_append, List.mem_map] at member
            rcases member with ⟨next, _, rfl⟩ | member
            · simp
            · have := restBound other member
              simp only [List.length_cons]; omega
          · simp only [ArenaState.decode, List.map_append]
            rw [decode_old_frontier arena frame task.root rest restBound]
            simp [step, RootTask.decode, instruction, Arena.expand, List.map_map]
      | tail callee =>
          refine ⟨⟨arena, (program.branches task.context callee).map (fun next =>
            ⟨next.1, next.2, task.root⟩) ++ rest, emitted⟩,
            by simp [arenaStep, instruction], ?_, ?_⟩
          · refine ⟨validArena, ?_⟩
            intro other member
            simp only [List.mem_append, List.mem_map] at member
            rcases member with ⟨next, _, rfl⟩ | member
            · exact rootBound
            · exact restBound other member
          · simp [step, ArenaState.decode, RootTask.decode, instruction, List.map_map]

/-- The checked carrier is for already admitted native states. An untrusted
root still goes through the explicit refusal result of `arenaStep`. -/
abbrev CheckedState (Context Control Frame Answer : Type) :=
  { state : ArenaState Context Control Frame Answer // state.Valid }

def checkedStep (program : Program Context Control Call Frame Answer)
    (state : CheckedState Context Control Frame Answer) :
    CheckedState Context Control Frame Answer :=
  let proof := arenaStep_exact program state.1 state.2
  let next := (arenaStep program state.1).get (by
    obtain ⟨next, found, _, _⟩ := proof
    simp [found])
  ⟨next, by
    dsimp only [next]
    obtain ⟨next, found, valid, _⟩ := proof
    simpa only [found, Option.get_some] using valid⟩

theorem decode_checkedStep (program : Program Context Control Call Frame Answer)
    (state : CheckedState Context Control Frame Answer) :
    (checkedStep program state).1.decode = step program state.1.decode := by
  obtain ⟨next, found, _, exactStep⟩ := arenaStep_exact program state.1 state.2
  simpa [checkedStep, found] using exactStep

/-- Import an arbitrary suspended reference frontier, including pending
returns. Already imported roots remain valid when subsequent nodes are added. -/
def saveFrontier (arena : Arena Frame) : List (Task Context Control Frame) →
    Arena Frame × List (RootTask Context Control)
  | [] => (arena, [])
  | task :: rest =>
      let saved := arena.save task.returns
      let later := saveFrontier saved.1 rest
      (later.1, ⟨task.context, task.control, saved.2⟩ :: later.2)

theorem saveFrontier_spec (arena : Arena Frame) (valid : arena.Valid)
    (frontier : List (Task Context Control Frame)) :
    (saveFrontier arena frontier).1.Valid ∧
    (∀ task ∈ (saveFrontier arena frontier).2,
      task.root ≤ (saveFrontier arena frontier).1.length) ∧
    (saveFrontier arena frontier).2.map
      (RootTask.decode (saveFrontier arena frontier).1) = frontier ∧
    arena.length ≤ (saveFrontier arena frontier).1.length ∧
    (∀ root, root ≤ arena.length →
      (saveFrontier arena frontier).1.expand root = arena.expand root) := by
  induction frontier generalizing arena with
  | nil => simp [saveFrontier, valid]
  | cons task rest ih =>
      obtain ⟨savedValid, savedBound, savedExact, savedLength, savedOld⟩ :=
        arena.save_spec valid task.returns
      obtain ⟨laterValid, laterBound, laterExact, laterLength, laterOld⟩ :=
        ih (arena.save task.returns).1 savedValid
      simp only [saveFrontier, List.map_cons]
      refine ⟨laterValid, ?_, ?_, by omega, ?_⟩
      · intro other member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · dsimp; omega
        · exact laterBound other member
      · rw [laterExact]
        simp only [RootTask.decode, laterOld _ savedBound, savedExact]
      · intro root bound
        rw [laterOld root (by omega), savedOld root bound]

def encode (state : State Context Control Frame Answer) :
    CheckedState Context Control Frame Answer :=
  let saved := saveFrontier [] state.frontier
  ⟨⟨saved.1, saved.2, state.emitted⟩,
    (saveFrontier_spec [] (by trivial) state.frontier).1,
    (saveFrontier_spec [] (by trivial) state.frontier).2.1⟩

@[simp] theorem decode_encode (state : State Context Control Frame Answer) :
    (encode state).1.decode = state := by
  have exactFrontier := (saveFrontier_spec [] (by trivial) state.frontier).2.2.1
  dsimp only [encode, ArenaState.decode]
  rw [exactFrontier]

/-- An ordered branching call allocates one return node, independently of
the number of callee alternatives and the caller's existing return depth. -/
theorem call_allocates_one (program : Program Context Control Call Frame Answer)
    (arena : Arena Frame) (task : RootTask Context Control)
    (rest : List (RootTask Context Control)) (emitted : List (Context × Answer))
    (callee : Call) (frame : Frame) (instruction : program.inspect task.control = .call callee frame) :
    (arenaStep program ⟨arena, task :: rest, emitted⟩).map (fun next => next.arena.length) =
      some (arena.length + 1) := by
  simp [arenaStep, instruction]

/-- Retire the newest region only when every frontier root and every externally
held root lies below its mark. The native capture inventory must include roots
held by exported closures or other owners; omitting such roots is not licensed.
Frame addresses below the mark do not change. -/
def retire? (count : Nat) (held : List Nat)
    (state : ArenaState Context Control Frame Answer) :
    Option (ArenaState Context Control Frame Answer) :=
  let kept := state.arena.drop count
  if state.frontier.all (fun task => decide (task.root ≤ kept.length)) &&
      held.all (fun root => decide (root ≤ kept.length)) then
    some { state with arena := kept }
  else none

/-- Checked retirement preserves the complete residual and every declared
external continuation, and keeps the arena well formed. -/
theorem retire?_exact (count : Nat) (held : List Nat)
    (state next : ArenaState Context Control Frame Answer) (valid : state.Valid)
    (retired : retire? count held state = some next) :
    next.Valid ∧ next.decode = state.decode ∧
      (∀ root ∈ held, next.arena.expand root = state.arena.expand root) ∧
      next.arena.length = state.arena.length - count := by
  unfold retire? at retired
  dsimp only at retired
  split at retired
  next admitted =>
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at admitted
    obtain ⟨frontierBound, heldBound⟩ := admitted
    cases Option.some.inj retired
    refine ⟨⟨state.arena.valid_drop valid.1 count, frontierBound⟩, ?_, ?_, ?_⟩
    · apply congrArg (fun frontier => State.mk frontier state.emitted)
      apply List.map_congr_left
      intro task member
      simp only [RootTask.decode, Arena.expand_drop _ count _ (frontierBound task member)]
    · intro root member
      exact state.arena.expand_drop count root (heldBound root member)
    · exact List.length_drop
  next refused => simp at retired

end Mettapedia.Machines.SharedContinuation
