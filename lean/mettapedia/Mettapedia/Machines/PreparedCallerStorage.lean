import Mettapedia.Machines.SharedContinuation

/-!
# Separating caller metadata from captured data

The source stores each caller's plan and payload together. The target keeps
two immutable arenas and checks their parent links before executing a return.
Its execution reads only the selected node; it does not expand the suffix.
Both machines use the existing shared-continuation instruction semantics.

The splitting theorem covers every instruction, including refused addresses,
and arbitrary bounded execution. Metadata interning, native pointer movement,
capture-port installation and source-plan admission are further obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedCallerStorage

open SharedContinuation

variable {Plan Payload Context Control Call Answer : Type}

def projectArena {Frame Image : Type} (f : Frame → Image) (arena : Arena Frame) : Arena Image :=
  arena.map fun node => (f node.1, node.2)

theorem project_read {Frame Image : Type} (f : Frame → Image) (arena : Arena Frame) (root : Nat) :
    (projectArena f arena).read root = (arena.read root).map (fun node => (f node.1, node.2)) := by
  induction arena with
  | nil => rfl
  | cons node older ih =>
      simp only [projectArena, List.map_cons, Arena.read, List.length_map]
      split <;> simp_all [projectArena]

structure SplitState (Context Control Plan Payload Answer : Type) where
  plans : Arena Plan
  payloads : Arena Payload
  frontier : List (RootTask Context Control)
  emitted : List (Context × Answer)

def split (state : ArenaState Context Control (Plan × Payload) Answer) :
    SplitState Context Control Plan Payload Answer :=
  ⟨projectArena Prod.fst state.arena, projectArena Prod.snd state.arena,
    state.frontier, state.emitted⟩

/-- Each lookup is independent. Disagreeing parents refuse the representation
instead of silently choosing one arena's continuation. -/
def readCaller (plans : Arena Plan) (payloads : Arena Payload) (root : Nat) :
    Option ((Plan × Payload) × Nat) := do
  let (plan, planParent) ← plans.read root
  let (payload, payloadParent) ← payloads.read root
  if planParent = payloadParent then some ((plan, payload), payloadParent) else none

theorem read_split (arena : Arena (Plan × Payload)) (root : Nat) :
    readCaller (projectArena Prod.fst arena) (projectArena Prod.snd arena) root =
      arena.read root := by
  simp only [readCaller, project_read]
  cases arena.read root with
  | none => rfl
  | some node => rcases node with ⟨⟨plan, payload⟩, parent⟩; simp

def targetStep (program : Program Context Control Call (Plan × Payload) Answer)
    (state : SplitState Context Control Plan Payload Answer) :
    Option (SplitState Context Control Plan Payload Answer) :=
  match state.frontier with
  | [] => some state
  | task :: rest =>
      match program.inspect task.control with
      | .ret value =>
          if task.root = 0 then
            some {state with frontier := rest, emitted := state.emitted ++ [(task.context, value)]}
          else (readCaller state.plans state.payloads task.root).map fun (frame, parent) =>
            let next := program.resume task.context frame value
            {state with frontier := ⟨next.1, next.2, parent⟩ :: rest}
      | .fail => some {state with frontier := rest}
      | .call callee frame =>
          some {state with
            plans := (frame.1, task.root) :: state.plans
            payloads := (frame.2, task.root) :: state.payloads
            frontier := (program.branches task.context callee).map (fun next =>
              ⟨next.1, next.2, state.payloads.length + 1⟩) ++ rest}
      | .tail callee =>
          some {state with frontier := (program.branches task.context callee).map (fun next =>
            ⟨next.1, next.2, task.root⟩) ++ rest}

/-- Separate lookups and separate node allocation implement the combined
machine step. Invalid selected addresses have exactly the same refusal. -/
theorem step_split_exact (program : Program Context Control Call (Plan × Payload) Answer)
    (state : ArenaState Context Control (Plan × Payload) Answer) :
    targetStep program (split state) = (arenaStep program state).map split := by
  rcases state with ⟨arena, frontier, emitted⟩
  cases frontier with
  | nil => rfl
  | cons task rest =>
      cases instruction : program.inspect task.control with
      | ret value =>
          by_cases empty : task.root = 0
          · simp [targetStep, split, arenaStep, instruction, empty]
          · simp only [targetStep, split, arenaStep, instruction, empty, ↓reduceIte, read_split]
            cases arena.read task.root <;> rfl
      | fail => simp [targetStep, split, arenaStep, instruction]
      | call callee frame =>
          simp [targetStep, split, arenaStep, instruction, projectArena]
      | tail callee => simp [targetStep, split, arenaStep, instruction]

def sourceRun (program : Program Context Control Call (Plan × Payload) Answer) :
    Nat → ArenaState Context Control (Plan × Payload) Answer →
      Option (ArenaState Context Control (Plan × Payload) Answer)
  | 0, state => some state
  | n + 1, state => (arenaStep program state).bind (sourceRun program n)

def targetRun (program : Program Context Control Call (Plan × Payload) Answer) :
    Nat → SplitState Context Control Plan Payload Answer →
      Option (SplitState Context Control Plan Payload Answer)
  | 0, state => some state
  | n + 1, state => (targetStep program state).bind (targetRun program n)

/-- No allowance requires suffix expansion. Published events, branch contexts
and the remaining frontier agree after any finite number of steps. -/
theorem run_split_exact (program : Program Context Control Call (Plan × Payload) Answer)
    (allowance : Nat) (state : ArenaState Context Control (Plan × Payload) Answer) :
    targetRun program allowance (split state) = (sourceRun program allowance state).map split := by
  induction allowance generalizing state with
  | zero => rfl
  | succ allowance ih =>
      simp only [targetRun, sourceRun, step_split_exact]
      cases arenaStep program state with
      | none => rfl
      | some next => simpa using ih next

theorem read_disagreeing_parents (plans : Arena Plan) (payloads : Arena Payload)
    (root planParent payloadParent : Nat) (plan : Plan) (payload : Payload)
    (foundPlan : plans.read root = some (plan, planParent))
    (foundPayload : payloads.read root = some (payload, payloadParent))
    (different : planParent ≠ payloadParent) : readCaller plans payloads root = none := by
  simp [readCaller, foundPlan, foundPayload, different]

section ExistingOwnership

variable {Frame : Type}

/-- The copying alternative rebuilds the selected return stack, even though
its nodes are already present in this arena. Older pending roots are kept. -/
def resaveHead (state : ArenaState Context Control Frame Answer) :
    ArenaState Context Control Frame Answer :=
  match state.frontier with
  | [] => state
  | task :: rest =>
      let saved := state.arena.save (state.arena.expand task.root)
      ⟨saved.1, {task with root := saved.2} :: rest, state.emitted⟩

theorem resaveHead_exact (state : ArenaState Context Control Frame Answer) (valid : state.Valid) :
    (resaveHead state).Valid ∧ (resaveHead state).decode = state.decode ∧
      (resaveHead state).arena.length = state.arena.length + state.decode.headReturnDepth := by
  rcases state with ⟨arena, frontier, emitted⟩
  rcases valid with ⟨arenaValid, bounded⟩
  cases frontier with
  | nil => simp [resaveHead, ArenaState.Valid, arenaValid, ArenaState.decode, State.headReturnDepth]
  | cons task rest =>
      obtain ⟨savedValid, savedBound, savedExact, savedLength, old⟩ :=
        arena.save_spec arenaValid (arena.expand task.root)
      have restExact : rest.map (RootTask.decode (arena.save (arena.expand task.root)).1) =
          rest.map (RootTask.decode arena) := by
        apply List.map_congr_left
        intro other member
        simp only [RootTask.decode, old other.root (bounded other (by simp [member]))]
      refine ⟨⟨savedValid, ?_⟩, ?_, ?_⟩
      · intro other member
        simp only [resaveHead, List.mem_cons] at member
        rcases member with rfl | member
        · exact savedBound
        · have bound := bounded other (by simp [member])
          change other.root ≤ arena.length at bound
          simp only [resaveHead]
          omega
      · simp [resaveHead, ArenaState.decode, RootTask.decode, savedExact, restExact]
      · simpa [resaveHead, ArenaState.decode, State.headReturnDepth, RootTask.decode] using savedLength

/-- Keeping an already owned root has the same bounded execution as copying
its stack again. The latter's added node count is given by resaveHead_exact.
Native detachment and reset-mark validity must justify that the root is owned. -/
theorem reuse_owned_root_slice_exact (program : Program Context Control Call Frame Answer)
    (state : CheckedState Context Control Frame Answer) (allowance : Nat) :
    ((MachineCore.runSlice (sharedCore program) allowance
        ⟨resaveHead state.1, (resaveHead_exact state.1 state.2).1⟩).1.1.decode,
      (MachineCore.runSlice (sharedCore program) allowance
        ⟨resaveHead state.1, (resaveHead_exact state.1 state.2).1⟩).2) =
      ((MachineCore.runSlice (sharedCore program) allowance state).1.1.decode,
        (MachineCore.runSlice (sharedCore program) allowance state).2) := by
  rw [slice_exact, slice_exact, (resaveHead_exact state.1 state.2).2.1]

end ExistingOwnership

namespace Examples

def program : Program Unit Nat Unit (Nat × Nat) Nat where
  inspect := Instruction.ret
  branches := fun _ _ => []
  resume := fun context frame value => (context, frame.1 * value + frame.2)

def source : ArenaState Unit Nat (Nat × Nat) Nat :=
  ⟨[((2, 3), 0)], [⟨(), 5, 1⟩, ⟨(), 7, 1⟩], []⟩

theorem shared_callers_keep_both_answers :
    (targetRun program 4 (split source)).map SplitState.emitted =
      some [((), 13), ((), 17)] := by decide +kernel

/-- A wrong plan can have a valid shape and still change the computation. -/
theorem wrong_plan_is_observable :
    (targetRun program 4 {split source with plans := [(9, 0)]}).map SplitState.emitted ≠
      (targetRun program 4 (split source)).map SplitState.emitted := by decide +kernel

theorem mismatched_parent_is_refused :
    readCaller ([(2, 0)] : Arena Nat) ([(3, 1)] : Arena Nat) 1 = none := by decide +kernel

end Examples
end Mettapedia.Machines.PreparedCallerStorage
