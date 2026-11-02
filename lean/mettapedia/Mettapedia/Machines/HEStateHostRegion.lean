import Mettapedia.Machines.DeterministicRegion

/-!
# Ready HE State operations at a native host boundary

The world contains stable State identities and immutable syntax payload values.
Allocation stores syntax without interpreting it; a ready scalar write mutates
one existing identity and returns that same handle. Reads return a snapshot of
that operation's current payload. The queued and direct interpreters have
independent administrative control and share only these primitive meanings.

This models ready operations, not native C admission or arbitrary operand
computation. In particular, a returned syntax payload can be interpreted again
by an HE consumer; no theorem here erases that readback. The first native lane
admits writes and leaves generic reads canonical. Typed publication, resource
root discovery, image ownership/collection, concurrency, allocation failure,
source authority and C correspondence remain separate native obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HEStateHostRegion

open DeterministicRegion

inductive Syntax where
  | literal (value : Nat)
  | add (left right : Syntax)
  | fault
  deriving DecidableEq, Repr

inductive Value where
  | payload (payload : Syntax)
  | reference (identity : Nat)
  deriving DecidableEq, Repr

structure World where
  next : Nat
  cells : Nat → Option Syntax
  writes : Nat

inductive Event where
  | allocated (identity : Nat) (payload : Syntax)
  | read (identity : Nat) (payload : Syntax)
  | written (identity : Nat) (value : Nat)
  deriving DecidableEq, Repr

inductive Operation where
  | allocate (payload : Syntax)
  | read (referenceSlot : Nat)
  | write (referenceSlot value : Nat)
  | raiseFault
  | unavailable
  deriving DecidableEq, Repr

inductive Ready where
  | allocate (payload : Syntax)
  | read (identity : Nat)
  | write (identity value : Nat)
  | raiseFault
  deriving DecidableEq, Repr

def meaning : Semantics Operation Ready Value World Event Nat where
  prepare operation registers := match operation with
    | .allocate payload => some (.allocate payload)
    | .read slot => match registers slot with
      | some (.reference identity) => some (.read identity)
      | _ => none
    | .write slot value => match registers slot with
      | some (.reference identity) => some (.write identity value)
      | _ => none
    | .raiseFault => some .raiseFault
    | .unavailable => none
  invoke ready world := match ready with
    | .allocate payload =>
        ⟨⟨world.next + 1, Function.update world.cells world.next (some payload),
            world.writes⟩,
          [.allocated world.next payload], .value (.reference world.next)⟩
    | .read identity => match world.cells identity with
      | none => ⟨world, [], .raised 1⟩
      | some payload => ⟨world, [.read identity payload], .value (.payload payload)⟩
    | .write identity value => match world.cells identity with
      | none => ⟨world, [], .raised 1⟩
      | some _ =>
          ⟨⟨world.next, Function.update world.cells identity
                (some (.literal value)), world.writes + 1⟩,
            [.written identity value], .value (.reference identity)⟩
    | .raiseFault => ⟨world, [], .raised 7⟩

def initial : State Value World Event :=
  ⟨fun _ => none, ⟨0, fun _ => none, 0⟩, []⟩

def instruction (destination : Nat) (operation : Operation) : Instruction Operation :=
  ⟨destination, operation⟩

/-- Arbitrary ready sequences retain the complete world and ordered effects. -/
theorem region_behavior (code : List (Instruction Operation))
    (state : State Value World Event) :
    behavior (queued meaning (schedule code) state) =
      scheduledBehavior (direct meaning code state) :=
  queued_behavior_eq_direct meaning code state

/-- Administrative scheduling never duplicates a native primitive invocation. -/
theorem region_invocations (code : List (Instruction Operation))
    (state : State Value World Event) :
    (queued meaning (schedule code) state).invocations =
      (direct meaning code state).invocations :=
  queued_invocations_eq_direct meaning code state

/-- Every instruction boundary preserves the committed prefix and residual. -/
theorem sliced_region_behavior (limit : Nat) (code : List (Instruction Operation))
    (state : State Value World Event) :
    behavior (queuedSlice meaning limit code state) =
      scheduledBehavior (directSlice meaning limit code state) :=
  sliced_behavior_eq_direct meaning limit code state

theorem ready_write_updates_one_identity (world : World)
    (identity value : Nat) (old : Syntax) (found : world.cells identity = some old) :
    let result := meaning.invoke (.write identity value) world
    result.world.cells identity = some (.literal value) ∧
      result.world.writes = world.writes + 1 ∧
      result.reply = .value (.reference identity) ∧
      result.events = [.written identity value] := by
  simp [meaning, found]

theorem ready_write_preserves_other_cell (world : World)
    (identity other value : Nat) (old : Syntax)
    (found : world.cells identity = some old) (different : other ≠ identity) :
    (meaning.invoke (.write identity value) world).world.cells other =
      world.cells other := by
  simp [meaning, found, different]

theorem ready_read_observes_current_payload (world : World)
    (identity : Nat) (payload : Syntax)
    (found : world.cells identity = some payload) :
    (meaning.invoke (.read identity) world).reply = .value (.payload payload) ∧
      (meaning.invoke (.read identity) world).world = world := by
  simp [meaning, found]

/-- A read before replacement retains its old immutable payload value. -/
theorem old_read_and_current_read :
    let result := direct meaning
      [instruction 0 (.allocate (.literal 7)), instruction 1 (.read 0),
       instruction 2 (.write 0 8), instruction 3 (.read 0)] initial
    result.state.registers 0 = some (.reference 0) ∧
      result.state.registers 1 = some (.payload (.literal 7)) ∧
      result.state.registers 2 = some (.reference 0) ∧
      result.state.registers 3 = some (.payload (.literal 8)) ∧
      result.state.world.cells 0 = some (.literal 8) ∧
      result.state.world.writes = 1 ∧
      result.state.trace = [.allocated 0 (.literal 7), .read 0 (.literal 7),
        .written 0 8, .read 0 (.literal 8)] ∧
      result.invocations = 4 := by
  simp [direct, meaning, initial, instruction, applyEffects, publish, charge]

/-- A writer's returned handle aliases the original State, rather than a copy. -/
theorem returned_handle_aliases :
    let result := direct meaning
      [instruction 0 (.allocate (.literal 7)), instruction 1 (.write 0 8),
       instruction 2 (.write 1 9), instruction 3 (.read 0)] initial
    result.state.registers 0 = some (.reference 0) ∧
      result.state.registers 1 = some (.reference 0) ∧
      result.state.registers 3 = some (.payload (.literal 9)) ∧
      result.state.world.next = 1 ∧ result.state.world.writes = 2 := by
  simp [direct, meaning, initial, instruction, applyEffects, publish, charge]

/-- A later fault keeps exactly one completed write and does not replay it. -/
theorem write_prefix_before_fault :
    let result := direct meaning
      [instruction 0 (.allocate (.literal 7)), instruction 1 (.write 0 8),
       instruction 2 .raiseFault, instruction 3 (.write 0 9)] initial
    result.state.world.cells 0 = some (.literal 8) ∧
      result.state.world.writes = 1 ∧
      result.state.trace = [.allocated 0 (.literal 7), .written 0 8] ∧
      result.stop = .raised 7 ∧
      result.remaining = [instruction 3 (.write 0 9)] ∧
      result.invocations = 3 := by
  simp [direct, meaning, initial, instruction, applyEffects, publish, charge]

/-- An unsupported operation leaves its exact residual after the committed write. -/
theorem unsupported_preserves_suffix :
    let result := direct meaning
      [instruction 0 (.allocate (.literal 7)), instruction 1 (.write 0 8),
       instruction 2 .unavailable, instruction 3 (.write 0 9)] initial
    result.state.world.cells 0 = some (.literal 8) ∧
      result.state.world.writes = 1 ∧
      result.stop = .unavailable ∧
      result.remaining = [instruction 2 .unavailable,
        instruction 3 (.write 0 9)] ∧ result.invocations = 2 := by
  simp [direct, meaning, initial, instruction, applyEffects, publish, charge]

/-- Syntax in a new State is not evaluated merely by storing or reading it. -/
theorem stored_program_is_not_evaluated :
    let result := direct meaning
      [instruction 0 (.allocate (.add (.literal 1) (.literal 2))),
       instruction 1 (.read 0)] initial
    result.state.registers 1 =
        some (.payload (.add (.literal 1) (.literal 2))) ∧
      result.state.registers 1 ≠ some (.payload (.literal 3)) ∧
      result.state.world.writes = 0 := by
  simp [direct, meaning, initial, instruction, applyEffects, publish, charge]

/-- A payload value cannot serve as a ready State reference. -/
example : meaning.prepare (.write 0 8)
    (Function.update (fun _ => none) 0 (some (.payload (.literal 7)))) = none := by
  simp [meaning]

end Mettapedia.Machines.HEStateHostRegion
