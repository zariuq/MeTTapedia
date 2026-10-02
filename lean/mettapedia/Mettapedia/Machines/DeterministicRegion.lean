import Mettapedia.Machines.RegisterCode
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mathlib.Tactic

/-!
# Direct execution of deterministic MeTTa operation regions

CeTTa's named-state route schedules operand preparation, dispatches the ready
operation, packages its answer, and publishes it through an outcome choice.
A ready operation with at most one answer does not need that answer worklist.
The two interpreters below independently execute a register-operation sequence:
one expands each instruction into administrative tasks; the other dispatches
the operation directly. Their final registers, world, ordered effect prefix,
failure/exception status, and unavailable-operation continuation agree.

The concrete instance models ready `get-state` and `change-state!`, integer
addition, and explicit failure/exception boundaries. Named state is PeTTa's
symbol-keyed world, not HE state handles or Prime's branch-local Need cache.
The C connection is `petta_machine_schedule_named_state`, the
`PETTA_GOAL_NAMED_STATE_READY` branch, and `petta_eval_machine_named_state`.
These are semantic component specifications, not a proof of the C source or
the compiler's admission analysis. Operands must already be values or slots;
arbitrary expression evaluation, nondeterministic operations, foreign hooks,
allocation failure, concurrent mutation, and physical timing are outside it.
Register publication is assignment: admission must establish an unconstrained
destination or include result unification explicitly. The C outcome route also
merges answer bindings and unifies the expected result; singleton cardinality
alone does not justify erasing either operation.
Instruction-boundary slicing preserves ordered prefixes and the exact suffix.
Interruption inside an operation or between its administrative tasks is not
modeled: removing those runtime safe points requires a separate contract.

The cost counts actual interpreter task dispatches and primitive invocations.
It does not assign constant cost to operand preparation, store access, or
trace construction. The interpreters share primitive meaning, not control.
The current C singleton route already avoids a choice snapshot; the modeled
four administrative phases are not a claim about four native instructions.
-/

namespace Mettapedia.Machines.DeterministicRegion

open Mettapedia.Machines.RegisterCode (Regs)

inductive Reply (Value Fault : Type) where
  | value (value : Value)
  | failed
  | raised (fault : Fault)
  deriving DecidableEq, Repr

inductive Stop (Fault : Type) where
  | complete
  | failed
  | raised (fault : Fault)
  | unavailable
  | budget
  deriving DecidableEq, Repr

structure Instruction (Op : Type) where
  destination : Nat
  operation : Op
  deriving DecidableEq, Repr

structure State (Value World Event : Type) where
  registers : Regs Value
  world : World
  trace : List Event

structure PrimitiveResult (Value World Event Fault : Type) where
  world : World
  events : List Event
  reply : Reply Value Fault

structure Semantics (Op Ready Value World Event Fault : Type) where
  /-- Pure operand preparation. `none` requests the surrounding exact route. -/
  prepare : Op → Regs Value → Option Ready
  /-- One ready operation, possibly failing or raising after performing effects. -/
  invoke : Ready → World → PrimitiveResult Value World Event Fault

structure Result (Continuation Value World Event Fault : Type) where
  state : State Value World Event
  stop : Stop Fault
  remaining : List Continuation
  dispatches : Nat
  invocations : Nat

section General

variable {Op Ready Value World Event Fault : Type}

def applyEffects (s : State Value World Event)
    (r : PrimitiveResult Value World Event Fault) : State Value World Event :=
  { s with world := r.world, trace := s.trace ++ r.events }

def publish (s : State Value World Event) (destination : Nat) (value : Value) :
    State Value World Event :=
  { s with registers := Function.update s.registers destination (some value) }

def charge (dispatches invocations : Nat)
    (r : Result Op Value World Event Fault) : Result Op Value World Event Fault :=
  { r with dispatches := dispatches + r.dispatches,
           invocations := invocations + r.invocations }

/-- The direct executor has one dispatch per source instruction. -/
def direct (sem : Semantics Op Ready Value World Event Fault) :
    List (Instruction Op) → State Value World Event →
      Result (Instruction Op) Value World Event Fault
  | [], s => ⟨s, .complete, [], 0, 0⟩
  | i :: rest, s =>
      match sem.prepare i.operation s.registers with
      | none => ⟨s, .unavailable, i :: rest, 1, 0⟩
      | some ready =>
          let r := sem.invoke ready s.world
          let next := applyEffects s r
          match r.reply with
          | .value v => charge 1 1 (direct sem rest (publish next i.destination v))
          | .failed => ⟨next, .failed, rest, 1, 1⟩
          | .raised fault => ⟨next, .raised fault, rest, 1, 1⟩

inductive Task (Op Ready Value Fault : Type) where
  | prepare (instruction : Instruction Op)
  | invoke (destination : Nat) (ready : Ready)
  | collect (destination : Nat) (reply : Reply Value Fault)
  | publish (destination : Nat) (value : Value)

def Task.weight : Task Op Ready Value Fault → Nat
  | .prepare _ => 4
  | .invoke _ _ => 3
  | .collect _ _ => 2
  | .publish _ _ => 1

def weight : List (Task Op Ready Value Fault) → Nat
  | [] => 0
  | t :: rest => t.weight + weight rest

def schedule (code : List (Instruction Op)) : List (Task Op Ready Value Fault) :=
  code.map Task.prepare

/-- Unlike `direct`, this machine allocates ready, collected, and publication
tasks and interprets each separately. The decreasing task weight is semantic
termination infrastructure, not source fuel and not a resource cutoff. -/
def queued (sem : Semantics Op Ready Value World Event Fault)
    (tasks : List (Task Op Ready Value Fault)) (s : State Value World Event) :
    Result (Task Op Ready Value Fault) Value World Event Fault :=
  match tasks with
  | [] => ⟨s, .complete, [], 0, 0⟩
  | .prepare i :: rest =>
      match sem.prepare i.operation s.registers with
      | none => ⟨s, .unavailable, tasks, 1, 0⟩
      | some ready => charge 1 0 (queued sem (.invoke i.destination ready :: rest) s)
  | .invoke destination ready :: rest =>
      let r := sem.invoke ready s.world
      charge 1 1 (queued sem (.collect destination r.reply :: rest) (applyEffects s r))
  | .collect destination reply :: rest =>
      match reply with
      | .value value => charge 1 0 (queued sem (.publish destination value :: rest) s)
      | .failed => ⟨s, .failed, rest, 1, 0⟩
      | .raised fault => ⟨s, .raised fault, rest, 1, 0⟩
  | .publish destination value :: rest =>
      charge 1 0 (queued sem rest (publish s destination value))
termination_by weight tasks
decreasing_by all_goals simp [weight, Task.weight]

structure Behavior (Continuation Value World Event Fault : Type) where
  state : State Value World Event
  stop : Stop Fault
  remaining : List Continuation

def behavior (r : Result Op Value World Event Fault) : Behavior Op Value World Event Fault :=
  ⟨r.state, r.stop, r.remaining⟩

def scheduledBehavior (r : Result (Instruction Op) Value World Event Fault) :
    Behavior (Task Op Ready Value Fault) Value World Event Fault :=
  ⟨r.state, r.stop, schedule r.remaining⟩

/-- Complete observations include the retained continuation and effects before
failure. Equality is stronger than agreement of successful answer bags. -/
theorem queued_behavior_eq_direct (sem : Semantics Op Ready Value World Event Fault)
    (code : List (Instruction Op)) (s : State Value World Event) :
    behavior (queued sem (schedule code) s) = scheduledBehavior (direct sem code s) := by
  induction code generalizing s with
  | nil => simp [schedule, queued, direct, behavior, scheduledBehavior]
  | cons i rest ih =>
      simp only [schedule, List.map_cons, queued, direct]
      cases hp : sem.prepare i.operation s.registers with
      | none => simp [behavior, scheduledBehavior, schedule]
      | some ready =>
          cases hr : (sem.invoke ready s.world).reply with
          | value v =>
              simpa [hp, queued, hr, behavior, scheduledBehavior, charge, schedule] using
                ih (publish (applyEffects s (sem.invoke ready s.world)) i.destination v)
          | failed => simp [queued, hr, behavior, scheduledBehavior, charge, schedule]
          | raised fault => simp [queued, hr, behavior, scheduledBehavior, charge, schedule]

/-- Eliminating administration never deletes or duplicates a primitive call. -/
theorem queued_invocations_eq_direct (sem : Semantics Op Ready Value World Event Fault)
    (code : List (Instruction Op)) (s : State Value World Event) :
    (queued sem (schedule code) s).invocations = (direct sem code s).invocations := by
  induction code generalizing s with
  | nil => simp [schedule, queued, direct]
  | cons i rest ih =>
      simp only [schedule, List.map_cons, queued, direct]
      cases hp : sem.prepare i.operation s.registers with
      | none => simp
      | some ready =>
          cases hr : (sem.invoke ready s.world).reply with
          | value v =>
              simpa [hp, queued, hr, charge, schedule] using
                ih (publish (applyEffects s (sem.invoke ready s.world)) i.destination v)
          | failed => simp [queued, hr, charge]
          | raised fault => simp [queued, hr, charge]

/-- On a completed region, four queued task dispatches become one direct
instruction dispatch. This is not a factor-four wall-clock theorem. -/
theorem completed_dispatches (sem : Semantics Op Ready Value World Event Fault)
    (code : List (Instruction Op)) (s : State Value World Event)
    (complete : (direct sem code s).stop = .complete) :
    (direct sem code s).dispatches = code.length ∧
    (queued sem (schedule code) s).dispatches = 4 * code.length := by
  induction code generalizing s with
  | nil => simp [schedule, queued, direct]
  | cons i rest ih =>
      cases hp : sem.prepare i.operation s.registers with
      | none => simp [direct, hp] at complete
      | some ready =>
          cases hr : (sem.invoke ready s.world).reply with
          | failed => simp [direct, hp, hr] at complete
          | raised fault => simp [direct, hp, hr] at complete
          | value v =>
              have hc : (direct sem rest
                  (publish (applyEffects s (sem.invoke ready s.world)) i.destination v)).stop =
                    .complete := by simpa [direct, hp, hr, charge] using complete
              obtain ⟨hd, hq⟩ := ih _ hc
              simp only [schedule] at hq
              simp [direct, hp, hr, queued, schedule, charge, hd, hq]
              omega

/-- A completed slice with deferred instructions is budget-limited, not
exhausted. Failure, exception and unavailable operands retain their status. -/
def boundaryStop (hasSuffix : Bool) : Stop Fault → Stop Fault
  | .complete => if hasSuffix then .budget else .complete
  | other => other

def directSlice (sem : Semantics Op Ready Value World Event Fault) (limit : Nat)
    (code : List (Instruction Op)) (s : State Value World Event) :
    Result (Instruction Op) Value World Event Fault :=
  let r := direct sem (code.take limit) s
  { r with stop := boundaryStop (!(code.drop limit).isEmpty) r.stop,
           remaining := r.remaining ++ code.drop limit }

/-- The same instruction-boundary request on the administrative machine;
this is not a request for an equal number of administrative task steps. -/
def queuedSlice (sem : Semantics Op Ready Value World Event Fault) (limit : Nat)
    (code : List (Instruction Op)) (s : State Value World Event) :
    Result (Task Op Ready Value Fault) Value World Event Fault :=
  let r := queued sem (schedule (code.take limit)) s
  { r with stop := boundaryStop (!(code.drop limit).isEmpty) r.stop,
           remaining := r.remaining ++ schedule (code.drop limit) }

/-- Every source-instruction boundary retains the same state, ordered trace,
status, and unexecuted continuation, including a failure within the prefix. -/
theorem sliced_behavior_eq_direct (sem : Semantics Op Ready Value World Event Fault)
    (limit : Nat) (code : List (Instruction Op)) (s : State Value World Event) :
    behavior (queuedSlice sem limit code s) =
      scheduledBehavior (directSlice sem limit code s) := by
  have eqPrefix := queued_behavior_eq_direct sem (code.take limit) s
  let extend (b : Behavior (Task Op Ready Value Fault) Value World Event Fault) :=
    { b with stop := boundaryStop (!(code.drop limit).isEmpty) b.stop,
             remaining := b.remaining ++ schedule (code.drop limit) }
  simpa [extend, behavior, scheduledBehavior, directSlice, queuedSlice, schedule]
    using congrArg extend eqPrefix

/-- Successful prefix completion can resume without rerunning its effects. -/
theorem direct_append_of_complete (sem : Semantics Op Ready Value World Event Fault)
    (leading suffix : List (Instruction Op)) (s : State Value World Event)
    (complete : (direct sem leading s).stop = .complete) :
    direct sem (leading ++ suffix) s =
      charge (direct sem leading s).dispatches (direct sem leading s).invocations
        (direct sem suffix (direct sem leading s).state) := by
  induction leading generalizing s with
  | nil => simp [direct, charge]
  | cons i rest ih =>
      cases hp : sem.prepare i.operation s.registers with
      | none => simp [direct, hp] at complete
      | some ready =>
          cases hr : (sem.invoke ready s.world).reply with
          | failed => simp [direct, hp, hr] at complete
          | raised fault => simp [direct, hp, hr] at complete
          | value v =>
              have hc : (direct sem rest
                  (publish (applyEffects s (sem.invoke ready s.world)) i.destination v)).stop =
                    .complete := by simpa [direct, hp, hr, charge] using complete
              simpa [direct, hp, hr, charge, Nat.add_assoc] using
                congrArg (charge 1 1) (ih _ hc)

end General

/-! ## PeTTa ready named-state operations

The reference clauses are `change-state!(Name, Value, true) :- nb_setval(Name,
Value)` and `get-state(Name, Value) :- nb_getval(Name, Value)`. Values here have
already been evaluated; this is the ready-operation boundary, not an evaluator
for arbitrary children of these source forms. A missing name raises at this
boundary, as the reference primitive does; an enclosing `reduce` handler may
catch it. The current C handler's missing-name behavior is not proved here.
-/

namespace PeTTa

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)

inductive Value where
  | integer (value : Int)
  | truth (value : Bool)
  deriving DecidableEq, Repr

def Value.toPattern : Value → Pattern
  | .integer n => .apply (toString n) []
  | .truth true => .apply "true" []
  | .truth false => .apply "false" []

abbrev Store := String → Option Value

inductive Fault where
  | missingState (name : String)
  | integerExpected
  | exception (message : String)
  deriving DecidableEq, Repr

inductive Event where
  | read (name : String) (value : Value)
  | write (name : String) (before : Option Value) (after : Value)
  deriving DecidableEq, Repr

inductive Operand where
  | literal (value : Value)
  | slot (register : Nat)
  deriving DecidableEq, Repr

def Operand.resolve (registers : Regs Value) : Operand → Option Value
  | .literal value => some value
  | .slot register => registers register

inductive Operation where
  | read (name : String)
  | write (name : String) (value : Operand)
  | add (left right : Operand)
  | unifyGround (left right : Operand)
  | fail
  | raise (fault : Fault)
  deriving DecidableEq, Repr

inductive Ready where
  | read (name : String)
  | write (name : String) (value : Value)
  | add (left right : Value)
  | unifyGround (left right : Value)
  | fail
  | raise (fault : Fault)
  deriving DecidableEq, Repr

def prepare : Operation → Regs Value → Option Ready
  | .read name, _ => some (.read name)
  | .write name value, registers => (value.resolve registers).map (.write name)
  | .add left right, registers => do
      let l ← left.resolve registers
      let r ← right.resolve registers
      pure (.add l r)
  | .unifyGround left right, registers => do
      let l ← left.resolve registers
      let r ← right.resolve registers
      pure (.unifyGround l r)
  | .fail, _ => some .fail
  | .raise fault, _ => some (.raise fault)

def invoke : Ready → Store → PrimitiveResult Value Store Event Fault
  | .read name, store =>
      match store name with
      | none => ⟨store, [], .raised (.missingState name)⟩
      | some value => ⟨store, [.read name value], .value value⟩
  | .write name value, store =>
      ⟨Function.update store name (some value), [.write name (store name) value],
        .value (.truth true)⟩
  | .add (.integer left) (.integer right), store =>
      ⟨store, [], .value (.integer (left + right))⟩
  | .add _ _, store => ⟨store, [], .raised .integerExpected⟩
  | .unifyGround left right, store =>
      ⟨store, [], if left = right then .value (.truth true) else .failed⟩
  | .fail, store => ⟨store, [], .failed⟩
  | .raise fault, store => ⟨store, [], .raised fault⟩

def semantics : Semantics Operation Ready Value Store Event Fault := ⟨prepare, invoke⟩

/-- The reference's two named-state calls, after argument evaluation. -/
inductive NamedCall where
  | read (name : String)
  | write (name : String) (value : Value)
  deriving DecidableEq, Repr

def NamedCall.toPattern : NamedCall → Pattern
  | .read name => .apply "get-state" [.apply name []]
  | .write name value => .apply "change-state!" [.apply name [], value.toPattern]

def NamedCall.ready : NamedCall → Ready
  | .read name => .read name
  | .write name value => .write name value

def NamedCall.instruction (destination : Nat) : NamedCall → Instruction Operation
  | .read name => ⟨destination, .read name⟩
  | .write name value => ⟨destination, .write name (.literal value)⟩

/-- An independent relational specification of the two reference operations.
Writes replace the named value and are not undone by a later failed operation.
The read/write events retain the order observable by the surrounding region. -/
inductive NamedStep : NamedCall → Store → PrimitiveResult Value Store Event Fault → Prop
  | read (name : String) (store : Store) (value : Value) (found : store name = some value) :
      NamedStep (.read name) store ⟨store, [.read name value], .value value⟩
  | missing (name : String) (store : Store) (absent : store name = none) :
      NamedStep (.read name) store ⟨store, [], .raised (.missingState name)⟩
  | write (name : String) (store : Store) (value : Value) :
      NamedStep (.write name value) store
        ⟨Function.update store name (some value), [.write name (store name) value],
          .value (.truth true)⟩

theorem named_invoke_sound (call : NamedCall) (store : Store) :
    NamedStep call store (invoke call.ready store) := by
  cases call with
  | read name =>
      cases h : store name with
      | none => simpa [NamedCall.ready, invoke, h] using NamedStep.missing name store h
      | some value => simpa [NamedCall.ready, invoke, h] using NamedStep.read name store value h
  | write name value => exact NamedStep.write name store value

theorem named_invoke_complete (call : NamedCall) (store : Store)
    (result : PrimitiveResult Value Store Event Fault) (reference : NamedStep call store result) :
    invoke call.ready store = result := by
  cases reference <;> simp_all [NamedCall.ready, invoke]

theorem named_prepare (call : NamedCall) (destination : Nat) (registers : Regs Value) :
    prepare (call.instruction destination).operation registers = some call.ready := by
  cases call <;> rfl

/-- Concrete PeTTa operation sequences inherit the complete control theorem.
Instruction results can feed later operands through registers. -/
theorem named_region_queue_elimination (code : List (Instruction Operation))
    (s : State Value Store Event) :
    behavior (queued semantics (schedule code) s) =
      scheduledBehavior (direct semantics code s) :=
  queued_behavior_eq_direct semantics code s

def initial : State Value Store Event :=
  ⟨fun _ => none, fun name => if name = "&counter" then some (.integer 0) else none, []⟩

def increment : List (Instruction Operation) :=
  [⟨0, .read "&counter"⟩,
   ⟨1, .add (.slot 0) (.literal (.integer 1))⟩,
   ⟨2, .write "&counter" (.slot 1)⟩,
   ⟨3, .read "&counter"⟩]

theorem increment_behavior :
    (direct semantics increment initial).stop = .complete ∧
    (direct semantics increment initial).state.world "&counter" = some (.integer 1) ∧
    (direct semantics increment initial).state.registers 3 = some (.integer 1) ∧
    (direct semantics increment initial).state.trace =
      [.read "&counter" (.integer 0),
       .write "&counter" (some (.integer 0)) (.integer 1),
       .read "&counter" (.integer 1)] := by
  decide

theorem increment_dispatches :
    (direct semantics increment initial).dispatches = 4 ∧
    (queued semantics (schedule increment) initial).dispatches = 16 ∧
    (queued semantics (schedule increment) initial).invocations = 4 := by
  have costs := completed_dispatches semantics increment initial increment_behavior.1
  refine ⟨costs.1, costs.2, ?_⟩
  rw [queued_invocations_eq_direct]
  decide

/-- Pausing after the write exposes precisely its effect prefix; resuming
executes the remaining read once and preserves the accumulated trace. -/
theorem increment_slice_resume :
    let paused := directSlice semantics 3 increment initial
    paused.stop = .budget ∧ paused.remaining = [⟨3, .read "&counter"⟩] ∧
    paused.state.trace =
      [.read "&counter" (.integer 0),
       .write "&counter" (some (.integer 0)) (.integer 1)] ∧
    (direct semantics paused.remaining paused.state).state.trace =
      (direct semantics increment initial).state.trace := by
  decide

def failAfterWrite : List (Instruction Operation) :=
  [⟨0, .write "&counter" (.literal (.integer 1))⟩,
   ⟨1, .fail⟩,
   ⟨2, .write "&counter" (.literal (.integer 2))⟩]

/-- A failed operation stops the suffix without rolling back prior named writes. -/
theorem failure_preserves_prefix :
    (direct semantics failAfterWrite initial).stop = .failed ∧
    (direct semantics failAfterWrite initial).state.world "&counter" = some (.integer 1) ∧
    (direct semantics failAfterWrite initial).state.trace =
      [.write "&counter" (some (.integer 0)) (.integer 1)] ∧
    (direct semantics failAfterWrite initial).remaining =
      [⟨2, .write "&counter" (.literal (.integer 2))⟩] ∧
    (queued semantics (schedule failAfterWrite) initial).dispatches = 7 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  simp [queued, schedule, failAfterWrite, semantics, prepare, Operand.resolve,
    invoke, charge, applyEffects, publish, initial]

/-- A successful singleton write still fails against an incompatible expected
result. The preceding write survives; assignment alone would lose this check. -/
theorem expected_result_failure_keeps_write :
    let unchecked : List (Instruction Operation) :=
      [⟨0, .write "&counter" (.literal (.integer 1))⟩]
    let checked := unchecked ++
      [⟨1, .unifyGround (.slot 0) (.literal (.truth false))⟩,
       ⟨2, .write "&counter" (.literal (.integer 2))⟩]
    (direct semantics unchecked initial).stop = .complete ∧
    (direct semantics checked initial).stop = .failed ∧
    (direct semantics checked initial).state.world "&counter" = some (.integer 1) ∧
    (direct semantics checked initial).state.trace =
      [.write "&counter" (some (.integer 0)) (.integer 1)] := by
  decide

def raiseAfterWrite : List (Instruction Operation) :=
  [⟨0, .write "&counter" (.literal (.integer 1))⟩,
   ⟨1, .raise (.exception "stop")⟩,
   ⟨2, .write "&counter" (.literal (.integer 2))⟩]

theorem exception_preserves_prefix :
    (direct semantics raiseAfterWrite initial).stop = .raised (.exception "stop") ∧
    (direct semantics raiseAfterWrite initial).state.world "&counter" = some (.integer 1) ∧
    (direct semantics raiseAfterWrite initial).state.trace =
      [.write "&counter" (some (.integer 0)) (.integer 1)] := by
  decide

def unresolved : List (Instruction Operation) :=
  [⟨0, .write "&counter" (.slot 42)⟩, ⟨1, .read "&counter"⟩]

/-- Unavailable operands retain the whole remaining operation, not successful
completion or an empty answer that loses the continuation. -/
theorem unresolved_retains_continuation :
    (direct semantics unresolved initial).stop = .unavailable ∧
    (direct semantics unresolved initial).remaining = unresolved ∧
    (direct semantics unresolved initial).state.trace = [] ∧
    (direct semantics unresolved initial).invocations = 0 := by
  decide

theorem resolved_continuation_can_resume :
    let paused := direct semantics unresolved initial
    let resumed := direct semantics paused.remaining (publish paused.state 42 (.integer 9))
    resumed.stop = .complete ∧ resumed.state.world "&counter" = some (.integer 9) ∧
    resumed.state.trace =
      [.write "&counter" (some (.integer 0)) (.integer 9), .read "&counter" (.integer 9)] := by
  decide

/-- Equal final state does not license changing the order of reads and writes. -/
theorem final_store_does_not_determine_effects :
    let first : List (Instruction Operation) :=
      [⟨0, .write "&counter" (.literal (.integer 1))⟩, ⟨1, .read "&counter"⟩]
    let second : List (Instruction Operation) :=
      [⟨1, .read "&counter"⟩, ⟨0, .write "&counter" (.literal (.integer 1))⟩]
    (direct semantics first initial).state.world "&counter" =
      (direct semantics second initial).state.world "&counter" ∧
    (direct semantics first initial).state.trace ≠
      (direct semantics second initial).state.trace := by
  decide

/-- Having the same answer value twice is outside singleton admission. -/
theorem duplicate_answers_cannot_be_one_result :
    ([Value.truth true, .truth true].take 1) ≠ [Value.truth true, .truth true] := by
  decide

end PeTTa

end Mettapedia.Machines.DeterministicRegion
