import Mettapedia.Machines.DeterministicRegion
import Mettapedia.Machines.HEProducerCompletion

/-!
# Native allocation inside a qualified HE eager region

The constructor is a real world transition: it returns the current fresh
identity, advances the allocator, and records one allocation event. The
existing independently defined queued and direct region interpreters execute
that same primitive. Their complete behavior and invocation counts agree,
including committed prefixes before a fault or an unavailable operation.
HE producer completion then operates on the unchanged occurrence carrier.

This is the component contract used by source-certified nullary `new-space`.
It does not turn allocation into a pure expression or replace the native
constructor. C admission must check the active constructor signature, source
revision, operand shape and the existing HE effect-order/binding restrictions.
Native SpaceHold ownership, physical collection, allocation failure and C
source correspondence remain separate obligations. No StateCell constructor
or broader typed/NotReducible/worker region is admitted by this model.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HENativeConstructorRegion

open DeterministicRegion

inductive Value where
  | space (identity : Nat)
  deriving DecidableEq, Repr

inductive Event where
  | allocated (identity : Nat)
  deriving DecidableEq, Repr

inductive Operation where
  | newSpace
  | raiseFault
  | unavailable
  deriving DecidableEq, Repr

inductive Ready where
  | allocate
  | raiseFault
  deriving DecidableEq, Repr

def meaning : Semantics Operation Ready Value Nat Event Nat where
  prepare operation _ := match operation with
    | .newSpace => some .allocate
    | .raiseFault => some .raiseFault
    | .unavailable => none
  invoke ready next := match ready with
    | .allocate =>
        ⟨next + 1, [.allocated next], .value (.space next)⟩
    | .raiseFault => ⟨next, [], .raised 7⟩

def initial (next : Nat) : State Value Nat Event :=
  ⟨fun _ => none, next, []⟩

def instruction (destination : Nat) (operation : Operation) : Instruction Operation :=
  ⟨destination, operation⟩

theorem constructor_allocates (next : Nat) :
    meaning.invoke .allocate next =
      ⟨next + 1, [.allocated next], .value (.space next)⟩ := rfl

/-- Primitive meaning is shared; administrative control is independent. -/
theorem region_behavior (code : List (Instruction Operation))
    (state : State Value Nat Event) :
    behavior (queued meaning (schedule code) state) =
      scheduledBehavior (direct meaning code state) :=
  queued_behavior_eq_direct meaning code state

theorem region_invocations (code : List (Instruction Operation))
    (state : State Value Nat Event) :
    (queued meaning (schedule code) state).invocations =
      (direct meaning code state).invocations :=
  queued_invocations_eq_direct meaning code state

/-- Distinct constructor calls never contract into one shared identity. -/
theorem two_fresh_allocations (next : Nat) :
    let result := direct meaning
      [instruction 0 .newSpace, instruction 1 .newSpace] (initial next)
    result.state.world = next + 2 ∧
      result.state.trace = [.allocated next, .allocated (next + 1)] ∧
      result.state.registers 0 = some (.space next) ∧
      result.state.registers 1 = some (.space (next + 1)) ∧
      result.invocations = 2 := by
  simp [direct, meaning, initial, instruction, applyEffects, publish, charge,
    Nat.add_assoc]

theorem fresh_identities_differ (next : Nat) :
    Value.space next ≠ Value.space (next + 1) := by
  intro same
  injection same with impossible
  omega

/-- A later fault keeps the first allocation, and never executes the suffix. -/
theorem fault_preserves_allocation_prefix (next : Nat) :
    let result := direct meaning
      [instruction 0 .newSpace, instruction 1 .raiseFault,
       instruction 2 .newSpace] (initial next)
    result.state.world = next + 1 ∧
      result.state.trace = [.allocated next] ∧
      result.stop = .raised 7 ∧
      result.remaining = [instruction 2 .newSpace] ∧
      result.invocations = 2 := by
  simp [direct, meaning, initial, instruction, applyEffects, publish, charge]

/-- Unsupported source retains its exact pending instruction and suffix. -/
theorem unavailable_preserves_residual (next : Nat) :
    let result := direct meaning
      [instruction 0 .newSpace, instruction 1 .unavailable,
       instruction 2 .newSpace] (initial next)
    result.state.world = next + 1 ∧
      result.state.trace = [.allocated next] ∧
      result.stop = .unavailable ∧
      result.remaining = [instruction 1 .unavailable, instruction 2 .newSpace] ∧
      result.invocations = 1 := by
  simp [direct, meaning, initial, instruction, applyEffects, publish, charge]

inductive Returned where
  | value (value : Value)
  | error (fault : Nat)
  deriving DecidableEq, Repr

def isError : Returned → Bool
  | .value _ => false
  | .error _ => true

/-- Completed HE presentation preserves each resource value's carrier. -/
theorem completed_frontier (rows : List Returned) :
    HEProducerCompletion.present isError true
      (HEProducerCompletion.collect isError true rows HEProducerCompletion.empty) =
      HEProducerCompletion.reference isError true rows :=
  HEProducerCompletion.collection_refines isError true rows

theorem aliases_keep_multiplicity (identity : Nat) :
    HEProducerCompletion.present isError true
      (HEProducerCompletion.collect isError true
        [.value (.space identity), .value (.space identity)] HEProducerCompletion.empty) =
      [.value (.space identity), .value (.space identity)] := by
  rw [completed_frontier]
  simp [HEProducerCompletion.reference, isError]

end Mettapedia.Machines.HENativeConstructorRegion
