import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedMachine

/-!
# Exact source actions of the scoped Need instance

These are laws of the existing owned Need machine with the scoped-code
specification. They retain arbitrary heaps, lexical environments and consumer
stacks. Successful allocation is explicit: arbitrary supplied heaps need not
have a fresh next slot. Allocation leaves a suspended origin; only the separate
force transition selects an occurrence and starts its producer.

The short unique paths describe administrative source actions, not a bounded
replacement for whole-program adequacy. Native Sigma pairing happens before
an enclosing commit. Completed cache observations retain the current world and
consumer, without calling the primitive handler or replaying an effect.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedMachine

open PrimeNeedReference
open ScopedNeedComputation (Code)

variable {Head Operation Effect NativeFault StableFault : Type} {m n k : Nat}

/-- Lazy binding allocates its producer and enters the handle-binding body;
there is no demand transition in this step. -/
theorem letNeed_allocate_step
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (suspended : Code Head Operation Effect n k)
    (body : Code Head Operation Effect n (k + 1))
    (values : Sub Head n m) (needs : Fin k → CellId) (kont : Kont Head m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    {world : NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    (control : machine.control =
      .run (.evaluate ⟨n, k, .letNeed suspended body, values, needs⟩ kont) stack)
    (allocated : machine.world.allocate? ⟨n, k, suspended, values, needs⟩ =
      some (world, cell)) :
    step (spec primitive) machine =
      [finished machine world
        (.run (.evaluate ⟨n, k + 1, body, values, Fin.cases cell needs⟩ kont) stack)
        1 1 1 1] := by
  simp only [step, control, spec, action, allocated, afterAllocation, NeedBody.open]

/-- Successful lazy allocation stores the unexecuted source closure. -/
theorem letNeed_allocated_suspended
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {suspended : Code Head Operation Effect n k}
    {values : Sub Head n m} {needs : Fin k → CellId} {cell : CellId}
    (allocated : world.allocate? ⟨n, k, suspended, values, needs⟩ = some (next, cell)) :
    next.heap.lookup cell = some ⟨⟨n, k, suspended, values, needs⟩, .suspended⟩ :=
  World.allocate?_lookup_same allocated

/-- Allocation cannot overwrite a different captured handle's cell. -/
theorem allocation_preserves_other
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {origin : Closure Head Operation Effect m} {cell other : CellId}
    (allocated : world.allocate? origin = some (next, cell)) (different : other ≠ cell) :
    next.heap.lookup other = world.heap.lookup other :=
  World.allocate?_preserves_other allocated different

theorem sequence_allocate_step
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (first : Code Head Operation Effect n k)
    (body : Code Head Operation Effect (n + 1) k)
    (values : Sub Head n m) (needs : Fin k → CellId) (kont : Kont Head m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    {world : NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    (control : machine.control =
      .run (.evaluate ⟨n, k, .sequence first body, values, needs⟩ kont) stack)
    (allocated : machine.world.allocate? ⟨n, k, first, values, needs⟩ = some (world, cell)) :
    step (spec primitive) machine =
      [finished machine world
        (.run (.demand cell (.bindValue ⟨n, k, body, values, needs⟩ kont)) stack)
        1 1 1 1] := by
  simp only [step, control, spec, action, allocated, afterAllocation]

theorem sequenceSigma_allocate_step
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (first : Code Head Operation Effect n k)
    (body : Code Head Operation Effect (n + 1) k)
    (values : Sub Head n m) (needs : Fin k → CellId) (kont : Kont Head m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    {world : NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    (control : machine.control =
      .run (.evaluate ⟨n, k, .sequenceSigma first body, values, needs⟩ kont) stack)
    (allocated : machine.world.allocate? ⟨n, k, first, values, needs⟩ = some (world, cell)) :
    step (spec primitive) machine =
      [finished machine world
        (.run (.demand cell (.bindSigma ⟨n, k, body, values, needs⟩ kont)) stack)
        1 1 1 1] := by
  simp only [step, control, spec, action, allocated, afterAllocation]

/-- The explicit local demand installs the consumer before forcing a cell. -/
theorem demand_step
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (cell : CellId) (resume : Resume Head Operation Effect m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (control : machine.control = .run (.demand cell resume) stack) :
    step (spec primitive) machine =
      [finished machine machine.world (.force cell (.resume resume :: stack)) 0 0 0 0] := by
  simp only [step, control, spec, action]

/-- A handle occurrence resolves through the captured handle environment, not
through the native substitution and not by allocating a second cell. -/
theorem force_reference_step
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (reference : Fin k) (values : Sub Head n m) (needs : Fin k → CellId)
    (kont : Kont Head m) (stack : List (Frame (Resume Head Operation Effect m)))
    (control : machine.control =
      .run (.evaluate ⟨n, k, .force reference, values, needs⟩ kont) stack) :
    step (spec primitive) machine =
      [finished machine machine.world
        (.force (needs reference) (.resume (.finish kont) :: stack)) 0 0 0 0] := by
  simp only [step, control, spec, action]

theorem returnValue_step
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (term : Tm Head n) (values : Sub Head n m) (needs : Fin k → CellId)
    (kont : Kont Head m) (stack : List (Frame (Resume Head Operation Effect m)))
    (control : machine.control =
      .run (.evaluate ⟨n, k, .returnValue term, values, needs⟩ kont) stack) :
    step (spec primitive) machine =
      [finished machine machine.world
        (.returned (finish (.value (subst values term)) kont) stack) 0 0 0 0] := by
  simp only [step, control, spec, action]

theorem sequence_allocate_then_demand
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (first : Code Head Operation Effect n k)
    (body : Code Head Operation Effect (n + 1) k)
    (values : Sub Head n m) (needs : Fin k → CellId) (kont : Kont Head m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    {world : NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    (control : machine.control =
      .run (.evaluate ⟨n, k, .sequence first body, values, needs⟩ kont) stack)
    (allocated : machine.world.allocate? ⟨n, k, first, values, needs⟩ = some (world, cell)) :
    UniqueSteps (spec primitive) 2 machine
      { world := world
        control := .force cell (.resume (.bindValue ⟨n, k, body, values, needs⟩ kont) :: stack)
        work := (machine.work.bump 1 1 1 1).bump 0 0 0 0 } := by
  exact .cons
    (sequence_allocate_step primitive machine first body values needs kont stack control allocated)
    (.cons rfl (.refl _))

theorem sequenceSigma_allocate_then_demand
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (first : Code Head Operation Effect n k)
    (body : Code Head Operation Effect (n + 1) k)
    (values : Sub Head n m) (needs : Fin k → CellId) (kont : Kont Head m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    {world : NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    (control : machine.control =
      .run (.evaluate ⟨n, k, .sequenceSigma first body, values, needs⟩ kont) stack)
    (allocated : machine.world.allocate? ⟨n, k, first, values, needs⟩ = some (world, cell)) :
    UniqueSteps (spec primitive) 2 machine
      { world := world
        control := .force cell (.resume (.bindSigma ⟨n, k, body, values, needs⟩ kont) :: stack)
        work := (machine.work.bump 1 1 1 1).bump 0 0 0 0 } := by
  exact .cons
    (sequenceSigma_allocate_step primitive machine first body values needs kont stack control allocated)
    (.cons rfl (.refl _))

theorem bindValue_resume_step
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (body : ValueBody Head Operation Effect m) (value : Tm Head m) (kont : Kont Head m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (control : machine.control =
      .returned (.value value) (.resume (.bindValue body kont) :: stack)) :
    step (spec primitive) machine =
      [finished machine machine.world (.run (.evaluate (body.open value) kont) stack) 0 0 0 0] := by
  simp only [step, control, spec, afterDemand]

theorem bindSigma_resume_step
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (body : ValueBody Head Operation Effect m) (value : Tm Head m) (kont : Kont Head m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (control : machine.control =
      .returned (.value value) (.resume (.bindSigma body kont) :: stack)) :
    step (spec primitive) machine =
      [finished machine machine.world
        (.run (.evaluate (body.open value) (.pair value kont)) stack) 0 0 0 0] := by
  simp only [step, control, spec, afterDemand]

theorem finish_resume_step
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head StableFault NativeFault m) (kont : Kont Head m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (control : machine.control = .returned outcome (.resume (.finish kont) :: stack)) :
    step (spec primitive) machine =
      [finished machine machine.world
        (.run (.complete (finish outcome kont)) stack) 0 0 0 0] := by
  simp only [step, control, spec, afterDemand]

theorem complete_step
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head StableFault NativeFault m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (control : machine.control = .run (.complete outcome) stack) :
    step (spec primitive) machine =
      [finished machine machine.world (.returned outcome stack) 0 0 0 0] := by
  simp only [step, control, spec, action]

/-- The caller's commit frame, if present in `stack`, receives the pair only
after the native-value continuation has completed. No cache is touched by these
two administrative transitions. -/
theorem sigma_return_before_commit
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (term : Tm Head (n + 1)) (values : Sub Head n m) (needs : Fin k → CellId)
    (value : Tm Head m) (kont : Kont Head m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (control : machine.control = .returned (.value value)
      (.resume (.bindSigma ⟨n, k, .returnValue term, values, needs⟩ kont) :: stack)) :
    UniqueSteps (spec primitive) 2 machine
      { world := machine.world
        control := .returned
          (finish (.value (.pair value (subst (consSub value values) term))) kont) stack
        work := (machine.work.bump 0 0 0 0).bump 0 0 0 0 } := by
  exact .cons
    (bindSigma_resume_step primitive machine ⟨n, k, .returnValue term, values, needs⟩
      value kont stack control)
    (.cons rfl (.refl _))

/-- A source effect appends one receipt and retains the heap and both
continuation layers. It is not an implicit external state transition. -/
theorem emit_step
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (effect : Effect) (next : Code Head Operation Effect n k)
    (values : Sub Head n m) (needs : Fin k → CellId) (kont : Kont Head m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (control : machine.control =
      .run (.evaluate ⟨n, k, .emit effect next, values, needs⟩ kont) stack) :
    step (spec primitive) machine =
      [finished machine (recorded machine.world (.effect effect))
        (.run (.evaluate ⟨n, k, next, values, needs⟩ kont) stack) 0 0 1 0] := by
  simp only [step, control, spec, action]

theorem call_step
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (operation : Operation) (argument : Tm Head n)
    (values : Sub Head n m) (needs : Fin k → CellId) (kont : Kont Head m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (control : machine.control =
      .run (.evaluate ⟨n, k, .call operation argument, values, needs⟩ kont) stack) :
    step (spec primitive) machine =
      [finished machine machine.world
        (.returned (finish (liftOutcome (primitive operation (subst values argument))) kont) stack)
        0 0 0 0] := by
  simp only [step, control, spec, action]

/-- First force of a choice installs two occurrence-indexed producer branches,
each with an empty native continuation and its own commit owner. -/
theorem choice_force_step
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (left right : Code Head Operation Effect n k)
    (values : Sub Head n m) (needs : Fin k → CellId)
    (cell : CellId) (stack : List (Frame (Resume Head Operation Effect m)))
    (control : machine.control = .force cell stack)
    (suspended : machine.world.heap.lookup cell =
      some ⟨⟨n, k, .choose left right, values, needs⟩, .suspended⟩) :
    let owner := machine.world.nextEvaluator
    let base := { machine.world with nextEvaluator := owner + 1 }
    let record : CellRecord (Closure Head Operation Effect m) (Tm Head m) StableFault :=
      ⟨⟨n, k, .choose left right, values, needs⟩, .suspended⟩
    step (spec primitive) machine =
      [finished machine
        (recorded (recorded ((base.fork 0).setKnownCache cell record (.evaluating owner))
          (.evaluate cell owner)) (.chooseRule cell .left))
        (.run (.evaluate ⟨n, k, left, values, needs⟩ .done) (.commit cell owner :: stack))
        1 1 2 0,
       finished machine
        (recorded (recorded ((base.fork 1).setKnownCache cell record (.evaluating owner))
          (.evaluate cell owner)) (.chooseRule cell .right))
        (.run (.evaluate ⟨n, k, right, values, needs⟩ .done) (.commit cell owner :: stack))
        1 1 2 0] := by
  simp only [step, control, suspended, spec, alternatives, branchAlternatives]

/-- This holds even when the two source branches are literally equal. -/
theorem choice_force_length
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (left right : Code Head Operation Effect n k)
    (values : Sub Head n m) (needs : Fin k → CellId)
    (cell : CellId) (stack : List (Frame (Resume Head Operation Effect m)))
    (control : machine.control = .force cell stack)
    (suspended : machine.world.heap.lookup cell =
      some ⟨⟨n, k, .choose left right, values, needs⟩, .suspended⟩) :
    (step (spec primitive) machine).length = 2 := by
  rw [choice_force_step primitive machine left right values needs cell stack control suspended]
  rfl

/-- Equal branch code cannot justify replacing choice by a singleton force. -/
theorem duplicate_choice_not_singleton
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine next : NeedMachine Head Operation Effect StableFault NativeFault m)
    (branch : Code Head Operation Effect n k)
    (values : Sub Head n m) (needs : Fin k → CellId)
    (cell : CellId) (stack : List (Frame (Resume Head Operation Effect m)))
    (control : machine.control = .force cell stack)
    (suspended : machine.world.heap.lookup cell =
      some ⟨⟨n, k, .choose branch branch, values, needs⟩, .suspended⟩) :
    step (spec primitive) machine ≠ [next] := by
  intro singleton
  have length := choice_force_length primitive machine branch branch values needs cell stack
    control suspended
  rw [singleton] at length
  simp at length

/-- Once a raw native value is cached, even a different primitive producer
cannot change this force transition. This says nothing about replacing that
producer while evaluating a still-suspended origin. -/
theorem cached_force_primitive_independent
    (first second : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    {cell : CellId} {stack : List (Frame (Resume Head Operation Effect m))}
    {origin : Closure Head Operation Effect m} {value : Tm Head m}
    (control : machine.control = .force cell stack)
    (cached : machine.world.heap.lookup cell = some ⟨origin, .value value⟩) :
    step (spec first) machine = step (spec second) machine := by
  rw [cached_force_step first machine control cached,
    cached_force_step second machine control cached]

/-- Completed native values and stable faults survive every actual execution
path of the scoped source instance, including effects and later allocations. -/
theorem completed_cache_retained
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    {length : Nat} {initial final : NeedMachine Head Operation Effect StableFault NativeFault m}
    (execution : Steps (spec primitive) length initial final)
    {cell : CellId} {record : CellRecord (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (cached : initial.world.heap.lookup cell = some record)
    (completed : PrimeNeedCacheLaws.Cache.Completed record.cache) :
    final.world.heap.lookup cell = some record :=
  PrimeNeedCacheLaws.steps_preserve_completed (spec primitive) execution cached completed

#print axioms letNeed_allocate_step
#print axioms letNeed_allocated_suspended
#print axioms sequence_allocate_then_demand
#print axioms sequenceSigma_allocate_then_demand
#print axioms sigma_return_before_commit
#print axioms emit_step
#print axioms choice_force_step
#print axioms duplicate_choice_not_singleton
#print axioms cached_force_primitive_independent
#print axioms completed_cache_retained

end ScopedNeedMachine
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
