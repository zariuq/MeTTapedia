import Mettapedia.Languages.MeTTa.PrimeNeedLocalStepPaths
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedMachine

/-!
# Exact-world finite segments of the polarized Need candidate

Segments compose actual extended-machine paths uniformly in incoming work.
Returned values and computation-function answers are retained without a
native-only restriction. Silent interception and reference fallback have
separate premises: an authored action is executable only when the local
interceptor declines that state. No source natural semantics is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedMachine

open PrimeNeedReference
open PolarizedNeed (Value Computation)

variable {Head Operation Effect NativeFault StableFault : Type} {m n v k : Nat}

abbrev NeedControl (Head Operation Effect StableFault NativeFault : Type) (m : Nat) :=
  Control (Local Head Operation Effect StableFault NativeFault m)
    (Resume Head Operation Effect m) (Answer Head Operation Effect m) StableFault (Fault NativeFault)

def RunSegment
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (control : NeedControl Head Operation Effect StableFault NativeFault m)
    (finalWorld : NeedWorld Head Operation Effect StableFault NativeFault m)
    (finalControl : NeedControl Head Operation Effect StableFault NativeFault m) : Prop :=
  ∀ work, ∃ length finalWork,
    PrimeNeedLocalSteps.Steps (extension primitive) length
      ⟨world, control, work⟩ ⟨finalWorld, finalControl, finalWork⟩

namespace RunSegment

variable {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
  {world middleWorld finalWorld : NeedWorld Head Operation Effect StableFault NativeFault m}
  {control middleControl finalControl : NeedControl Head Operation Effect StableFault NativeFault m}

theorem refl (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (control : NeedControl Head Operation Effect StableFault NativeFault m) :
    RunSegment primitive world control world control :=
  fun work => ⟨0, work, .refl _⟩

theorem trans (first : RunSegment primitive world control middleWorld middleControl)
    (second : RunSegment primitive middleWorld middleControl finalWorld finalControl) :
    RunSegment primitive world control finalWorld finalControl := by
  intro work
  obtain ⟨firstLength, middleWork, earlier⟩ := first work
  obtain ⟨secondLength, finalWork, later⟩ := second middleWork
  exact ⟨firstLength + secondLength, finalWork, earlier.trans (extension primitive) later⟩

theorem of_step
    (successor : ∀ work, ∃ finalWork,
      Nonempty (PrimeNeedLocalSteps.StepOccurrence (extension primitive)
        ⟨world, control, work⟩ ⟨finalWorld, finalControl, finalWork⟩)) :
    RunSegment primitive world control finalWorld finalControl := by
  intro work
  obtain ⟨finalWork, ⟨occurrence⟩⟩ := successor work
  exact ⟨1, finalWork, .cons occurrence (.refl _)⟩

theorem of_mem
    (successor : ∀ work, ∃ finalWork,
      (⟨finalWorld, finalControl, finalWork⟩ : NeedMachine Head Operation Effect StableFault NativeFault m)
        ∈ PrimeNeedLocalSteps.step (extension primitive) ⟨world, control, work⟩) :
    RunSegment primitive world control finalWorld finalControl := by
  apply of_step
  intro work
  obtain ⟨finalWork, member⟩ := successor work
  exact ⟨finalWork, PrimeNeedLocalSteps.StepOccurrence.of_mem (extension primitive) member⟩

theorem of_singleton {lookups updates receipts allocations : Nat}
    (successor : ∀ work,
      PrimeNeedLocalSteps.step (extension primitive)
          (⟨world, control, work⟩ : NeedMachine Head Operation Effect StableFault NativeFault m) =
        [finished ⟨world, control, work⟩ finalWorld finalControl lookups updates receipts allocations]) :
    RunSegment primitive world control finalWorld finalControl := by
  apply of_step
  intro work
  refine ⟨work.bump lookups updates receipts allocations, ⟨⟨0, ?_⟩⟩⟩
  simp only [successor work, List.getElem?_cons_zero, finished]

theorem halted_endpoint {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (execution : RunSegment primitive world (.halted outcome) finalWorld finalControl) :
    finalWorld = world ∧ finalControl = .halted outcome := by
  obtain ⟨length, finalWork, path⟩ := execution {}
  have same := (path.halted_endpoint (extension primitive) rfl).1
  exact ⟨congrArg Machine.world same, congrArg Machine.control same⟩

theorem not_halted_fault_to_value (fault : StableFault) (answer : Answer Head Operation Effect m) :
    ¬ RunSegment primitive world (.halted (.stableFault fault)) finalWorld (.halted (.value answer)) := by
  intro execution
  have impossible := execution.halted_endpoint.2
  cases impossible

/-- Every completed segment occurs in some bounded actual answer frontier.
The segment itself supplies neither a uniform fuel bound nor exact cost. -/
theorem answers {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (execution : RunSegment primitive world control finalWorld (.halted outcome))
    (work : Work) :
    ∃ fuel, outcome ∈ PrimeNeedLocalSteps.answers (extension primitive) fuel ⟨world, control, work⟩ := by
  obtain ⟨length, finalWork, path⟩ := execution work
  exact ⟨length, (PrimeNeedLocalSteps.answers_iff_steps (extension primitive) length _ outcome).mpr
    ⟨length, Nat.le_refl _, finalWorld, finalWork, path⟩⟩

variable (primitive)
  (world : NeedWorld Head Operation Effect StableFault NativeFault m)
  (stack : List (Frame (Resume Head Operation Effect m)))

theorem local_step (state next : Local Head Operation Effect StableFault NativeFault m)
    (selected : localStep state = some next) :
    RunSegment primitive world (.run state stack) world (.run next stack) := by
  apply of_singleton (lookups := 0) (updates := 0) (receipts := 0) (allocations := 0)
  intro work
  exact PrimeNeedLocalSteps.step_local (extension primitive) _ rfl selected

/-- Reference-step equations can be reused only at unhandled local controls. -/
theorem fallback (state : Local Head Operation Effect StableFault NativeFault m)
    (unhandled : localStep state = none)
    {lookups updates receipts allocations : Nat}
    (successor : ∀ work,
      PrimeNeedReference.step (reference primitive)
          (⟨world, .run state stack, work⟩ : NeedMachine Head Operation Effect StableFault NativeFault m) =
        [finished ⟨world, .run state stack, work⟩ finalWorld finalControl lookups updates receipts allocations]) :
    RunSegment primitive world (.run state stack) finalWorld finalControl := by
  apply of_singleton (lookups := lookups) (updates := updates)
    (receipts := receipts) (allocations := allocations)
  intro work
  rw [PrimeNeedLocalSteps.step_unhandled (extension primitive) _ rfl unhandled]
  exact successor work

theorem action_done (state : Local Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head Operation Effect StableFault NativeFault m)
    (unhandled : localStep state = none) (selected : action primitive state = .done outcome) :
    RunSegment primitive world (.run state stack) world (.returned outcome stack) := by
  apply fallback primitive world stack state unhandled
    (lookups := 0) (updates := 0) (receipts := 0) (allocations := 0)
  intro work
  simp only [PrimeNeedReference.step, reference, selected]

theorem action_demand (state : Local Head Operation Effect StableFault NativeFault m)
    (cell : CellId) (token : Resume Head Operation Effect m)
    (unhandled : localStep state = none) (selected : action primitive state = .demand cell token) :
    RunSegment primitive world (.run state stack) world (.force cell (.resume token :: stack)) := by
  apply fallback primitive world stack state unhandled
    (lookups := 0) (updates := 0) (receipts := 0) (allocations := 0)
  intro work
  simp only [PrimeNeedReference.step, reference, selected]

theorem action_allocate (state : Local Head Operation Effect StableFault NativeFault m)
    (origin : Closure Head Operation Effect m) (token : Resume Head Operation Effect m)
    {nextWorld : NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    (unhandled : localStep state = none) (selected : action primitive state = .allocate origin token)
    (allocated : world.allocate? origin = some (nextWorld, cell)) :
    RunSegment primitive world (.run state stack) nextWorld (.run (afterAllocation token cell) stack) := by
  apply fallback primitive world stack state unhandled
    (lookups := 1) (updates := 1) (receipts := 1) (allocations := 1)
  intro work
  simp only [PrimeNeedReference.step, reference, selected, allocated]

theorem action_perform (state next : Local Head Operation Effect StableFault NativeFault m)
    (effect : Effect) (unhandled : localStep state = none)
    (selected : action primitive state = .perform effect next) :
    RunSegment primitive world (.run state stack) (recorded world (.effect effect)) (.run next stack) := by
  apply fallback primitive world stack state unhandled
    (lookups := 0) (updates := 0) (receipts := 1) (allocations := 0)
  intro work
  simp only [PrimeNeedReference.step, reference, selected]

theorem complete (outcome : Outcome Head Operation Effect StableFault NativeFault m) :
    RunSegment primitive world (.run (.complete outcome) stack) world (.returned outcome stack) :=
  action_done primitive world stack (.complete outcome) outcome rfl rfl

theorem halt (outcome : Outcome Head Operation Effect StableFault NativeFault m) :
    RunSegment primitive world (.returned outcome []) world (.halted outcome) := by
  apply of_singleton (lookups := 0) (updates := 0) (receipts := 0) (allocations := 0)
  intro work
  rfl

theorem resume (token : Resume Head Operation Effect m)
    (outcome : Outcome Head Operation Effect StableFault NativeFault m) :
    RunSegment primitive world (.returned outcome (.resume token :: stack)) world
      (.run (afterDemand token outcome) stack) := by
  apply of_singleton (lookups := 0) (updates := 0) (receipts := 0) (allocations := 0)
  intro work
  rfl

theorem finish_resume (outcome : Outcome Head Operation Effect StableFault NativeFault m)
    (kont : Kont Head Operation Effect m) :
    RunSegment primitive world (.returned outcome (.resume (.finish kont) :: stack)) world
      (.run (deliver outcome kont) stack) :=
  resume primitive world stack (.finish kont) outcome

theorem bindNative_resume (body : NativeBody Head Operation Effect m) (value : Tm Head m)
    (kont : Kont Head Operation Effect m) :
    RunSegment primitive world
      (.returned (.value (.returned (.native value))) (.resume (.bindNative body kont) :: stack))
      world (.run (.evaluate (body.open value) kont) stack) :=
  resume primitive world stack (.bindNative body kont) (.value (.returned (.native value)))

theorem bindValue_resume (body : ValueBody Head Operation Effect m)
    (value : RuntimeValue Head Operation Effect m) (kont : Kont Head Operation Effect m) :
    RunSegment primitive world (.returned (.value (.returned value)) (.resume (.bindValue body kont) :: stack))
      world (.run (.evaluate (body.open value) kont) stack) :=
  resume primitive world stack (.bindValue body kont) (.value (.returned value))

theorem bindSigma_resume (body : NativeBody Head Operation Effect m) (value : Tm Head m)
    (kont : Kont Head Operation Effect m) :
    RunSegment primitive world
      (.returned (.value (.returned (.native value))) (.resume (.bindSigma body kont) :: stack))
      world (.run (.evaluate (body.open value) (.pair value kont)) stack) :=
  resume primitive world stack (.bindSigma body kont) (.value (.returned (.native value)))

theorem demand (cell : CellId) (token : Resume Head Operation Effect m) :
    RunSegment primitive world (.run (.demand cell token) stack) world
      (.force cell (.resume token :: stack)) :=
  action_demand primitive world stack (.demand cell token) cell token rfl rfl

theorem returnValue (value : Value Head Operation Effect n v k) (native : Sub Head n m)
    (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId)
    (kont : Kont Head Operation Effect m) :
    RunSegment primitive world
      (.run (.evaluate ⟨n, v, k, .returnValue value, native, values, needs⟩ kont) stack)
      world (.returned (finish (.value (.returned (captureValue native values needs value))) kont) stack) :=
  action_done primitive world stack _ _ rfl rfl

theorem call (operation : Operation) (argument : Tm Head n) (native : Sub Head n m)
    (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId)
    (kont : Kont Head Operation Effect m) :
    RunSegment primitive world
      (.run (.evaluate ⟨n, v, k, .call operation argument, native, values, needs⟩ kont) stack)
      world (.returned (finish (liftOutcome (primitive operation (subst native argument))) kont) stack) :=
  action_done primitive world stack _ _ rfl rfl

theorem emit (effect : Effect) (next : Computation Head Operation Effect n v k) (native : Sub Head n m)
    (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId)
    (kont : Kont Head Operation Effect m) :
    RunSegment primitive world
      (.run (.evaluate ⟨n, v, k, .emit effect next, native, values, needs⟩ kont) stack)
      (recorded world (.effect effect)) (.run (.evaluate ⟨n, v, k, next, native, values, needs⟩ kont) stack) :=
  action_perform primitive world stack _ _ effect rfl rfl

theorem forceNeed (index : Fin k) (native : Sub Head n m)
    (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId)
    (kont : Kont Head Operation Effect m) :
    RunSegment primitive world
      (.run (.evaluate ⟨n, v, k, .forceNeed index, native, values, needs⟩ kont) stack)
      world (.force (needs index) (.resume (.finish kont) :: stack)) :=
  action_demand primitive world stack _ (needs index) (.finish kont) rfl rfl

theorem ordinary_force (code : Computation Head Operation Effect n v k) (native : Sub Head n m)
    (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId)
    (kont : Kont Head Operation Effect m) :
    RunSegment primitive world
      (.run (.evaluate ⟨n, v, k, .forceThunk (.thunk code), native, values, needs⟩ kont) stack)
      world (.run (.evaluate ⟨n, v, k, code, native, values, needs⟩ kont) stack) :=
  local_step primitive world stack _ _ rfl

theorem cached_answer (cell : CellId) (origin : Closure Head Operation Effect m)
    (answer : Answer Head Operation Effect m)
    (cached : world.heap.lookup cell = some ⟨origin, .value answer⟩) :
    RunSegment primitive world (.force cell stack)
      (recorded world (.observe cell (.value answer))) (.returned (.value answer) stack) := by
  apply of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
  intro work
  exact cached_answer_step primitive _ rfl cached

end RunSegment

#print axioms RunSegment.trans
#print axioms RunSegment.of_step
#print axioms RunSegment.of_mem
#print axioms RunSegment.of_singleton
#print axioms RunSegment.halted_endpoint
#print axioms RunSegment.not_halted_fault_to_value
#print axioms RunSegment.answers
#print axioms RunSegment.local_step
#print axioms RunSegment.fallback
#print axioms RunSegment.action_allocate
#print axioms RunSegment.finish_resume
#print axioms RunSegment.bindSigma_resume
#print axioms RunSegment.ordinary_force
#print axioms RunSegment.cached_answer

end PolarizedNeedMachine
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
