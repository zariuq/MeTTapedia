import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedInvocationEvents

/-!
# Invocation-labelled segments of the existing polarized execution

Every edge is an actual Need/local transition. Labels are read from the
transition's original source control. Segment composition concatenates those
chronological observations while preserving complete worlds and controls.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.PolarizedNeedInvocation

open Mettapedia.Machines Mettapedia.Machines.BranchLocalNeed
open NeedReference PolarizedNeedMachine PolarizedNeed

variable {Head Operation Effect StableFault NativeFault : Type} {m n v k : Nat}

def base (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault) :
    OccurrenceMachineCore (NeedMachine Head Operation Effect StableFault NativeFault m)
      (NeedMachine Head Operation Effect StableFault NativeFault m)
      (Outcome Head Operation Effect StableFault NativeFault m) where
  load := id
  next := NeedLocalSteps.step (extension primitive)
  answer := haltedOutcome
  answer_final state answer returned := by
    cases control : state.control <;> simp [haltedOutcome, control, NeedLocalSteps.step, step] at returned ⊢

def RunSegment
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (control : NeedControl Head Operation Effect StableFault NativeFault m)
    (finalWorld : NeedWorld Head Operation Effect StableFault NativeFault m)
    (finalControl : NeedControl Head Operation Effect StableFault NativeFault m)
    (events : List (Event Head Operation Effect m)) : Prop :=
  ∀ work, ∃ length finalWork,
    OccurrenceObservation.Steps (base primitive) atState length events
      ⟨world, control, work⟩ ⟨finalWorld, finalControl, finalWork⟩

namespace RunSegment

variable {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
  {world middleWorld finalWorld : NeedWorld Head Operation Effect StableFault NativeFault m}
  {control middleControl finalControl : NeedControl Head Operation Effect StableFault NativeFault m}
  {firstEvents secondEvents : List (Event Head Operation Effect m)}

theorem refl (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (control : NeedControl Head Operation Effect StableFault NativeFault m) :
    RunSegment primitive world control world control [] := fun work => ⟨0, work, .refl _⟩

theorem trans (first : RunSegment primitive world control middleWorld middleControl firstEvents)
    (second : RunSegment primitive middleWorld middleControl finalWorld finalControl secondEvents) :
    RunSegment primitive world control finalWorld finalControl (firstEvents ++ secondEvents) := by
  intro work
  obtain ⟨n, middleWork, earlier⟩ := first work
  obtain ⟨k, finalWork, later⟩ := second middleWork
  exact ⟨n + k, finalWork, earlier.trans later⟩

theorem trans_empty (first : RunSegment primitive world control middleWorld middleControl firstEvents)
    (second : RunSegment primitive middleWorld middleControl finalWorld finalControl []) :
    RunSegment primitive world control finalWorld finalControl firstEvents := by
  simpa only [List.append_nil] using first.trans second

theorem of_step
    (successor : ∀ work, ∃ finalWork,
      Nonempty (NeedLocalSteps.StepOccurrence (extension primitive)
        ⟨world, control, work⟩ ⟨finalWorld, finalControl, finalWork⟩)) :
    RunSegment primitive world control finalWorld finalControl (atControl control) := by
  intro work
  obtain ⟨finalWork, ⟨occurrence⟩⟩ := successor work
  refine ⟨1, finalWork, ?_⟩
  simpa only [atState, List.append_nil] using
    (OccurrenceObservation.Steps.cons (base := base primitive) (emit := atState)
      occurrence.index occurrence.successorAt
        (.refl (⟨finalWorld, finalControl, finalWork⟩ : NeedMachine Head Operation Effect StableFault NativeFault m)))

theorem of_singleton {lookups updates receipts allocations : Nat}
    (successor : ∀ work,
      NeedLocalSteps.step (extension primitive)
          (⟨world, control, work⟩ : NeedMachine Head Operation Effect StableFault NativeFault m) =
        [finished ⟨world, control, work⟩ finalWorld finalControl lookups updates receipts allocations]) :
    RunSegment primitive world control finalWorld finalControl (atControl control) := by
  apply of_step
  intro work
  refine ⟨work.bump lookups updates receipts allocations, ⟨⟨0, ?_⟩⟩⟩
  simp only [successor work, List.getElem?_cons_zero, finished]

theorem local_unobserved
    (state next : Local Head Operation Effect StableFault NativeFault m)
    (selected : localStep state = some next) (stack : List (Frame (Resume Head Operation Effect m))) :
    atControl (.run state stack) = [] := by
  cases state with
  | demand cell token => rfl
  | complete result => rfl
  | evaluate closure kont =>
      rcases closure with ⟨n, v, k, code, native, values, needs⟩
      cases code <;> first | rfl | simp [localStep] at selected

variable (primitive)
  (world : NeedWorld Head Operation Effect StableFault NativeFault m)
  (stack : List (Frame (Resume Head Operation Effect m)))

theorem local_step (state next : Local Head Operation Effect StableFault NativeFault m)
    (selected : localStep state = some next) :
    RunSegment primitive world (.run state stack) world (.run next stack) [] := by
  rw [← local_unobserved state next selected stack]
  apply of_singleton (lookups := 0) (updates := 0) (receipts := 0) (allocations := 0)
  intro work
  exact NeedLocalSteps.step_local (extension primitive) _ rfl selected

theorem fallback (state : Local Head Operation Effect StableFault NativeFault m)
    (unhandled : localStep state = none)
    {lookups updates receipts allocations : Nat}
    (successor : ∀ work,
      NeedReference.step (reference primitive)
          (⟨world, .run state stack, work⟩ : NeedMachine Head Operation Effect StableFault NativeFault m) =
        [finished ⟨world, .run state stack, work⟩ finalWorld finalControl lookups updates receipts allocations]) :
    RunSegment primitive world (.run state stack) finalWorld finalControl (atControl (.run state stack)) := by
  apply of_singleton (lookups := lookups) (updates := updates) (receipts := receipts) (allocations := allocations)
  intro work
  rw [NeedLocalSteps.step_unhandled (extension primitive) _ rfl unhandled]
  exact successor work

theorem action_done (state : Local Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head Operation Effect StableFault NativeFault m)
    (unhandled : localStep state = none) (selected : action primitive state = .done outcome) :
    RunSegment primitive world (.run state stack) world (.returned outcome stack) (atControl (.run state stack)) := by
  apply fallback primitive world stack state unhandled (lookups := 0) (updates := 0) (receipts := 0) (allocations := 0)
  intro work
  simp only [NeedReference.step, reference, selected]

theorem allocation_unobserved (state : Local Head Operation Effect StableFault NativeFault m)
    (origin : Closure Head Operation Effect m) (token : Resume Head Operation Effect m)
    (selected : action primitive state = .allocate origin token) : atControl (.run state stack) = [] := by
  cases state with
  | demand cell token => rfl
  | complete result => rfl
  | evaluate closure kont =>
      rcases closure with ⟨n, v, k, code, native, values, needs⟩
      cases code <;> first | rfl | cases selected

theorem action_allocate (state : Local Head Operation Effect StableFault NativeFault m)
    (origin : Closure Head Operation Effect m) (token : Resume Head Operation Effect m)
    {nextWorld : NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    (unhandled : localStep state = none) (selected : action primitive state = .allocate origin token)
    (allocated : world.allocate? origin = some (nextWorld, cell)) :
    RunSegment primitive world (.run state stack) nextWorld (.run (afterAllocation token cell) stack) [] := by
  rw [← allocation_unobserved primitive stack state origin token selected]
  apply fallback primitive world stack state unhandled (lookups := 1) (updates := 1) (receipts := 1) (allocations := 1)
  intro work
  simp only [NeedReference.step, reference, selected, allocated]

theorem complete (outcome : Outcome Head Operation Effect StableFault NativeFault m) :
    RunSegment primitive world (.run (.complete outcome) stack) world (.returned outcome stack) [] :=
  action_done primitive world stack _ _ rfl rfl

theorem halt (outcome : Outcome Head Operation Effect StableFault NativeFault m) :
    RunSegment primitive world (.returned outcome []) world (.halted outcome) [] := by
  apply of_singleton (lookups := 0) (updates := 0) (receipts := 0) (allocations := 0)
  intro work
  rfl

theorem resume (token : Resume Head Operation Effect m) (outcome : Outcome Head Operation Effect StableFault NativeFault m) :
    RunSegment primitive world (.returned outcome (.resume token :: stack)) world (.run (afterDemand token outcome) stack) [] := by
  apply of_singleton (lookups := 0) (updates := 0) (receipts := 0) (allocations := 0)
  intro work
  rfl

theorem finish_resume (outcome : Outcome Head Operation Effect StableFault NativeFault m) (kont : Kont Head Operation Effect m) :
    RunSegment primitive world (.returned outcome (.resume (.finish kont) :: stack)) world (.run (deliver outcome kont) stack) [] :=
  resume primitive world stack (.finish kont) outcome

theorem bindNative_resume (body : NativeBody Head Operation Effect m) (value : Tm Head m) (kont : Kont Head Operation Effect m) :
    RunSegment primitive world (.returned (.value (.returned (.native value))) (.resume (.bindNative body kont) :: stack))
      world (.run (.evaluate (body.open value) kont) stack) [] :=
  resume primitive world stack (.bindNative body kont) (.value (.returned (.native value)))

theorem bindValue_resume (body : ValueBody Head Operation Effect m) (value : RuntimeValue Head Operation Effect m) (kont : Kont Head Operation Effect m) :
    RunSegment primitive world (.returned (.value (.returned value)) (.resume (.bindValue body kont) :: stack))
      world (.run (.evaluate (body.open value) kont) stack) [] :=
  resume primitive world stack (.bindValue body kont) (.value (.returned value))

theorem bindSigma_resume (body : NativeBody Head Operation Effect m) (value : Tm Head m) (kont : Kont Head Operation Effect m) :
    RunSegment primitive world (.returned (.value (.returned (.native value))) (.resume (.bindSigma body kont) :: stack))
      world (.run (.evaluate (body.open value) (.pair value kont)) stack) [] :=
  resume primitive world stack (.bindSigma body kont) (.value (.returned (.native value)))

theorem demand (cell : CellId) (token : Resume Head Operation Effect m) :
    RunSegment primitive world (.run (.demand cell token) stack) world (.force cell (.resume token :: stack)) [] := by
  apply fallback primitive world stack _ rfl (lookups := 0) (updates := 0) (receipts := 0) (allocations := 0)
  intro work
  rfl

theorem returnValue (value : Value Head Operation Effect n v k) (native : Sub Head n m)
    (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId) (kont : Kont Head Operation Effect m) :
    RunSegment primitive world (.run (.evaluate ⟨n, v, k, .returnValue value, native, values, needs⟩ kont) stack)
      world (.returned (finish (.value (.returned (captureValue native values needs value))) kont) stack) [] :=
  action_done primitive world stack _ _ rfl rfl

theorem call (operation : Operation) (argument : Tm Head n) (native : Sub Head n m)
    (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId) (kont : Kont Head Operation Effect m) :
    RunSegment primitive world (.run (.evaluate ⟨n, v, k, .call operation argument, native, values, needs⟩ kont) stack)
      world (.returned (finish (liftOutcome (primitive operation (subst native argument))) kont) stack)
      [.invoke operation (subst native argument)] := action_done primitive world stack _ _ rfl rfl

theorem emit (effect : Effect) (next : Computation Head Operation Effect n v k) (native : Sub Head n m)
    (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId) (kont : Kont Head Operation Effect m) :
    RunSegment primitive world (.run (.evaluate ⟨n, v, k, .emit effect next, native, values, needs⟩ kont) stack)
      (recorded world (.effect effect)) (.run (.evaluate ⟨n, v, k, next, native, values, needs⟩ kont) stack)
      [.emitted effect] := by
  apply fallback primitive world stack _ rfl (lookups := 0) (updates := 0) (receipts := 1) (allocations := 0)
  intro work
  rfl

theorem forceNeed (index : Fin k) (native : Sub Head n m)
    (values : Fin v → RuntimeValue Head Operation Effect m) (needs : Fin k → CellId) (kont : Kont Head Operation Effect m) :
    RunSegment primitive world (.run (.evaluate ⟨n, v, k, .forceNeed index, native, values, needs⟩ kont) stack)
      world (.force (needs index) (.resume (.finish kont) :: stack)) [] := by
  apply fallback primitive world stack _ rfl (lookups := 0) (updates := 0) (receipts := 0) (allocations := 0)
  intro work
  rfl

theorem cached_answer (cell : CellId) (origin : Closure Head Operation Effect m) (answer : Answer Head Operation Effect m)
    (cached : world.heap.lookup cell = some ⟨origin, .value answer⟩) :
    RunSegment primitive world (.force cell stack) (recorded world (.observe cell (.value answer)))
      (.returned (.value answer) stack) [] := by
  apply of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
  intro work
  exact cached_answer_step primitive _ rfl cached

end RunSegment

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.PolarizedNeedInvocation
