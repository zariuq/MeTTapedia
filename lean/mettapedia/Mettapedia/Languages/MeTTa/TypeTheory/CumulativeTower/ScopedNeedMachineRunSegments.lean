import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedMachineLaws

/-!
# Composable exact-world segments of the scoped Need machine

A segment is a finite path of the existing occurrence-sensitive machine,
uniformly in the incoming work counters. Its endpoint retains the exact world
and control; only path length and outgoing work are existential. This interface
does not assert a cost bound, normalize payloads, choose a producer answer, or
define another evaluator. All consumer stacks and native continuations remain
explicit, including when a non-value outcome bypasses a native binder.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedMachine

open PrimeNeedReference
open ScopedNeedComputation (Code)

variable {Head Operation Effect NativeFault StableFault : Type} {m n k : Nat}

abbrev NeedControl (Head Operation Effect StableFault NativeFault : Type) (m : Nat) :=
  Control (Local Head Operation Effect StableFault NativeFault m)
    (Resume Head Operation Effect m) (Tm Head m) StableFault (Fault NativeFault)

def RunSegment
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (control : NeedControl Head Operation Effect StableFault NativeFault m)
    (finalWorld : NeedWorld Head Operation Effect StableFault NativeFault m)
    (finalControl : NeedControl Head Operation Effect StableFault NativeFault m) : Prop :=
  ∀ work, ∃ length finalWork,
    Steps (spec primitive) length ⟨world, control, work⟩ ⟨finalWorld, finalControl, finalWork⟩

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
  exact ⟨firstLength + secondLength, finalWork, earlier.trans (spec primitive) later⟩

theorem of_step
    (successor : ∀ work, ∃ finalWork,
      Nonempty (StepOccurrence (spec primitive) ⟨world, control, work⟩
        ⟨finalWorld, finalControl, finalWork⟩)) :
    RunSegment primitive world control finalWorld finalControl := by
  intro work
  obtain ⟨finalWork, ⟨occurrence⟩⟩ := successor work
  exact ⟨1, finalWork, .cons occurrence (.refl _)⟩

/-- Membership supplies a genuine successor occurrence; no multiplicity claim
is inferred from this existential path interface. -/
theorem of_mem
    (successor : ∀ work, ∃ finalWork,
      (⟨finalWorld, finalControl, finalWork⟩ : NeedMachine Head Operation Effect StableFault NativeFault m)
        ∈ step (spec primitive) ⟨world, control, work⟩) :
    RunSegment primitive world control finalWorld finalControl := by
  apply of_step
  intro work
  obtain ⟨finalWork, member⟩ := successor work
  obtain ⟨index, bounded, selected⟩ := List.mem_iff_getElem.mp member
  exact ⟨finalWork, ⟨⟨index, List.getElem?_eq_some_iff.mpr ⟨bounded, selected⟩⟩⟩⟩

theorem of_singleton {lookups updates receipts allocations : Nat}
    (successor : ∀ work,
      step (spec primitive) (⟨world, control, work⟩ : NeedMachine Head Operation Effect StableFault NativeFault m) =
        [finished ⟨world, control, work⟩ finalWorld finalControl lookups updates receipts allocations]) :
    RunSegment primitive world control finalWorld finalControl := by
  apply of_step
  intro work
  refine ⟨work.bump lookups updates receipts allocations, ⟨⟨0, ?_⟩⟩⟩
  simp only [successor work, List.getElem?_cons_zero, finished]

/-- Existential work counters do not license a transition out of a halt. -/
theorem halted_endpoint {outcome : Outcome Head StableFault NativeFault m}
    (execution : RunSegment primitive world (.halted outcome) finalWorld finalControl) :
    finalWorld = world ∧ finalControl = .halted outcome := by
  obtain ⟨length, finalWork, path⟩ := execution {}
  cases path with
  | refl => exact ⟨rfl, rfl⟩
  | cons occurrence _ =>
      have impossible := occurrence.mem (spec primitive)
      simp only [step, List.not_mem_nil] at impossible

theorem not_halted_fault_to_value (fault : StableFault) (value : Tm Head m) :
    ¬ RunSegment primitive world (.halted (.stableFault fault)) finalWorld (.halted (.value value)) := by
  intro execution
  have impossible := execution.halted_endpoint.2
  cases impossible

variable (primitive)
  (world : NeedWorld Head Operation Effect StableFault NativeFault m)
  (stack : List (Frame (Resume Head Operation Effect m)))

theorem complete (outcome : Outcome Head StableFault NativeFault m) :
    RunSegment primitive world (.run (.complete outcome) stack) world (.returned outcome stack) := by
  apply of_singleton
  intro work
  exact complete_step primitive _ outcome stack rfl

theorem halt (outcome : Outcome Head StableFault NativeFault m) :
    RunSegment primitive world (.returned outcome []) world (.halted outcome) := by
  apply of_singleton (lookups := 0) (updates := 0) (receipts := 0) (allocations := 0)
  intro work
  rfl

theorem resume (token : Resume Head Operation Effect m)
    (outcome : Outcome Head StableFault NativeFault m) :
    RunSegment primitive world (.returned outcome (.resume token :: stack)) world
      (.run (afterDemand token outcome) stack) := by
  apply of_singleton (lookups := 0) (updates := 0) (receipts := 0) (allocations := 0)
  intro work
  rfl

/-- The complete local consumer is traversed as well as its resume frame. -/
theorem finish_resume (outcome : Outcome Head StableFault NativeFault m) (kont : Kont Head m) :
    RunSegment primitive world (.returned outcome (.resume (.finish kont) :: stack)) world
      (.returned (finish outcome kont) stack) :=
  (resume primitive world stack (.finish kont) outcome).trans
    (complete primitive world stack (finish outcome kont))

theorem bindValue_resume (body : ValueBody Head Operation Effect m)
    (value : Tm Head m) (kont : Kont Head m) :
    RunSegment primitive world (.returned (.value value) (.resume (.bindValue body kont) :: stack))
      world (.run (.evaluate (body.open value) kont) stack) := by
  apply of_singleton
  intro work
  exact bindValue_resume_step primitive _ body value kont stack rfl

theorem bindSigma_resume (body : ValueBody Head Operation Effect m)
    (value : Tm Head m) (kont : Kont Head m) :
    RunSegment primitive world (.returned (.value value) (.resume (.bindSigma body kont) :: stack))
      world (.run (.evaluate (body.open value) (.pair value kont)) stack) := by
  apply of_singleton
  intro work
  exact bindSigma_resume_step primitive _ body value kont stack rfl

theorem bindValue_stableFault (body : ValueBody Head Operation Effect m)
    (fault : StableFault) (kont : Kont Head m) :
    RunSegment primitive world (.returned (.stableFault fault) (.resume (.bindValue body kont) :: stack))
      world (.returned (.stableFault fault) stack) :=
  (resume primitive world stack (.bindValue body kont) (.stableFault fault)).trans
    (complete primitive world stack (.stableFault fault))

theorem bindValue_retryableFault (body : ValueBody Head Operation Effect m)
    (reason : RetryReason (Fault NativeFault)) (kont : Kont Head m) :
    RunSegment primitive world (.returned (.retryableFault reason) (.resume (.bindValue body kont) :: stack))
      world (.returned (.retryableFault reason) stack) :=
  (resume primitive world stack (.bindValue body kont) (.retryableFault reason)).trans
    (complete primitive world stack (.retryableFault reason))

theorem bindSigma_stableFault (body : ValueBody Head Operation Effect m)
    (fault : StableFault) (kont : Kont Head m) :
    RunSegment primitive world (.returned (.stableFault fault) (.resume (.bindSigma body kont) :: stack))
      world (.returned (.stableFault fault) stack) :=
  (resume primitive world stack (.bindSigma body kont) (.stableFault fault)).trans
    (complete primitive world stack (.stableFault fault))

theorem bindSigma_retryableFault (body : ValueBody Head Operation Effect m)
    (reason : RetryReason (Fault NativeFault)) (kont : Kont Head m) :
    RunSegment primitive world (.returned (.retryableFault reason) (.resume (.bindSigma body kont) :: stack))
      world (.returned (.retryableFault reason) stack) :=
  (resume primitive world stack (.bindSigma body kont) (.retryableFault reason)).trans
    (complete primitive world stack (.retryableFault reason))

theorem demand (cell : CellId) (token : Resume Head Operation Effect m) :
    RunSegment primitive world (.run (.demand cell token) stack) world
      (.force cell (.resume token :: stack)) := by
  apply of_singleton
  intro work
  exact demand_step primitive _ cell token stack rfl

theorem returnValue (term : Tm Head n) (values : Sub Head n m) (needs : Fin k → CellId)
    (kont : Kont Head m) :
    RunSegment primitive world (.run (.evaluate ⟨n, k, .returnValue term, values, needs⟩ kont) stack)
      world (.returned (finish (.value (subst values term)) kont) stack) := by
  apply of_singleton
  intro work
  exact returnValue_step primitive _ term values needs kont stack rfl

theorem call (operation : Operation) (argument : Tm Head n)
    (values : Sub Head n m) (needs : Fin k → CellId) (kont : Kont Head m) :
    RunSegment primitive world (.run (.evaluate ⟨n, k, .call operation argument, values, needs⟩ kont) stack)
      world (.returned (finish (liftOutcome (primitive operation (subst values argument))) kont) stack) := by
  apply of_singleton
  intro work
  exact call_step primitive _ operation argument values needs kont stack rfl

theorem emit (effect : Effect) (next : Code Head Operation Effect n k)
    (values : Sub Head n m) (needs : Fin k → CellId) (kont : Kont Head m) :
    RunSegment primitive world (.run (.evaluate ⟨n, k, .emit effect next, values, needs⟩ kont) stack)
      (recorded world (.effect effect)) (.run (.evaluate ⟨n, k, next, values, needs⟩ kont) stack) := by
  apply of_singleton
  intro work
  exact emit_step primitive _ effect next values needs kont stack rfl

theorem force_reference (reference : Fin k) (values : Sub Head n m) (needs : Fin k → CellId)
    (kont : Kont Head m) :
    RunSegment primitive world (.run (.evaluate ⟨n, k, .force reference, values, needs⟩ kont) stack)
      world (.force (needs reference) (.resume (.finish kont) :: stack)) := by
  apply of_singleton
  intro work
  exact force_reference_step primitive _ reference values needs kont stack rfl

theorem action_allocate (state : Local Head Operation Effect StableFault NativeFault m)
    (origin : Closure Head Operation Effect m) (token : Resume Head Operation Effect m)
    {nextWorld : NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    (selected : action primitive state = .allocate origin token)
    (allocated : world.allocate? origin = some (nextWorld, cell)) :
    RunSegment primitive world (.run state stack) nextWorld (.run (afterAllocation token cell) stack) := by
  apply of_singleton (lookups := 1) (updates := 1) (receipts := 1) (allocations := 1)
  intro work
  simp only [step, spec, selected, allocated]

theorem letNeed_allocate (suspended : Code Head Operation Effect n k)
    (body : Code Head Operation Effect n (k + 1))
    (values : Sub Head n m) (needs : Fin k → CellId) (kont : Kont Head m)
    {nextWorld : NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    (allocated : world.allocate? ⟨n, k, suspended, values, needs⟩ = some (nextWorld, cell)) :
    RunSegment primitive world (.run (.evaluate ⟨n, k, .letNeed suspended body, values, needs⟩ kont) stack)
      nextWorld (.run (.evaluate ⟨n, k + 1, body, values, Fin.cases cell needs⟩ kont) stack) := by
  apply of_singleton
  intro work
  exact letNeed_allocate_step primitive _ suspended body values needs kont stack rfl allocated

/-- Explicit sequencing takes the actual allocation and separate demand steps. -/
theorem sequence_allocate (first : Code Head Operation Effect n k)
    (body : Code Head Operation Effect (n + 1) k)
    (values : Sub Head n m) (needs : Fin k → CellId) (kont : Kont Head m)
    {nextWorld : NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    (allocated : world.allocate? ⟨n, k, first, values, needs⟩ = some (nextWorld, cell)) :
    RunSegment primitive world (.run (.evaluate ⟨n, k, .sequence first body, values, needs⟩ kont) stack)
      nextWorld (.force cell (.resume (.bindValue ⟨n, k, body, values, needs⟩ kont) :: stack)) := by
  intro work
  exact ⟨2, _, (sequence_allocate_then_demand primitive _ first body values needs kont stack rfl allocated).toSteps _⟩

theorem sequenceSigma_allocate (first : Code Head Operation Effect n k)
    (body : Code Head Operation Effect (n + 1) k)
    (values : Sub Head n m) (needs : Fin k → CellId) (kont : Kont Head m)
    {nextWorld : NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    (allocated : world.allocate? ⟨n, k, first, values, needs⟩ = some (nextWorld, cell)) :
    RunSegment primitive world (.run (.evaluate ⟨n, k, .sequenceSigma first body, values, needs⟩ kont) stack)
      nextWorld (.force cell (.resume (.bindSigma ⟨n, k, body, values, needs⟩ kont) :: stack)) := by
  intro work
  exact ⟨2, _, (sequenceSigma_allocate_then_demand primitive _ first body values needs kont stack rfl allocated).toSteps _⟩

#print axioms trans
#print axioms of_mem
#print axioms not_halted_fault_to_value
#print axioms finish_resume
#print axioms bindValue_resume
#print axioms bindSigma_retryableFault
#print axioms returnValue
#print axioms call
#print axioms emit
#print axioms action_allocate
#print axioms sequenceSigma_allocate

end RunSegment

/-- Every member of the actual bounded frontier has an occurrence-sensitive
execution from one initial member, of length at most the fuel. Holding a state
with no successors and the all-halted early exit consume no actual step. -/
theorem runFrontier_reachable
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    {fuel : Nat} {states : List (NeedMachine Head Operation Effect StableFault NativeFault m)}
    {final : NeedMachine Head Operation Effect StableFault NativeFault m}
    (member : final ∈ runFrontier (spec primitive) fuel states) :
    ∃ initial ∈ states, ∃ length ≤ fuel, Steps (spec primitive) length initial final := by
  induction fuel generalizing states final with
  | zero => exact ⟨final, member, 0, Nat.le_refl 0, .refl _⟩
  | succ fuel ih =>
      by_cases stopped : states.all isHalted
      · simp only [runFrontier, stopped, ↓reduceIte] at member
        exact ⟨final, member, 0, Nat.zero_le _, .refl _⟩
      · simp only [runFrontier, stopped, Bool.false_eq_true, ↓reduceIte] at member
        obtain ⟨middle, advanced, length, bounded, path⟩ := ih member
        obtain ⟨initial, initialMember, advancedFrom⟩ := List.mem_flatMap.mp advanced
        cases successors : step (spec primitive) initial with
        | nil =>
            simp only [advance, successors, List.mem_singleton] at advancedFrom
            subst middle
            exact ⟨initial, initialMember, length,
              Nat.le_trans bounded (Nat.le_succ fuel), path⟩
        | cons first rest =>
            have successor : middle ∈ step (spec primitive) initial := by
              simpa only [advance, successors] using advancedFrom
            obtain ⟨index, inBounds, selected⟩ := List.mem_iff_getElem.mp successor
            have occurrence : StepOccurrence (spec primitive) initial middle :=
              ⟨index, List.getElem?_eq_some_iff.mpr ⟨inBounds, selected⟩⟩
            exact ⟨initial, initialMember, length + 1, Nat.succ_le_succ bounded,
              .cons occurrence path⟩

#print axioms runFrontier_reachable

end ScopedNeedMachine
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
