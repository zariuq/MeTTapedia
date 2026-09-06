import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedNaturalMachineLaws

/-!
# Source derivations implemented by the scoped Need machine

Natural evaluation is defined independently by source constructors and owned
heap observations. Its implementation theorem retains the exact final world,
including effects, choice occurrences and retry receipts. Native consumers
and outer stacks are arbitrary. Finite path length and work counters are
existential; this interface does not claim cost equivalence or termination.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedNaturalSemantics

open PrimeNeedReference ScopedNeedMachine
open ScopedNeedComputation (Code)

variable {Head Operation Effect StableFault NativeFault : Type} {m n k : Nat}
  {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}

theorem finish_pairOutcome (first : Tm Head m)
    (outcome : Outcome Head StableFault NativeFault m) (kont : Kont Head m) :
    finish (pairOutcome first outcome) kont = finish outcome (.pair first kont) := by
  cases outcome <;> simp only [pairOutcome, finish, finish_stableFault, finish_retryableFault]

private theorem allocate_failure_segment
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (state : Local Head Operation Effect StableFault NativeFault m)
    (origin : Closure Head Operation Effect m) (token : Resume Head Operation Effect m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (selected : action primitive state = .allocate origin token)
    (failed : world.allocate? origin = none) :
    RunSegment primitive world (.run state stack)
      (retryResult world (world.freshCell 0) (.allocationCollision (world.freshCell 0))).2
      (.returned (.retryableFault (.allocationCollision (world.freshCell 0))) stack) := by
  apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
  intro work
  simp only [step, spec, selected, failed, retryMachine, retryResult, recorded]

private theorem choose_allocate_segment
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (left right : Code Head Operation Effect n k)
    (values : Sub Head n m) (needs : Fin k → CellId) (kont : Kont Head m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    {allocated : NeedWorld Head Operation Effect StableFault NativeFault m} {cell : CellId}
    (allocation : world.allocate? ⟨n, k, .choose left right, values, needs⟩ = some (allocated, cell)) :
    RunSegment primitive world
      (.run (.evaluate ⟨n, k, .choose left right, values, needs⟩ kont) stack)
      allocated (.force cell (.resume (.finish kont) :: stack)) :=
  (RunSegment.action_allocate primitive world stack _ _ (.finish kont) rfl allocation).trans
    (RunSegment.demand primitive allocated stack cell (.finish kont))

private theorem cached_value_segment
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell : CellId) (origin : Closure Head Operation Effect m) (value : Tm Head m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (cached : world.heap.lookup cell = some ⟨origin, .value value⟩) :
    RunSegment primitive world (.force cell stack)
      (world.record (.observe cell (.value value))).1 (.returned (.value value) stack) := by
  apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
  intro work
  simp only [step, cached, recorded]

private theorem cached_stable_segment
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell : CellId) (origin : Closure Head Operation Effect m) (fault : StableFault)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (cached : world.heap.lookup cell = some ⟨origin, .stableFault fault⟩) :
    RunSegment primitive world (.force cell stack)
      (world.record (.observe cell (.stableFault fault))).1 (.returned (.stableFault fault) stack) := by
  apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
  intro work
  simp only [step, cached, recorded]

private theorem missing_segment
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell : CellId) (stack : List (Frame (Resume Head Operation Effect m)))
    (missing : world.heap.lookup cell = none) :
    RunSegment primitive world (.force cell stack)
      (retryResult world cell (.outOfScope cell)).2
      (.returned (.retryableFault (.outOfScope cell)) stack) := by
  apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
  intro work
  simp only [step, missing, retryMachine, retryResult, recorded]

private theorem evaluating_segment
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell : CellId) (origin : Closure Head Operation Effect m) (owner : EvaluatorId)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (evaluating : world.heap.lookup cell = some ⟨origin, .evaluating owner⟩) :
    RunSegment primitive world (.force cell stack)
      (retryResult world cell (.blackhole cell)).2
      (.returned (.retryableFault (.blackhole cell)) stack) := by
  apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
  intro work
  simp only [step, evaluating, retryMachine, retryResult, recorded]

mutual

/-- Each independent natural derivation has an actual machine path under any
native consumer and any outer stack, with the exact source-observed world. -/
theorem Eval.sound {origin : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m}
    (evaluation : Eval primitive origin world outcome final)
    (kont : Kont Head m) (stack : List (Frame (Resume Head Operation Effect m))) :
    RunSegment primitive world (.run (.evaluate origin kont) stack)
      final (.returned (finish outcome kont) stack) := by
  match evaluation with
  | .returnValue term values needs world =>
      exact RunSegment.returnValue primitive world stack term values needs kont
  | .call operation argument values needs world =>
      exact RunSegment.call primitive world stack operation argument values needs kont
  | .emit effect next =>
      exact (RunSegment.emit primitive _ stack effect _ _ _ kont).trans
        (Eval.sound next kont stack)
  | .force reference forced =>
      exact (RunSegment.force_reference primitive _ stack reference _ _ kont).trans
        ((Force.sound forced _).trans (RunSegment.finish_resume primitive _ stack _ kont))
  | .sequenceValue allocation producer consumer =>
      exact (RunSegment.sequence_allocate primitive _ stack _ _ _ _ kont allocation).trans
        ((Force.sound producer _).trans
          ((RunSegment.bindValue_resume primitive _ stack _ _ kont).trans
            (Eval.sound consumer kont stack)))
  | .sequenceStable body allocation producer =>
      simpa only [finish_stableFault] using
        (RunSegment.sequence_allocate primitive _ stack _ body _ _ kont allocation).trans
          ((Force.sound producer _).trans
            (RunSegment.bindValue_stableFault primitive _ stack _ _ kont))
  | .sequenceRetry body allocation producer =>
      simpa only [finish_retryableFault] using
        (RunSegment.sequence_allocate primitive _ stack _ body _ _ kont allocation).trans
          ((Force.sound producer _).trans
            (RunSegment.bindValue_retryableFault primitive _ stack _ _ kont))
  | .sequenceSigmaValue allocation producer consumer =>
      simpa only [finish_pairOutcome] using
        (RunSegment.sequenceSigma_allocate primitive _ stack _ _ _ _ kont allocation).trans
          ((Force.sound producer _).trans
            ((RunSegment.bindSigma_resume primitive _ stack _ _ kont).trans
              (Eval.sound consumer (.pair _ kont) stack)))
  | .sequenceSigmaStable body allocation producer =>
      simpa only [finish_stableFault] using
        (RunSegment.sequenceSigma_allocate primitive _ stack _ body _ _ kont allocation).trans
          ((Force.sound producer _).trans
            (RunSegment.bindSigma_stableFault primitive _ stack _ _ kont))
  | .sequenceSigmaRetry body allocation producer =>
      simpa only [finish_retryableFault] using
        (RunSegment.sequenceSigma_allocate primitive _ stack _ body _ _ kont allocation).trans
          ((Force.sound producer _).trans
            (RunSegment.bindSigma_retryableFault primitive _ stack _ _ kont))
  | .choose left right allocation producer =>
      exact (choose_allocate_segment _ left right _ _ kont stack allocation).trans
        ((Force.sound producer _).trans (RunSegment.finish_resume primitive _ stack _ kont))
  | .letNeed allocation body =>
      exact (RunSegment.letNeed_allocate primitive _ stack _ _ _ _ kont allocation).trans
        (Eval.sound body kont stack)
  | .sequenceAllocationFailure body failed =>
      simpa only [retryResult, finish_retryableFault] using
        (allocate_failure_segment _ _ _ _ stack rfl failed)
  | .sequenceSigmaAllocationFailure body failed =>
      simpa only [retryResult, finish_retryableFault] using
        (allocate_failure_segment _ _ _ _ stack rfl failed)
  | .chooseAllocationFailure left right failed =>
      simpa only [retryResult, finish_retryableFault] using
        (allocate_failure_segment _ _ _ _ stack rfl failed)
  | .letNeedAllocationFailure body failed =>
      simpa only [retryResult, finish_retryableFault] using
        (allocate_failure_segment _ _ _ _ stack rfl failed)
termination_by structural evaluation

/-- Forcing implements the natural shared-cell judgment, including owned
producer evaluation and its observed commit or retry result. -/
theorem Force.sound {cell : CellId}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m}
    (forcing : Force primitive cell world outcome final)
    (stack : List (Frame (Resume Head Operation Effect m))) :
    RunSegment primitive world (.force cell stack) final (.returned outcome stack) := by
  match forcing with
  | .cachedValue cached => exact cached_value_segment _ _ _ _ stack cached
  | .cachedStable cached => exact cached_stable_segment _ _ _ _ stack cached
  | .missing missing => exact missing_segment _ _ stack missing
  | .evaluating evaluating => exact evaluating_segment _ _ _ _ stack evaluating
  | .suspended suspended selection body =>
      exact (Selection.force_entry primitive _ stack selection suspended).trans
        ((Eval.sound body .done _).trans (finalize_commit primitive _ stack _ _ _))
termination_by structural forcing

end

/-- An independent source derivation yields a completed machine run. This is
the forward finite-evaluation direction, not an assumption of reflection. -/
theorem Eval.halts {origin : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m}
    (evaluation : Eval primitive origin world outcome final) :
    RunSegment primitive world (.run (.evaluate origin .done) []) final (.halted outcome) :=
  (evaluation.sound .done []).trans (RunSegment.halt primitive final outcome)

theorem Force.halts {cell : CellId}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m}
    (forcing : Force primitive cell world outcome final) :
    RunSegment primitive world (.force cell []) final (.halted outcome) :=
  (forcing.sound []).trans (RunSegment.halt primitive final outcome)

#print axioms finish_pairOutcome
#print axioms Eval.sound
#print axioms Force.sound
#print axioms Eval.halts
#print axioms Force.halts

end ScopedNeedNaturalSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
