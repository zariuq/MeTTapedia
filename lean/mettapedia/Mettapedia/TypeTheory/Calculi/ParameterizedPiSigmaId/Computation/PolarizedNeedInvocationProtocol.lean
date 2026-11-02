import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedInvocationSegments
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedNaturalMachineLaws

/-!
# Event-free Need entry and finalization

These are actual protocol edges. Selecting a suspended producer and committing
its cached answer emit no primitive invocation or authored effect themselves.
The producer's separate execution retains those observations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.PolarizedNeedInvocation

open Mettapedia.Machines.BranchLocalNeed NeedReference PolarizedNeedMachine
open PolarizedNeedNaturalSemantics

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

theorem force_entry
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    {cell : CellId} {origin selected : Closure Head Operation Effect m}
    {position : Nat} {rule : Rule}
    (selection : Selection origin position rule selected)
    (suspended : world.heap.lookup cell = some ⟨origin, .suspended⟩) :
    RunSegment primitive world (.force cell stack)
      (enterWorld world cell origin position rule)
      (.run (.evaluate selected .done) (.commit cell world.nextEvaluator :: stack)) [] := by
  apply RunSegment.of_step
  intro work
  exact ⟨work.bump 1 1 2 0, ⟨⟨position, selection.force_entry_at primitive world stack suspended work⟩⟩⟩

theorem finalize_commit
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (cell : CellId) (owner : EvaluatorId) (outcome : Outcome Head Operation Effect StableFault NativeFault m) :
    RunSegment primitive world (.returned outcome (.commit cell owner :: stack))
      (finalize world cell owner outcome).2
      (.returned (finalize world cell owner outcome).1 stack) [] := by
  cases present : world.heap.lookup cell with
  | none =>
      apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
      intro work
      simp only [NeedLocalSteps.step, NeedReference.step, present, finalize,
        retryResult, retryMachine, finished, recorded]
  | some record =>
      cases cached : record.cache with
      | evaluating actual =>
          by_cases same : actual = owner
          · cases outcome <;>
              apply RunSegment.of_singleton (lookups := 1) (updates := 1) (receipts := 1) (allocations := 0) <;>
              intro work <;>
              simp only [NeedLocalSteps.step, NeedReference.step, present, cached,
                dif_pos same, finalize, if_pos same, retryResult, retryMachine, finished, recorded]
          · apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
            intro work
            simp only [NeedLocalSteps.step, NeedReference.step, present, cached,
              dif_neg same, finalize, if_neg same, retryResult, retryMachine, finished, recorded]
      | suspended | value _ | stableFault _ =>
          apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
          intro work
          simp only [NeedLocalSteps.step, NeedReference.step, present, cached, finalize,
            retryResult, retryMachine, finished, recorded]

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.PolarizedNeedInvocation
