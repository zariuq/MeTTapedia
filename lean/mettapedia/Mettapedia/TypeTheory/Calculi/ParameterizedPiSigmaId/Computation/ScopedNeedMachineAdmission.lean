import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedComputationTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedMachineTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDependentComputation

/-!
# Native admission of actual cached Need results

A captured force obtains its displayed native result type from independent
source typing, a typed captured environment, and the actual heap invariant.
Successful lookup alone provides no native admission. Source conversion tails
are replayed with their formation premises after typed substitution.

The cached-step theorem concerns the existing machine's actual successor, and
the continuation theorem concerns its actual resume operation. The dependent
sharing example executes the machine with a genuine native Sigma result. These
are local admission results and a concrete execution, not preservation for every
control stack. The malformed-cache control makes that boundary explicit.
-/

open Mettapedia.Machines.BranchLocalNeed

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedNeedMachine

open NeedReference
open ScopedComputation (OperationSignature)

variable {Head Operation Effect StableFault NativeFault : Type} {n m k : Nat}
  {R : Rules Head} {signature : OperationSignature Head Operation} {Δ : Ctx Head m}

/-- Recover the captured force's complete displayed type, including conversion
tails. Its selected cache is independently admitted through the actual heap. -/
theorem ClosureTyping.cached_force_judgment
    {types : CellTypes Head m} {values : Sub Head n m} {needs : Fin k → CellId}
    {index : Fin k} {A value : Tm Head m}
    {origin : Closure Head Operation Effect m}
    {heap : Heap (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (source : ClosureTyping (Effect := Effect) R signature Δ types
      ⟨n, k, .force index, values, needs⟩ A)
    (context : FormationSensitive.ContextFormation R Δ)
    (heapTyped : HeapTyping R signature Δ types heap)
    (cached : heap.lookup (needs index) = some ⟨origin, .value value⟩) :
    FormationSensitive.Judgment R Δ value A := by
  cases source with
  | captured source environment references =>
      refine ⟨context, ?_⟩
      exact (source.substitute environment).force_replay rfl
        (heapTyped.cached_value (references index) cached)

/-- Every returned value of the actual cached-force step has the source
closure's displayed native judgment. Recording an observation does not change
the selected cached value, and cannot create its typing evidence. -/
theorem cached_force_result_judgment
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    {types : CellTypes Head m} {values : Sub Head n m} {needs : Fin k → CellId}
    {index : Fin k} {A value result : Tm Head m}
    {origin : Closure Head Operation Effect m}
    {machine next : NeedMachine Head Operation Effect StableFault NativeFault m}
    {stack : List (Frame (Resume Head Operation Effect m))}
    (source : ClosureTyping (Effect := Effect) R signature Δ types
      ⟨n, k, .force index, values, needs⟩ A)
    (context : FormationSensitive.ContextFormation R Δ)
    (heapTyped : HeapTyping R signature Δ types machine.world.heap)
    (control : machine.control = .force (needs index) stack)
    (cached : machine.world.heap.lookup (needs index) = some ⟨origin, .value value⟩)
    (successor : next ∈ step (spec primitive) machine)
    (returned : next.control = .returned (.value result) stack) :
    FormationSensitive.Judgment R Δ result A := by
  rw [cached_force_step primitive machine control cached, List.mem_singleton] at successor
  subst next
  have equal : value = result := by cases returned; rfl
  subst result
  exact source.cached_force_judgment context heapTyped cached

/-- Resume a typed native pair continuation with the actual cached result.
Only value outcomes yield native judgments; stable and retryable faults do not. -/
theorem cached_force_consumer_judgment
    {types : CellTypes Head m} {values : Sub Head n m} {needs : Fin k → CellId}
    {index : Fin k} {A B value result : Tm Head m}
    {origin : Closure Head Operation Effect m} {kont : Kont Head m}
    {heap : Heap (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (source : ClosureTyping (Effect := Effect) R signature Δ types
      ⟨n, k, .force index, values, needs⟩ A)
    (context : FormationSensitive.ContextFormation R Δ)
    (heapTyped : HeapTyping R signature Δ types heap)
    (cached : heap.lookup (needs index) = some ⟨origin, .value value⟩)
    (continuation : KontTyping R Δ kont A B)
    (resumed : afterDemand (.finish kont) (.value value) =
      (.complete (.value result) : Local Head Operation Effect StableFault NativeFault m)) :
    FormationSensitive.Judgment R Δ result B := by
  have input := source.cached_force_judgment context heapTyped cached
  have output : OutcomeTyping R Δ B
      (finish (.value value : Outcome Head StableFault NativeFault m) kont) :=
    continuation.finish_preserves (.value input.typing)
  have equal := Local.complete.inj resumed
  rw [equal] at output
  cases output with
  | value admitted => exact ⟨context, admitted⟩


#print axioms ClosureTyping.cached_force_judgment
#print axioms cached_force_result_judgment
#print axioms cached_force_consumer_judgment

end ScopedNeedMachine
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
