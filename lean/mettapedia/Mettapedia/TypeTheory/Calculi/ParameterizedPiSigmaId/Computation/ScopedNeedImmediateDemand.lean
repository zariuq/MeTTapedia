import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedNaturalAdequacy

/-!
# Immediate suspension demand and eager sequencing

Two different source forms allocate the same producer and demand it at the
same point: `letNeed producer (force 0)` and `sequence producer (return 0)`.
They have exactly the same completed source outcomes and worlds, including
failure status, selected branch, cache state and receipts. Actual machine
correspondence follows through the independently proved natural semantics.

This is not a license to pre-evaluate an unused suspension or erase its owned
cell. A source sequence that forces an existing handle allocates an additional
forwarding cell; its protocol world therefore differs even if its native
dependent pair agrees. Payloads remain raw native terms, not normalized CBPV
values. No full CBPV profile is selected here.
-/

open Mettapedia.Machines.BranchLocalNeed

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedNeedImmediateDemand

open NeedReference ScopedNeedMachine ScopedNeedNaturalSemantics
open ScopedNeedComputation (Code)

variable {Head Operation Effect StableFault NativeFault : Type} {n m k : Nat}

def immediateNeed (producer : Code Head Operation Effect n k) :
    Code Head Operation Effect n k := .letNeed producer (.force 0)

def immediateSequence (producer : Code Head Operation Effect n k) :
    Code Head Operation Effect n k := .sequence producer (.returnValue (.var 0))

/-- The identity consumer returns the selected native payload, including its
unchanged index when that payload later enters a dependent consumer. -/
def sequence_of_force
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {producer : Code Head Operation Effect n k} {values : Sub Head n m} {needs : Fin k → CellId}
    {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {outcome : Outcome Head StableFault NativeFault m}
    (allocation : world.allocate? ⟨n, k, producer, values, needs⟩ = some (allocated, cell))
    (forcing : Force primitive cell allocated outcome final) :
    Eval primitive ⟨n, k, immediateSequence producer, values, needs⟩ world outcome final := by
  cases outcome with
  | value value =>
      exact .sequenceValue allocation forcing (.returnValue (.var 0) (Fin.cases value values) needs final)
  | stableFault fault => exact .sequenceStable _ allocation forcing
  | retryableFault reason => exact .sequenceRetry _ allocation forcing

def need_of_force
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {producer : Code Head Operation Effect n k} {values : Sub Head n m} {needs : Fin k → CellId}
    {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {outcome : Outcome Head StableFault NativeFault m}
    (allocation : world.allocate? ⟨n, k, producer, values, needs⟩ = some (allocated, cell))
    (forcing : Force primitive cell allocated outcome final) :
    Eval primitive ⟨n, k, immediateNeed producer, values, needs⟩ world outcome final :=
  .letNeed allocation (.force 0 forcing)

/-- Transport a natural derivation, not an assumed agreement of observations. -/
def need_to_sequence
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {producer : Code Head Operation Effect n k} {values : Sub Head n m} {needs : Fin k → CellId}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m}
    (evaluation : Eval primitive ⟨n, k, immediateNeed producer, values, needs⟩ world outcome final) :
    Eval primitive ⟨n, k, immediateSequence producer, values, needs⟩ world outcome final := by
  cases evaluation with
  | letNeed allocation body =>
      cases body with
      | force _ forcing => exact sequence_of_force allocation forcing
  | letNeedAllocationFailure _ allocation => exact .sequenceAllocationFailure _ allocation

def sequence_to_need
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {producer : Code Head Operation Effect n k} {values : Sub Head n m} {needs : Fin k → CellId}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m}
    (evaluation : Eval primitive ⟨n, k, immediateSequence producer, values, needs⟩ world outcome final) :
    Eval primitive ⟨n, k, immediateNeed producer, values, needs⟩ world outcome final := by
  cases evaluation with
  | sequenceValue allocation forcing body =>
      cases body with
      | returnValue => exact need_of_force allocation forcing
  | sequenceStable _ allocation forcing => exact need_of_force allocation forcing
  | sequenceRetry _ allocation forcing => exact need_of_force allocation forcing
  | sequenceAllocationFailure _ allocation => exact .letNeedAllocationFailure _ allocation

theorem immediate_eval_iff
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {producer : Code Head Operation Effect n k} {values : Sub Head n m} {needs : Fin k → CellId}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m} :
    Nonempty (Eval primitive ⟨n, k, immediateNeed producer, values, needs⟩ world outcome final) ↔
      Nonempty (Eval primitive ⟨n, k, immediateSequence producer, values, needs⟩ world outcome final) :=
  ⟨fun ⟨evaluation⟩ => ⟨need_to_sequence evaluation⟩,
    fun ⟨evaluation⟩ => ⟨sequence_to_need evaluation⟩⟩

/-- Both actual source forms have the same exact-world completed runs. This
does not compare derivation counts, running frontiers or work counters. -/
theorem immediate_run_iff
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {producer : Code Head Operation Effect n k} {values : Sub Head n m} {needs : Fin k → CellId}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m} :
    RunSegment primitive world
      (.run (.evaluate ⟨n, k, immediateNeed producer, values, needs⟩ .done) []) final (.halted outcome) ↔
    RunSegment primitive world
      (.run (.evaluate ⟨n, k, immediateSequence producer, values, needs⟩ .done) []) final (.halted outcome) := by
  rw [← eval_iff_runSegment, ← eval_iff_runSegment]
  exact immediate_eval_iff

/-- Independent source typing on the eager form qualifies the actual lazy
form's same native result. No final heap invariant or result typing is assumed. -/
theorem need_result_typing
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {producer : Code Head Operation Effect n k} {values : Sub Head n m} {needs : Fin k → CellId}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m}
    {R : Rules Head} {signature : ScopedComputation.OperationSignature Head Operation}
    {Δ : Ctx Head m} {types : CellTypes Head m} {A : Tm Head m}
    (evaluation : Eval primitive ⟨n, k, immediateNeed producer, values, needs⟩ world outcome final)
    (sound : PrimitiveSoundness R signature Δ primitive)
    (source : ClosureTyping R signature Δ types
      ⟨n, k, immediateSequence producer, values, needs⟩ A)
    (heap : HeapTyping R signature Δ types world.heap) : OutcomeTyping R Δ A outcome :=
  (need_to_sequence evaluation).result_typing sound source heap


#print axioms sequence_of_force
#print axioms need_of_force
#print axioms need_to_sequence
#print axioms sequence_to_need
#print axioms immediate_eval_iff
#print axioms immediate_run_iff
#print axioms need_result_typing

end ScopedNeedImmediateDemand
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
