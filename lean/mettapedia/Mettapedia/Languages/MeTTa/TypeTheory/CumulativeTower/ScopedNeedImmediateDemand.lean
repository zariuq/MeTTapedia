import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedNaturalAdequacy
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedMachineExamples

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

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedImmediateDemand

open PrimeNeedReference ScopedNeedMachine ScopedNeedNaturalSemantics
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

namespace Controls

open ScopedNeedMachineExamples

/-- Complete worlds and optional completed outcomes remain visible; this
projection discards only control details and work, not receipts or caches. -/
def worldOutcomes (source : Source) :=
  (frontier 16 source).map fun machine => (machine.world, haltedOutcome machine)

/-- An actual effectful nondeterministic producer exercises both distinct
source forms. Their complete worlds agree, not merely their native answers. -/
theorem immediate_choice_worlds :
    worldOutcomes (immediateNeed producer) = worldOutcomes (immediateSequence producer) := by
  cbv

theorem immediate_choice_effects :
    observations 16 (immediateNeed producer) =
      [(some (.value (.head 10)), [7]), (some (.value (.head 20)), [7])] := rfl

def plain : Source := .returnValue (.head 42)

def protocol (machine : ExampleMachine) : Nat × Nat × Nat :=
  (machine.world.nextCell, machine.world.nextEvaluator, machine.world.receipts.nextSerial)

/-- Even a raw return acquires an allocation, entry, selection and observation
when it is executed as an owned suspension. Direct evaluation does not. -/
theorem direct_and_suspended_protocols :
    (frontier 64 plain).map protocol = [(0, 0, 0)] ∧
      (frontier 64 (immediateNeed plain)).map protocol = [(1, 1, 4)] := ⟨rfl, rfl⟩

theorem suspension_erasure_changes_world :
    worldOutcomes (immediateNeed plain) ≠ worldOutcomes plain := by
  intro equal
  have counts := congrArg (fun results => results.map fun result => result.1.nextCell) equal
  change [1] = ([0] : List Nat) at counts
  cases counts

end Controls

namespace NativeControls

open ScopedNeedMachine.PreservationExamples

abbrev NativeOperation := ScopedNeedMachine.PreservationExamples.Operation

def first : Code Tower.Head NativeOperation Nat 2 0 := .call .retain older

def body {handles : Nat} : Code Tower.Head NativeOperation Nat 3 handles :=
  .call .reflexivity (.var 0)

def direct : Code Tower.Head NativeOperation Nat 2 0 := .sequenceSigma first body

/-- `sequenceSigma (force 0)` creates a second cell whose origin forwards to
the first one. It is not an allocation-free native value bind. -/
def forwarding : Code Tower.Head NativeOperation Nat 2 0 :=
  .letNeed first (.sequenceSigma (.force 0) body)

theorem direct_typed : ScopedNeedComputation.Typing Tower.rules signature context Fin.elim0
    direct (.sigma ground identityFamily) :=
  .sequenceSigma sigma_formed (.sort _)
    (.call (operation_formation .retain) (.var 1))
    (.call (operation_formation .reflexivity) (.var 0))

theorem forwarding_typed : ScopedNeedComputation.Typing Tower.rules signature context Fin.elim0
    forwarding (.sigma ground identityFamily) := by
  refine .letNeed (.headType .legacyGround) (.sort Tower.zero) sigma_formed (.sort _)
    (.call (operation_formation .retain) (.var 1)) ?_
  exact .sequenceSigma sigma_formed (.sort _) (.force 0)
    (.call (operation_formation .reflexivity) (.var 0))

def completed (source : Code Tower.Head NativeOperation Nat 2 0) :=
  runFrontier (spec primitive) 32 [initial source ids]

theorem dependent_answers_agree :
    (completed direct).filterMap haltedOutcome = [.value (.pair older (.refl older))] ∧
      (completed forwarding).filterMap haltedOutcome = [.value (.pair older (.refl older))] := ⟨rfl, rfl⟩

/-- Native dependent typing does not hide the extra protocol allocation. -/
theorem forwarding_adds_cell_and_receipts :
    (completed direct).map (fun machine => (machine.world.nextCell, machine.world.receipts.nextSerial)) =
      [(1, 4)] ∧
    (completed forwarding).map (fun machine => (machine.world.nextCell, machine.world.receipts.nextSerial)) =
      [(2, 8)] := ⟨rfl, rfl⟩

theorem forwarding_worlds_differ :
    (completed forwarding).map (fun machine => machine.world) ≠
      (completed direct).map (fun machine => machine.world) := by
  intro equal
  have counts := congrArg (fun worlds => worlds.map fun world => world.nextCell) equal
  change [2] = ([1] : List Nat) at counts
  cases counts

end NativeControls

#print axioms sequence_of_force
#print axioms need_of_force
#print axioms need_to_sequence
#print axioms sequence_to_need
#print axioms immediate_eval_iff
#print axioms immediate_run_iff
#print axioms need_result_typing
#print axioms Controls.immediate_choice_worlds
#print axioms Controls.immediate_choice_effects
#print axioms Controls.direct_and_suspended_protocols
#print axioms Controls.suspension_erasure_changes_world
#print axioms NativeControls.direct_typed
#print axioms NativeControls.forwarding_typed
#print axioms NativeControls.dependent_answers_agree
#print axioms NativeControls.forwarding_adds_cell_and_receipts
#print axioms NativeControls.forwarding_worlds_differ

end ScopedNeedImmediateDemand
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
