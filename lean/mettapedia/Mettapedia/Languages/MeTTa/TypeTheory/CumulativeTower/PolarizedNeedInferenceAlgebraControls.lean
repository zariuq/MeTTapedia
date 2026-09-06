import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedInferenceAlgebra
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RawInferenceMILWorkload

/-!
# Full-world controls for the interpreted checker function

The service's semantic application retains the actual lexical cache origin,
the original caller world and the allocation/owned-observation effects. Pure
return of the same verdict is distinguishable. Raw malformed heaps exercise
allocation collision without replacing an existing cell. Independently formed
native data may fail decoding; an accepted nontrivial MIL chain supplies the
positive mathematical input. These controls do not equate Data formation with
logical acceptance, interpret all source programs, or erase cache identity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace PolarizedNeedInferenceAlgebra.Controls

open Presentation PrimeNeedReference
open Presentation.PolarizedNeed Presentation.PolarizedNeedMachine
open Presentation.PolarizedNeedNaturalSemantics
open PolarizedNeedInferenceService PolarizedNeedInferenceFunction
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

variable {Effect : Type} {n m v k : Nat}

section Worlds

variable (definition : ValidatedCalculusLanguageDef) (scope : Scope) (expected : Request)
  (native : Sub Tower.Head n m)
  (values : Fin v → RuntimeValue Tower.Head Operation Effect m) (needs : Fin k → CellId)
  (argument : Tower.Tm m)

theorem allocated_result_cache {world allocated : ServiceWorld Effect m} {cell : CellId}
    (allocation : world.allocate? (nativeOrigin argument native values needs) = some (allocated, cell)) :
    (applicationResult definition scope expected native values needs argument world).2.heap.lookup cell =
      some ⟨nativeOrigin argument native values needs,
        .value (.returned (.native (NativeWireData.encode (nativeReply definition scope argument))))⟩ := by
  simp only [applicationResult, allocation]
  exact replyWorld_cached _ _ _ _

theorem allocated_result_counter {world allocated : ServiceWorld Effect m} {cell : CellId}
    (allocation : world.allocate? (nativeOrigin argument native values needs) = some (allocated, cell)) :
    (applicationResult definition scope expected native values needs argument world).2.nextCell =
      world.nextCell + 1 := by
  simp only [applicationResult, allocation]
  change allocated.nextCell = world.nextCell + 1
  exact World.allocate?_nextCell allocation

/-- The original lexical scope remains in the stored source, even if its
unused environment does not affect the checker verdict. -/
theorem lexical_origin_not_closed (closed : Closure Tower.Head Operation Effect m)
    (closedScope : closed.n = 0) : nativeOrigin argument native values needs ≠ closed := by
  intro same
  have sizes := congrArg (fun closure : Closure Tower.Head Operation Effect m => closure.n) same
  change n + 1 = closed.n at sizes
  rw [closedScope] at sizes
  omega

theorem allocated_result_not_closed_cache {world allocated : ServiceWorld Effect m} {cell : CellId}
    (allocation : world.allocate? (nativeOrigin argument native values needs) = some (allocated, cell))
    (closed : Closure Tower.Head Operation Effect m) (closedScope : closed.n = 0)
    (cache : Cache (Answer Tower.Head Operation Effect m) Empty) :
    (applicationResult definition scope expected native values needs argument world).2.heap.lookup cell ≠
      some ⟨closed, cache⟩ := by
  rw [allocated_result_cache definition scope expected native values needs argument allocation]
  intro same
  exact lexical_origin_not_closed native values needs argument closed closedScope
    (congrArg CellRecord.origin (Option.some.inj same))

/-- Returning the exact same raw result does not reproduce the owned service
effects. This distinguishes whole ordered semantic worlds, not a cost model. -/
theorem allocation_is_not_pure_return {world allocated : ServiceWorld Effect m} {cell : CellId}
    (allocation : world.allocate? (nativeOrigin argument native values needs) = some (allocated, cell)) :
    runWorlds (applicationProgram definition scope expected native values needs argument) world ≠
      runWorlds (Program.pure
        (applicationResult definition scope expected native values needs argument world).1) world := by
  intro same
  rw [runWorlds, applicationProgram_worlds] at same
  change [_] = [_] at same
  have worlds := congrArg WorldResult.state (List.cons.inj same).1
  have counters := congrArg World.nextCell worlds
  rw [allocated_result_counter definition scope expected native values needs argument allocation] at counters
  omega

/-- A collision leaves the old heap untouched and appends a retry receipt. -/
theorem collision_preserves_heap_and_records_retry (world : ServiceWorld Effect m)
    (collision : world.allocate? (nativeOrigin argument native values needs) = none) :
    (applicationResult definition scope expected native values needs argument world).2.heap = world.heap ∧
      (applicationResult definition scope expected native values needs argument world).2.receipts.nodes.head?.map
        ReceiptNode.payload = some (.retry (world.freshCell 0) (.allocationCollision (world.freshCell 0))) := by
  simp only [applicationResult, collision, allocationFailure, retryResult, World.record,
    ReceiptGraph.append, List.head?_cons, Option.map_some]
  exact ⟨rfl, rfl⟩

theorem collision_program_worlds (world : ServiceWorld Effect m)
    (collision : world.allocate? (nativeOrigin argument native values needs) = none) :
    runWorlds (applicationProgram definition scope expected native values needs argument) world =
      [{ branch := [], answer := (allocationFailure world).1, state := (allocationFailure world).2,
         intents := [] }] := by
  rw [runWorlds, applicationProgram_worlds]
  simp only [applicationResult, collision]

theorem allocated_machine_result {world allocated : ServiceWorld Effect m} {cell : CellId}
    (allocation : world.allocate? (nativeOrigin argument native values needs) = some (allocated, cell)) :
    RunSegment (primitive definition scope) world
      (.run (.evaluate (openedFunction expected argument native values needs) .done) [])
      (replyWorld allocated cell (nativeOrigin argument native values needs) (nativeReply definition scope argument))
      (.halted (replyOutcome (nativeQualification definition scope expected argument))) :=
  eval_iff_runSegment.mp
    (opened_evaluates_of_allocation definition scope expected argument native values needs allocation)

end Worlds

section Malformed

variable (definition : ValidatedCalculusLanguageDef) (scope : Scope) (expected : Request)

theorem undecoded_native_reply (argument : Tower.Tm m) (undecoded : NativeWireData.decode argument = none) :
    nativeReply definition scope argument = RawInferenceService.encodeVerdict .malformed := by
  simp only [nativeReply, undecoded, Option.bind_none, Option.getD_none]

theorem undecoded_native_qualification (argument : Tower.Tm m)
    (undecoded : NativeWireData.decode argument = none) :
    nativeQualification definition scope expected argument = admissionVerdict none := by
  rw [nativeQualification, undecoded_native_reply definition scope argument undecoded]
  rfl

/-- Formation of transport Data does not justify skipping structural decoding.
The same well-formed argument is covered by the actual semantic function. -/
theorem formed_malformed_argument :
    ∃ argument : Tower.Tm 0,
      FormationSensitive.Judgment NativeWireData.rules .nil argument NativeWireData.dataType ∧
      nativeReply definition scope argument = RawInferenceService.encodeVerdict .malformed ∧
      nativeQualification definition scope expected argument = admissionVerdict none := by
  obtain ⟨argument, formed, undecoded⟩ := NativeWireData.formed_data_need_not_decode
  exact ⟨argument, formed, undecoded_native_reply definition scope argument undecoded,
    undecoded_native_qualification definition scope expected argument undecoded⟩

end Malformed

section Concrete

def emptyWorld : ServiceWorld Nat 0 := ⟨8, [], .empty, .empty, 0, 0⟩

/-- An existing entry paired with a stale allocation counter, supplied as raw
world data. Its collision is intentionally outside the slot-bound invariant. -/
def collisionWorld (origin : Closure Tower.Head Operation Nat 0) : ServiceWorld Nat 0 :=
  { emptyWorld with heap :=
      { current := fun cell =>
          if cell = emptyWorld.freshCell 0 then some ⟨origin, .suspended⟩ else none,
        spine := [.allocate (emptyWorld.freshCell 0) origin] } }

theorem actual_collision (origin : Closure Tower.Head Operation Nat 0)
    (newOrigin : Closure Tower.Head Operation Nat 0) :
    (collisionWorld origin).allocate? newOrigin = none := by
  simp only [collisionWorld, World.allocate?, Heap.allocate?, Heap.lookup, World.freshCell,
    emptyWorld, ↓reduceIte]

def scope : Scope := ⟨23, 4⟩
def expected : Request := RawInferenceMILWorkload.request scope MILCheckedChain.alice MILCheckedChain.carol
def chainInput : Tower.Tm 0 := NativeWireData.encode
  (RawInferenceService.encodeCandidate
    (RawInferenceMILWorkload.candidate scope MILCheckedChain.alice MILCheckedChain.carol
      MILCheckedChain.grandparentProof))

theorem chain_qualification :
    nativeQualification MILCheckedChain.learned.target scope expected chainInput =
      admissionVerdict (some true) := by
  simp only [chainInput, nativeQualification_encoded, rawQualificationResult_candidate,
    qualificationResult, expected, RawInferenceMILWorkload.grandparent_service_accepted]

def priorWorld : ServiceWorld Nat 0 := (emptyWorld.record (.effect 41)).1

theorem actual_allocation :
    ∃ allocated cell,
      priorWorld.allocate? (nativeOrigin chainInput
        (Fin.elim0 : Sub Tower.Head 0 0) Fin.elim0 Fin.elim0) = some (allocated, cell) := by
  exact ⟨_, _, rfl⟩

/-- The positive service invocation retains earlier effects, its actual
native proof article in the cached reply, and all owned protocol receipts. -/
theorem chain_semantic_and_machine_result :
    ∃ allocated cell,
      priorWorld.allocate? (nativeOrigin chainInput
        (Fin.elim0 : Sub Tower.Head 0 0) Fin.elim0 Fin.elim0) = some (allocated, cell) ∧
      let final := replyWorld allocated cell (nativeOrigin chainInput
        (Fin.elim0 : Sub Tower.Head 0 0) Fin.elim0 Fin.elim0)
        (nativeReply MILCheckedChain.learned.target scope chainInput)
      runWorlds (application (service MILCheckedChain.learned.target scope expected
        (Fin.elim0 : Sub Tower.Head 0 0) Fin.elim0 Fin.elim0) chainInput) priorWorld =
        [{ branch := [], answer := replyOutcome (admissionVerdict (some true)), state := final, intents := [] }] ∧
      RunSegment (primitive MILCheckedChain.learned.target scope) priorWorld
        (.run (.evaluate (openedFunction expected chainInput
          (Fin.elim0 : Sub Tower.Head 0 0) Fin.elim0 Fin.elim0) .done) [])
        final (.halted (replyOutcome (admissionVerdict (some true)))) := by
  obtain ⟨allocated, cell, allocation⟩ := actual_allocation
  refine ⟨allocated, cell, allocation, ?_, ?_⟩
  · rw [application_service, runWorlds, applicationProgram_worlds]
    simp only [applicationResult, allocation, chain_qualification]
  · have run := allocated_machine_result MILCheckedChain.learned.target scope expected
      (Fin.elim0 : Sub Tower.Head 0 0) (Fin.elim0 : Fin 0 → RuntimeValue Tower.Head Operation Nat 0)
      Fin.elim0 chainInput allocation
    simpa only [chain_qualification] using run

end Concrete

#print axioms allocated_result_cache
#print axioms allocated_result_counter
#print axioms lexical_origin_not_closed
#print axioms allocated_result_not_closed_cache
#print axioms allocation_is_not_pure_return
#print axioms collision_preserves_heap_and_records_retry
#print axioms collision_program_worlds
#print axioms allocated_machine_result
#print axioms undecoded_native_reply
#print axioms undecoded_native_qualification
#print axioms formed_malformed_argument
#print axioms actual_collision
#print axioms chain_qualification
#print axioms actual_allocation
#print axioms chain_semantic_and_machine_result

end PolarizedNeedInferenceAlgebra.Controls
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
