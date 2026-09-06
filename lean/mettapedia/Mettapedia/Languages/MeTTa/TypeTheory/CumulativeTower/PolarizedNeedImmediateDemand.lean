import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalAdequacy

/-!
# Immediate Need demand and returned-value sequencing

Both source forms allocate the same producer and immediately demand its cell.
The returned-value consumer preserves returned values and faults, but rejects
a computation-function answer. The raw correspondence therefore retains an
explicit answer projection. Independent returner typing removes that mismatch.

All correspondences keep the exact final world, including captured origins,
caches and receipts. They do not identify work, fuel or occurrence counts, nor
license erasing an allocation or eagerly forcing an unused suspension.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedImmediateDemand

open PrimeNeedReference PolarizedNeedMachine PolarizedNeedNaturalSemantics
open PolarizedNeed (Computation VTy)

variable {Head Operation Effect StableFault NativeFault : Type} {n v k m : Nat}

def immediateNeed (producer : Computation Head Operation Effect n v k) :
    Computation Head Operation Effect n v k := .letNeed producer (.forceNeed 0)

def immediateBindValue (producer : Computation Head Operation Effect n v k) :
    Computation Head Operation Effect n v k :=
  .bindValue producer (.returnValue (.variable 0))

/-- The existing returned-value consumer's polarity check, not a new evaluator. -/
def returnedProjection : Outcome Head Operation Effect StableFault NativeFault m →
    Outcome Head Operation Effect StableFault NativeFault m
  | .value (.returned value) => .value (.returned value)
  | .value (.nativeFunction _) => .retryableFault (.domain .expectedReturnedValue)
  | .value (.valueFunction _) => .retryableFault (.domain .expectedReturnedValue)
  | .stableFault fault => .stableFault fault
  | .retryableFault reason => .retryableFault reason

theorem returnedProjection_fault
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (fault : FaultOutcome outcome) : returnedProjection outcome = outcome := by
  cases fault <;> rfl

section Correspondence

variable {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
  {producer : Computation Head Operation Effect n v k} {native : Sub Head n m}
  {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
  {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
  {cell : CellId} {outcome : Outcome Head Operation Effect StableFault NativeFault m}

def need_of_force
    (allocation : world.allocate? ⟨n, v, k, producer, native, values, needs⟩ = some (allocated, cell))
    (forcing : Force primitive cell allocated outcome final) :
    Eval primitive ⟨n, v, k, immediateNeed producer, native, values, needs⟩ world outcome final :=
  .letNeed allocation (.forceNeed 0 forcing)

def bindValue_of_force
    (allocation : world.allocate? ⟨n, v, k, producer, native, values, needs⟩ = some (allocated, cell))
    (forcing : Force primitive cell allocated outcome final) :
    Eval primitive ⟨n, v, k, immediateBindValue producer, native, values, needs⟩ world
      (returnedProjection outcome) final := by
  cases outcome with
  | value answer =>
      cases answer with
      | returned value =>
          exact .bindValueValue allocation forcing
            (.returnValue (.variable 0) native (Fin.cases value values) needs final)
      | nativeFunction body =>
          exact .bindValueMismatch _ allocation forcing (by intro value equal; cases equal)
      | valueFunction body =>
          exact .bindValueMismatch _ allocation forcing (by intro value equal; cases equal)
  | stableFault fault => exact .bindValueFault _ allocation forcing (.stableFault fault)
  | retryableFault reason => exact .bindValueFault _ allocation forcing (.retryableFault reason)

/-- Transform an independent source derivation without changing its world. -/
def need_to_bindValue
    (evaluation : Eval primitive ⟨n, v, k, immediateNeed producer, native, values, needs⟩
      world outcome final) :
    Eval primitive ⟨n, v, k, immediateBindValue producer, native, values, needs⟩ world
      (returnedProjection outcome) final := by
  cases evaluation with
  | letNeed allocation body =>
      cases body with
      | forceNeed _ forcing => exact bindValue_of_force allocation forcing
  | letNeedAllocationFailure _ allocation =>
      exact .bindValueAllocationFailure _ allocation

theorem bindValue_to_need
    (evaluation : Eval primitive ⟨n, v, k, immediateBindValue producer, native, values, needs⟩
      world outcome final) :
    ∃ raw, Nonempty (Eval primitive
      ⟨n, v, k, immediateNeed producer, native, values, needs⟩ world raw final) ∧
      returnedProjection raw = outcome := by
  cases evaluation with
  | bindValueValue allocation forcing body =>
      cases body with
      | returnValue => exact ⟨_, ⟨need_of_force allocation forcing⟩, rfl⟩
  | bindValueMismatch _ allocation forcing mismatch =>
      refine ⟨_, ⟨need_of_force allocation forcing⟩, ?_⟩
      rename_i answer
      cases answer with
      | returned value => exact False.elim (mismatch value rfl)
      | nativeFunction body => rfl
      | valueFunction body => rfl
  | bindValueFault _ allocation forcing fault =>
      exact ⟨_, ⟨need_of_force allocation forcing⟩, returnedProjection_fault fault⟩
  | bindValueAllocationFailure _ allocation =>
      exact ⟨_, ⟨.letNeedAllocationFailure _ allocation⟩, rfl⟩

/-- Exact raw correspondence includes function-answer rejection explicitly. -/
theorem immediate_eval_iff :
    Nonempty (Eval primitive ⟨n, v, k, immediateBindValue producer, native, values, needs⟩
      world outcome final) ↔
      ∃ raw, Nonempty (Eval primitive
        ⟨n, v, k, immediateNeed producer, native, values, needs⟩ world raw final) ∧
        returnedProjection raw = outcome := by
  constructor
  · rintro ⟨evaluation⟩
    exact bindValue_to_need evaluation
  · rintro ⟨raw, ⟨evaluation⟩, rfl⟩
    exact ⟨need_to_bindValue evaluation⟩

theorem immediate_run_iff :
    RunSegment primitive world
      (.run (.evaluate ⟨n, v, k, immediateBindValue producer, native, values, needs⟩ .done) [])
      final (.halted outcome) ↔
      ∃ raw, RunSegment primitive world
        (.run (.evaluate ⟨n, v, k, immediateNeed producer, native, values, needs⟩ .done) [])
        final (.halted raw) ∧ returnedProjection raw = outcome := by
  simp only [← eval_iff_runSegment]
  exact immediate_eval_iff

end Correspondence

section Qualification

variable {R : Rules Head} {signature : ScopedComputation.OperationSignature Head Operation}
  {Δ : Ctx Head m} {types : CellTypes Head m} {A : VTy Head m}

/-- Source formation and producer admission independently qualify immediate
demand at any computation type, including a computation-function type. -/
theorem immediateNeed_typed {Γ : Ctx Head n}
    {sv : Fin v → VTy Head n} {sn : Fin k → PolarizedNeed.CTy Head n}
    {producer : Computation Head Operation Effect n v k} {B : PolarizedNeed.CTy Head n}
    (formed : PolarizedNeed.ComputationFormation R Γ B)
    (typed : PolarizedNeed.ComputationTyping R signature Γ sv sn producer B) :
    PolarizedNeed.ComputationTyping R signature Γ sv sn (immediateNeed producer) B :=
  .letNeed formed formed typed (.forceNeed 0)

/-- The returned-value form has the genuinely narrower source interface. -/
theorem immediateBindValue_typed {Γ : Ctx Head n}
    {sv : Fin v → VTy Head n} {sn : Fin k → PolarizedNeed.CTy Head n}
    {producer : Computation Head Operation Effect n v k} {B : VTy Head n}
    (formed : PolarizedNeed.ValueFormation R Γ B)
    (typed : PolarizedNeed.ComputationTyping R signature Γ sv sn producer (.returns B)) :
    PolarizedNeed.ComputationTyping R signature Γ sv sn
      (immediateBindValue producer) (.returns B) :=
  .bindValue formed (.returns formed) typed (.returnValue (.variable 0))

theorem returnedProjection_of_typed
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (typed : OutcomeTyping R signature Δ types (.returns A) outcome) :
    returnedProjection outcome = outcome := by
  cases typed with
  | value answer =>
      obtain ⟨value, rfl, _⟩ := answer.returned_payload
      rfl
  | stableFault fault => rfl
  | retryableFault reason allowed => rfl

variable {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
  {producer : Computation Head Operation Effect n v k} {native : Sub Head n m}
  {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
  {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
  {outcome : Outcome Head Operation Effect StableFault NativeFault m}

/-- Independent source and heap typing exclude a computation-function result
at a returner type. This does not assume the producer's cached denotation. -/
theorem returnedProjection_of_evaluation
    (evaluation : Eval primitive ⟨n, v, k, immediateNeed producer, native, values, needs⟩
      world outcome final)
    (sound : PrimitiveSoundness R signature Δ primitive)
    (source : ClosureTyping R signature Δ types
      ⟨n, v, k, immediateNeed producer, native, values, needs⟩ (.returns A))
    (heap : HeapTyping R signature Δ types world.heap) :
    returnedProjection outcome = outcome := by
  have initial : MachineTyping R signature Δ types
      (⟨world, .run (.evaluate ⟨n, v, k, immediateNeed producer, native, values, needs⟩ .done) [],
        {}⟩ : NeedMachine Head Operation Effect StableFault NativeFault m) (.returns A) :=
    ⟨heap, .run (.evaluate source (.done _)) (.nil _)⟩
  obtain ⟨_, _, _, typed⟩ := evaluation.final_world_typing sound initial
  exact returnedProjection_of_typed typed

theorem immediate_eval_iff_of_returner
    (sound : PrimitiveSoundness R signature Δ primitive)
    (source : ClosureTyping R signature Δ types
      ⟨n, v, k, immediateNeed producer, native, values, needs⟩ (.returns A))
    (heap : HeapTyping R signature Δ types world.heap) :
    Nonempty (Eval primitive ⟨n, v, k, immediateBindValue producer, native, values, needs⟩
      world outcome final) ↔
    Nonempty (Eval primitive ⟨n, v, k, immediateNeed producer, native, values, needs⟩
      world outcome final) := by
  rw [immediate_eval_iff]
  constructor
  · rintro ⟨raw, ⟨evaluation⟩, equal⟩
    rw [returnedProjection_of_evaluation evaluation sound source heap] at equal
    cases equal
    exact ⟨evaluation⟩
  · rintro ⟨evaluation⟩
    exact ⟨outcome, ⟨evaluation⟩, returnedProjection_of_evaluation evaluation sound source heap⟩

theorem immediate_run_iff_of_returner
    (sound : PrimitiveSoundness R signature Δ primitive)
    (source : ClosureTyping R signature Δ types
      ⟨n, v, k, immediateNeed producer, native, values, needs⟩ (.returns A))
    (heap : HeapTyping R signature Δ types world.heap) :
    RunSegment primitive world
      (.run (.evaluate ⟨n, v, k, immediateBindValue producer, native, values, needs⟩ .done) [])
      final (.halted outcome) ↔
    RunSegment primitive world
      (.run (.evaluate ⟨n, v, k, immediateNeed producer, native, values, needs⟩ .done) [])
      final (.halted outcome) := by
  rw [← eval_iff_runSegment, ← eval_iff_runSegment]
  exact immediate_eval_iff_of_returner sound source heap

end Qualification

namespace Controls

abbrev Source := Computation Nat Unit Nat 0 0 0
abbrev ExampleMachine := NeedMachine Nat Unit Nat Unit Unit 0

def primitive (_ : Unit) (term : Tm Nat 0) : Produced (Tm Nat 0) Unit Unit := .value term

def initial (source : Source) : ExampleMachine :=
  ⟨⟨0, [], .empty, .empty, 0, 0⟩,
    .run (.evaluate ⟨0, 0, 0, source, ids, Fin.elim0, Fin.elim0⟩ .done) [], {}⟩

def frontier (source : Source) : List ExampleMachine :=
  PrimeNeedLocalSteps.runFrontier (extension primitive) 24 [initial source]

def worldOutcomes (source : Source) :=
  (frontier source).map fun machine => (machine.world, haltedOutcome machine)

def nativeProducer : Source := .emit 7 (.returnValue (.native (.head 10)))
def thunkProducer : Source := .returnValue (.thunk nativeProducer)
def functionProducer : Source := .nativeLambda (.returnValue (.native (.var 0)))

theorem native_need_answer :
    (frontier (immediateNeed nativeProducer)).filterMap haltedOutcome =
      [.value (.returned (.native (.head 10)))] := by rfl

theorem native_worlds_agree :
    worldOutcomes (immediateNeed nativeProducer) =
      worldOutcomes (immediateBindValue nativeProducer) := by rfl

/-- The identical returned thunk closure is retained, not forced or classified
only by its outer constructor. -/
theorem thunk_worlds_agree :
    worldOutcomes (immediateNeed thunkProducer) =
      worldOutcomes (immediateBindValue thunkProducer) := by rfl

theorem thunk_need_answer :
    (frontier (immediateNeed thunkProducer)).filterMap haltedOutcome =
      [.value (.returned (.thunk nativeProducer ids Fin.elim0 Fin.elim0))] := by rfl

theorem function_need_answer :
    (frontier (immediateNeed functionProducer)).filterMap haltedOutcome =
      [.value (.nativeFunction ⟨0, 0, 0, .returnValue (.native (.var 0)),
        ids, Fin.elim0, Fin.elim0⟩)] := by rfl

theorem function_bind_rejected :
    (frontier (immediateBindValue functionProducer)).filterMap haltedOutcome =
      [.retryableFault (.domain .expectedReturnedValue)] := by rfl

/-- The consumer changes the observed polarity, not the producer's cached
function or its complete protocol world. -/
theorem function_final_worlds_agree :
    (frontier (immediateNeed functionProducer)).map (fun machine => machine.world) =
      (frontier (immediateBindValue functionProducer)).map (fun machine => machine.world) := by rfl

theorem unqualified_answer_equality_is_false :
    (frontier (immediateNeed functionProducer)).filterMap haltedOutcome ≠
      (frontier (immediateBindValue functionProducer)).filterMap haltedOutcome := by
  rw [function_need_answer, function_bind_rejected]
  intro impossible
  cases impossible

end Controls

#print axioms need_of_force
#print axioms bindValue_of_force
#print axioms need_to_bindValue
#print axioms bindValue_to_need
#print axioms immediate_eval_iff
#print axioms immediate_run_iff
#print axioms immediateNeed_typed
#print axioms immediateBindValue_typed
#print axioms returnedProjection_of_typed
#print axioms returnedProjection_of_evaluation
#print axioms immediate_eval_iff_of_returner
#print axioms immediate_run_iff_of_returner
#print axioms Controls.native_need_answer
#print axioms Controls.native_worlds_agree
#print axioms Controls.thunk_worlds_agree
#print axioms Controls.thunk_need_answer
#print axioms Controls.function_need_answer
#print axioms Controls.function_bind_rejected
#print axioms Controls.function_final_worlds_agree
#print axioms Controls.unqualified_answer_equality_is_false

end PolarizedNeedImmediateDemand
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
