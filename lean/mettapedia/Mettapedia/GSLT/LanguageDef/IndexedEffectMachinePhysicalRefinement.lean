import Mettapedia.GSLT.LanguageDef.IndexedEffectMachineCompilation

/-!
# Physical refinement for generated indexed-effect plans

The generated storage-plan record and the native indexed-effect machine meet at
two independent boundaries.  First, a symbolic record is admitted only when it
selects the fixed generic effect ABI requested by the caller.  Second, the
native machine carries an unsigned 64-bit value-instruction counter and must
reject a full counter before invoking a value effect.

This module models those physical boundaries independently of any guest
language.  It proves exact symbolic-plan admission and a one-step refinement
from the counter-bearing physical machine to the abstract effect algebra.
-/

namespace Mettapedia.GSLT.LanguageDef.IndexedEffectMachinePhysicalRefinement

open IndexedInstructionStreamCompilation
open IndexedEffectMachineCompilation

/-! ## Generated symbolic plan and exact native admission -/

inductive UnknownPolicy where
  | reject
  | use
  deriving DecidableEq, Repr

/-- The nine payload fields of a generated indexed-effect-machine record. -/
structure GeneratedPlanRecord where
  operation : String
  actionIndex : UInt32
  machine : String
  carrier : String
  preparedEffect : String
  savedEffect : String
  saveEffect : String
  unknownPolicy : UnknownPolicy
  region : String
  deriving DecidableEq, Repr

/-- The exact selection made by a native call site.  The region and generic ABI
are retained from the generated record rather than repeated by the caller. -/
structure PlanRequest where
  operation : String
  actionIndex : UInt32
  machine : String
  unknownPolicy : UnknownPolicy
  region : String
  deriving DecidableEq, Repr

structure AdmittedPhysicalPlan where
  operation : String
  actionIndex : UInt32
  machine : String
  unknownPolicy : UnknownPolicy
  region : String
  deriving DecidableEq, Repr

def genericCarrier : String := "indexed-effect-machine-v1"
def genericPreparedEffect : String := "use-prepared-value-v1"
def genericSavedEffect : String := "use-saved-value-v1"
def genericSaveEffect : String := "save-top-value-v1"

/-- Decode the generated record into the vocabulary-neutral physical ABI.
Unknown carriers and effect codes fail closed. -/
def decodeGeneratedPlan? (record : GeneratedPlanRecord) :
    Option AdmittedPhysicalPlan :=
  if record.carrier != genericCarrier then none
  else if record.preparedEffect != genericPreparedEffect then none
  else if record.savedEffect != genericSavedEffect then none
  else if record.saveEffect != genericSaveEffect then none
  else some
    { operation := record.operation
      actionIndex := record.actionIndex
      machine := record.machine
      unknownPolicy := record.unknownPolicy
      region := record.region }

def admitsRequest (plan : AdmittedPhysicalPlan) (request : PlanRequest) : Bool :=
  plan.operation == request.operation &&
    plan.actionIndex == request.actionIndex &&
    plan.machine == request.machine &&
    plan.unknownPolicy == request.unknownPolicy &&
    plan.region == request.region

theorem decodeGeneratedPlan?_eq_some_iff
    (record : GeneratedPlanRecord) (plan : AdmittedPhysicalPlan) :
    decodeGeneratedPlan? record = some plan ↔
      record.carrier = genericCarrier ∧
      record.preparedEffect = genericPreparedEffect ∧
      record.savedEffect = genericSavedEffect ∧
      record.saveEffect = genericSaveEffect ∧
      plan =
        { operation := record.operation
          actionIndex := record.actionIndex
          machine := record.machine
          unknownPolicy := record.unknownPolicy
          region := record.region } := by
  simp only [decodeGeneratedPlan?]
  by_cases carrier : record.carrier = genericCarrier
  · simp [carrier]
    by_cases prepared : record.preparedEffect = genericPreparedEffect
    · simp [prepared]
      by_cases saved : record.savedEffect = genericSavedEffect
      · simp [saved]
        by_cases save : record.saveEffect = genericSaveEffect
        · simp [save, eq_comm]
        · simp [save]
      · simp [saved]
    · simp [prepared]
  · simp [carrier]

theorem admitsRequest_eq_true_iff
    (plan : AdmittedPhysicalPlan) (request : PlanRequest) :
    admitsRequest plan request = true ↔
      plan.operation = request.operation ∧
      plan.actionIndex = request.actionIndex ∧
      plan.machine = request.machine ∧
      plan.unknownPolicy = request.unknownPolicy ∧
      plan.region = request.region := by
  simp [admitsRequest, and_assoc]

/-! ## Exact counter-bearing physical effect step -/

inductive PhysicalExecutionError (Failure : Type) where
  | resource
  | indexOutOfRange (index : UInt64)
  | effect (failure : Failure)
  deriving DecidableEq, Repr

structure PhysicalState (State : Type) where
  logical : State
  valueInstructionLen : UInt64 := 0
  deriving DecidableEq, Repr

def counterFull (state : PhysicalState State) : Bool :=
  decide (state.valueInstructionLen.toNat = uint64MaxNat)

def instructionCarriesValue : Instruction -> Bool
  | .use _ => true
  | .unknown => true
  | .save => false

def incrementValueCount (instruction : Instruction)
    (state : PhysicalState State) (next : State) : PhysicalState State :=
  { logical := next
    valueInstructionLen :=
      if instructionCarriesValue instruction then
        UInt64.ofNat (state.valueInstructionLen.toNat + 1)
      else state.valueInstructionLen }

/-- Physical execution duplicates the native branch structure rather than
calling the abstract interpreter.  In particular, the resource guard precedes
table lookup and all user effects. -/
def executePhysicalInstruction
    (algebra : EffectAlgebra Prepared Saved State Failure)
    (state : PhysicalState State) (instruction : Instruction) :
    Except (PhysicalExecutionError Failure) (PhysicalState State) :=
  if instructionCarriesValue instruction && counterFull state then
    .error .resource
  else
    match instruction with
    | .use index =>
        let values := algebra.values state.logical
        match lookupSplit values.1 values.2 index with
        | none => .error (.indexOutOfRange index)
        | some (.prepared value) =>
            match algebra.usePrepared state.logical value with
            | .error failure => .error (.effect failure)
            | .ok next => .ok (incrementValueCount instruction state next)
        | some (.saved value) =>
            match algebra.useSaved state.logical value with
            | .error failure => .error (.effect failure)
            | .ok next => .ok (incrementValueCount instruction state next)
    | .save =>
        match algebra.saveTop state.logical with
        | .error failure => .error (.effect failure)
        | .ok next => .ok (incrementValueCount instruction state next)
    | .unknown =>
        match algebra.useUnknown state.logical with
        | .error failure => .error (.effect failure)
        | .ok next => .ok (incrementValueCount instruction state next)

def liftExecutionError : ExecutionError Failure -> PhysicalExecutionError Failure
  | .indexOutOfRange index => .indexOutOfRange index
  | .effect failure => .effect failure

/-- Below the physical counter boundary, one native effect step is exactly the
abstract effect step plus the independently specified counter update. -/
theorem executePhysicalInstruction_refines
    (algebra : EffectAlgebra Prepared Saved State Failure)
    (state : PhysicalState State) (instruction : Instruction)
    (capacity : instructionCarriesValue instruction = false ∨
      counterFull state = false) :
    executePhysicalInstruction algebra state instruction =
      match executeInstruction algebra state.logical instruction with
      | .error failure => .error (liftExecutionError failure)
      | .ok next => .ok (incrementValueCount instruction state next) := by
  cases instruction with
  | use index =>
      simp only [instructionCarriesValue, Bool.true_eq_false, false_or] at capacity
      simp only [executePhysicalInstruction, instructionCarriesValue, capacity,
        Bool.and_false, executeInstruction]
      cases splitEq : lookupSplit
          (algebra.values state.logical).1 (algebra.values state.logical).2 index with
      | none => simp [liftExecutionError]
      | some value =>
          cases value with
          | prepared prepared =>
              cases effectEq : algebra.usePrepared state.logical prepared <;>
                simp [effectEq, Except.mapError,
                  liftExecutionError]
          | saved saved =>
              cases effectEq : algebra.useSaved state.logical saved <;>
                simp [effectEq, Except.mapError,
                  liftExecutionError]
  | save =>
      simp only [executePhysicalInstruction, instructionCarriesValue,
        Bool.false_and, executeInstruction]
      cases effectEq : algebra.saveTop state.logical <;>
        simp [Except.mapError, liftExecutionError]
  | unknown =>
      simp only [instructionCarriesValue, Bool.true_eq_false, false_or] at capacity
      simp only [executePhysicalInstruction, instructionCarriesValue, capacity,
        Bool.and_false, executeInstruction]
      cases effectEq : algebra.useUnknown state.logical <;>
        simp [Except.mapError, liftExecutionError]

def advanceCounter (instruction : Instruction) (count : UInt64) : UInt64 :=
  if instructionCarriesValue instruction then
    UInt64.ofNat (count.toNat + 1)
  else count

def advanceCounters : UInt64 -> List Instruction -> UInt64
  | count, [] => count
  | count, instruction :: instructions =>
      advanceCounters (advanceCounter instruction count) instructions

def counterIsFull (count : UInt64) : Bool :=
  decide (count.toNat = uint64MaxNat)

/-- Capacity is a property of the instruction trace and physical counter, not
of the guest effect state.  It therefore remains stable when an effect changes
the logical state. -/
def CounterCapacity : UInt64 -> List Instruction -> Prop
  | _, [] => True
  | count, instruction :: instructions =>
      (instructionCarriesValue instruction = false ∨
        counterIsFull count = false) ∧
      CounterCapacity (advanceCounter instruction count) instructions

def executePhysicalInstructions
    (algebra : EffectAlgebra Prepared Saved State Failure) :
    PhysicalState State -> List Instruction ->
      Except (PhysicalExecutionError Failure) (PhysicalState State)
  | state, [] => .ok state
  | state, instruction :: instructions =>
      match executePhysicalInstruction algebra state instruction with
      | .error failure => .error failure
      | .ok next => executePhysicalInstructions algebra next instructions

theorem counterFull_eq_counterIsFull (state : PhysicalState State) :
    counterFull state = counterIsFull state.valueInstructionLen := by rfl

theorem incrementValueCount_eq_advanceCounter
    (instruction : Instruction) (state : PhysicalState State) (next : State) :
    incrementValueCount instruction state next =
      { logical := next
        valueInstructionLen :=
          advanceCounter instruction state.valueInstructionLen } := by
  cases instruction <;> rfl

/-- Every capacity-admitted physical instruction trace refines the abstract
effect trace.  Successful execution retains the exact final 64-bit count;
logical index/effect failures are preserved with no invented success case. -/
theorem executePhysicalInstructions_refines
    (algebra : EffectAlgebra Prepared Saved State Failure)
    (state : PhysicalState State) (instructions : List Instruction)
    (capacity : CounterCapacity state.valueInstructionLen instructions) :
    executePhysicalInstructions algebra state instructions =
      match executeInstructions algebra state.logical instructions with
      | .error failure => .error (liftExecutionError failure)
      | .ok next => .ok
          { logical := next
            valueInstructionLen :=
              advanceCounters state.valueInstructionLen instructions } := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instruction instructions inductionHypothesis =>
      rcases capacity with ⟨headCapacity, tailCapacity⟩
      have physicalCapacity :
          instructionCarriesValue instruction = false ∨
            counterFull state = false := by
        simpa [counterFull_eq_counterIsFull] using headCapacity
      rw [executePhysicalInstructions]
      rw [executePhysicalInstruction_refines
        algebra state instruction physicalCapacity]
      cases abstractStep : executeInstruction algebra state.logical instruction with
      | error failure =>
          simp only [executeInstructions]
          rw [abstractStep]
          rfl
      | ok next =>
          simp only [executeInstructions]
          rw [abstractStep]
          simp only [bind, Except.bind]
          rw [incrementValueCount_eq_advanceCounter]
          have tail := inductionHypothesis
            { logical := next
              valueInstructionLen :=
                advanceCounter instruction state.valueInstructionLen }
            tailCapacity
          simpa [advanceCounters] using tail

inductive PhysicalMachineError (Failure : Type) where
  | decode (failure : DecodeError)
  | execute (failure : PhysicalExecutionError Failure)
  deriving DecidableEq, Repr

/-- Online physical execution mirrors the native loop: decode one byte, apply
the emitted effect immediately, and retain both decoder and effect state. -/
def runPhysicalFusedBytesFrom
    (plan : Plan) (algebra : EffectAlgebra Prepared Saved State Failure) :
    DecoderState -> PhysicalState State -> List UInt8 ->
      Except (PhysicalMachineError Failure)
        (PhysicalState State × DecoderState)
  | decoder, state, [] => .ok (state, decoder)
  | decoder, state, byte :: bytes =>
      match feed plan decoder byte with
      | .error failure => .error (.decode failure)
      | .ok (none, nextDecoder) =>
          runPhysicalFusedBytesFrom plan algebra nextDecoder state bytes
      | .ok (some instruction, nextDecoder) =>
          match executePhysicalInstruction algebra state instruction with
          | .error failure => .error (.execute failure)
          | .ok next =>
              runPhysicalFusedBytesFrom plan algebra nextDecoder next bytes

/-- Given an independently admitted decoder trace, the native fused loop is
exactly decode-then-run on the physical instruction machine.  This theorem
also preserves the ordering of effect failures relative to later bytes. -/
theorem runPhysicalFusedBytesFrom_eq_execute_of_decode
    (plan : Plan) (algebra : EffectAlgebra Prepared Saved State Failure)
    (decoder : DecoderState) (state : PhysicalState State)
    (bytes : List UInt8) (instructions : List Instruction)
    (finalDecoder : DecoderState)
    (admitted : runBytesFrom plan decoder bytes =
      .ok (instructions, finalDecoder)) :
    runPhysicalFusedBytesFrom plan algebra decoder state bytes =
      match executePhysicalInstructions algebra state instructions with
      | .error failure => .error (.execute failure)
      | .ok finalState => .ok (finalState, finalDecoder) := by
  induction bytes generalizing decoder state instructions finalDecoder with
  | nil =>
      simp only [runBytesFrom] at admitted
      cases admitted
      rfl
  | cons byte bytes inductionHypothesis =>
      simp only [runBytesFrom] at admitted
      cases feedEq : feed plan decoder byte with
      | error failure =>
          simp only [feedEq] at admitted
          cases admitted
      | ok result =>
          simp only [feedEq] at admitted
          obtain ⟨event, nextDecoder⟩ := result
          cases tailEq : runBytesFrom plan nextDecoder bytes with
          | error failure =>
              simp only [tailEq] at admitted
              cases admitted
          | ok tailResult =>
              simp only [tailEq] at admitted
              obtain ⟨tail, tailDecoder⟩ := tailResult
              cases admitted
              cases event with
              | none =>
                  simpa only [runPhysicalFusedBytesFrom, feedEq,
                    Option.toList_none, List.nil_append] using
                    inductionHypothesis nextDecoder state tail tailDecoder tailEq
              | some instruction =>
                  simp only [Option.toList_some, List.singleton_append]
                  cases effectEq :
                      executePhysicalInstruction algebra state instruction with
                  | error failure =>
                      simp [runPhysicalFusedBytesFrom, feedEq, effectEq,
                        executePhysicalInstructions]
                  | ok next =>
                      have tailRun := inductionHypothesis nextDecoder next tail
                        tailDecoder tailEq
                      simp only [runPhysicalFusedBytesFrom, feedEq, effectEq]
                      simpa only [executePhysicalInstructions, effectEq] using
                        tailRun

/-- Composing decoder admission with the counter-bearing execution refinement
gives the exact abstract observation and the exact successful physical count. -/
theorem runPhysicalFusedBytesFrom_refines_abstract_of_decode
    (plan : Plan) (algebra : EffectAlgebra Prepared Saved State Failure)
    (decoder : DecoderState) (state : PhysicalState State)
    (bytes : List UInt8) (instructions : List Instruction)
    (finalDecoder : DecoderState)
    (admitted : runBytesFrom plan decoder bytes =
      .ok (instructions, finalDecoder))
    (capacity : CounterCapacity state.valueInstructionLen instructions) :
    runPhysicalFusedBytesFrom plan algebra decoder state bytes =
      match executeInstructions algebra state.logical instructions with
      | .error failure =>
          .error (.execute (liftExecutionError failure))
      | .ok finalState => .ok
          ({ logical := finalState
             valueInstructionLen :=
               advanceCounters state.valueInstructionLen instructions },
           finalDecoder) := by
  rw [runPhysicalFusedBytesFrom_eq_execute_of_decode
    plan algebra decoder state bytes instructions finalDecoder admitted]
  rw [executePhysicalInstructions_refines algebra state instructions capacity]
  cases executeInstructions algebra state.logical instructions <;> rfl

/-- Complete physical execution performs the same plan and open-index checks
as the native initializer/finalizer. -/
def runPhysicalMachine
    (plan : Plan) (algebra : EffectAlgebra Prepared Saved State Failure)
    (state : PhysicalState State) (chunks : List (List UInt8)) :
    Except (PhysicalMachineError Failure) (PhysicalState State) :=
  if plan.valid != true then .error (.decode .invalidPlan)
  else
    match runPhysicalFusedBytesFrom
        plan algebra initialState state chunks.flatten with
    | .error failure => .error failure
    | .ok (finalState, finalDecoder) =>
        match finalDecoder.phase with
        | .openIndex _ => .error (.decode .openIndexAtEnd)
        | .betweenUses | .justCompletedUse => .ok finalState

def fullCounterState (logical : State) : PhysicalState State :=
  { logical
    valueInstructionLen := UInt64.ofNat uint64MaxNat }

theorem fullCounterState_counterFull {State : Type} (logical : State) :
    counterFull (fullCounterState logical) = true := by
  rfl

/-- A full counter rejects a value use before even consulting the dynamic
table.  The theorem is polymorphic in the algebra, so no effect can distinguish
this refusal from an uncalled effect. -/
theorem use_at_full_counter_is_resource
    (algebra : EffectAlgebra Prepared Saved State Failure)
    (logical : State) (index : UInt64) :
    executePhysicalInstruction algebra (fullCounterState logical) (.use index) =
      .error .resource := by
  simp [executePhysicalInstruction, instructionCarriesValue,
    fullCounterState_counterFull]

theorem unknown_at_full_counter_is_resource
    (algebra : EffectAlgebra Prepared Saved State Failure)
    (logical : State) :
    executePhysicalInstruction algebra (fullCounterState logical) .unknown =
      .error .resource := by
  simp [executePhysicalInstruction, instructionCarriesValue,
    fullCounterState_counterFull]

/-! ## Structurally independent plan witnesses -/

private def firstRecord : GeneratedPlanRecord :=
  { operation := "alpha-operation"
    actionIndex := 4
    machine := "alpha-machine"
    carrier := genericCarrier
    preparedEffect := genericPreparedEffect
    savedEffect := genericSavedEffect
    saveEffect := genericSaveEffect
    unknownPolicy := .use
    region := "alpha-region" }

private def secondRecord : GeneratedPlanRecord :=
  { operation := "beta-operation"
    actionIndex := 17
    machine := "beta-machine"
    carrier := genericCarrier
    preparedEffect := genericPreparedEffect
    savedEffect := genericSavedEffect
    saveEffect := genericSaveEffect
    unknownPolicy := .reject
    region := "beta-region" }

example : decodeGeneratedPlan? firstRecord = some
    { operation := "alpha-operation"
      actionIndex := 4
      machine := "alpha-machine"
      unknownPolicy := .use
      region := "alpha-region" } := by decide

example : decodeGeneratedPlan? secondRecord = some
    { operation := "beta-operation"
      actionIndex := 17
      machine := "beta-machine"
      unknownPolicy := .reject
      region := "beta-region" } := by decide

example :
    (decodeGeneratedPlan? secondRecord).any fun plan =>
      admitsRequest plan
        { operation := "beta-operation"
          actionIndex := 17
          machine := "beta-machine"
          unknownPolicy := .reject
          region := "beta-region" } = true := by decide

example :
    (decodeGeneratedPlan? secondRecord).any fun plan =>
      admitsRequest plan
        { operation := "beta-operation"
          actionIndex := 17
          machine := "beta-machine"
          unknownPolicy := .reject
          region := "different-region" } = false := by decide

example : decodeGeneratedPlan?
    { secondRecord with carrier := "unadmitted-carrier" } = none := by decide

example : decodeGeneratedPlan?
    { secondRecord with savedEffect := "unadmitted-effect" } = none := by decide

end Mettapedia.GSLT.LanguageDef.IndexedEffectMachinePhysicalRefinement
