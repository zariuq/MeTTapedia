import Mettapedia.GSLT.LanguageDef.ExactArithmeticToC0

/-!
# Exact-arithmetic C instruction-array refinement

This module models the concrete instruction-array shape used by the first
exact-arithmetic C lowering.  The model is independent of the authored C0
patterns: slots, externals, instructions, program counters, and chronological
execution events are represented as ordinary Lean data and then related to
the C0 operational presentation.

The C event array records events in execution order.  C0 receipts are nested
with the newest event at the outside, so the representation map is an explicit
left fold.  Outcome equality alone is deliberately insufficient.

The external provider remains a separate adequacy boundary.  This file proves
the instruction and receipt representation, including every external outcome
class; it does not identify a concrete GMP implementation with the authored
external relation.
-/

namespace Mettapedia.GSLT.LanguageDef.ExactArithmeticC0IRRefinement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger

namespace IR

inductive ValueType where
  | exactInteger
  deriving DecidableEq, Repr

inductive SlotMode where
  | borrowedInput
  | borrowedMutableOutput
  deriving DecidableEq, Repr

structure Slot where
  type : ValueType
  mode : SlotMode
  deriving DecidableEq, Repr

structure BinaryExternal where
  linkName : String
  firstInputSlot : Nat
  secondInputSlot : Nat
  outputSlot : Nat
  deriving DecidableEq, Repr

inductive Instruction where
  | branchZero (slot zeroTarget nonzeroTarget : Nat)
  | callBinaryExternal
      (external valueTarget languageFaultTarget engineFaultTarget
        resourceFaultTarget : Nat)
  | returnValue
  | returnDeclined
  | returnLanguageFault
  | returnEngineFault
  | returnResourceFault
  deriving DecidableEq, Repr

structure Program where
  semanticName : String
  entryLinkName : String
  slots : List Slot
  externals : List BinaryExternal
  instructions : List Instruction
  entryInstruction : Nat
  deriving DecidableEq, Repr

inductive ExternalOutcome where
  | value
  | languageFault
  | engineFault
  | resourceFault
  deriving DecidableEq, Repr

inductive Outcome where
  | value
  | declined
  | languageFault
  | engineFault
  | resourceFault
  deriving DecidableEq, Repr

/-- The external event retains the instruction as the C receipt does, even
though authored C0 obtains the same program counter from the immediately
preceding step event. -/
inductive Event where
  | step (instruction : Nat)
  | external (instruction external : Nat) (outcome : ExternalOutcome)
  deriving DecidableEq, Repr

structure ExecutionReceipt where
  outcome : Outcome
  stepCount : Nat
  externalCallCount : Nat
  finalInstruction : Nat
  events : List Event
  deriving DecidableEq, Repr

inductive ExecutionResult where
  | success (receipt : ExecutionReceipt)
  | invalidProgram
  | stepLimit
  deriving DecidableEq, Repr

def exactSlots : List Slot := [
  { type := .exactInteger, mode := .borrowedInput },
  { type := .exactInteger, mode := .borrowedInput },
  { type := .exactInteger, mode := .borrowedMutableOutput }]

def entryLinkName : CoreOp → String
  | .add => "cetta_carithmetic0_add_v1"
  | .sub => "cetta_carithmetic0_sub_v1"
  | .mul => "cetta_carithmetic0_mul_v1"
  | .tquot => "cetta_carithmetic0_tquot_v1"
  | .fquot => "cetta_carithmetic0_fquot_v1"
  | .trem => "cetta_carithmetic0_trem_v1"
  | .frem => "cetta_carithmetic0_frem_v1"

def exactExternal (operation : CoreOp) : BinaryExternal := {
  linkName := ExactArithmeticToC0.targetLinkName operation
  firstInputSlot := 0
  secondInputSlot := 1
  outputSlot := 2
}

def totalInstructions : List Instruction := [
  .callBinaryExternal 0 1 2 3 4,
  .returnValue,
  .returnLanguageFault,
  .returnEngineFault,
  .returnResourceFault]

def guardedInstructions : List Instruction := [
  .branchZero 1 1 2,
  .returnDeclined,
  .callBinaryExternal 0 3 4 5 6,
  .returnValue,
  .returnLanguageFault,
  .returnEngineFault,
  .returnResourceFault]

/-- Handwritten bootstrap lowering corresponding field-for-field to the C
instruction-array representation. -/
def lowerProgram (operation : CoreOp) : Program := {
  semanticName := operation.name
  entryLinkName := entryLinkName operation
  slots := exactSlots
  externals := [exactExternal operation]
  instructions :=
    if operation.isPartial then guardedInstructions else totalInstructions
  entryInstruction := 0
}

theorem lowerProgram_exact_abi (operation : CoreOp) :
    (lowerProgram operation).semanticName = operation.name ∧
      (lowerProgram operation).entryLinkName = entryLinkName operation ∧
      (lowerProgram operation).slots = exactSlots ∧
      (lowerProgram operation).externals = [exactExternal operation] ∧
      (lowerProgram operation).entryInstruction = 0 := by
  simp [lowerProgram]

theorem lowerProgram_instruction_count (operation : CoreOp) :
    (lowerProgram operation).instructions.length =
      if operation.isPartial then 7 else 5 := by
  cases operation <;> rfl

def branchOracle (secondIsZero : Bool) (slot : Nat) : Bool :=
  decide (slot = 1) && secondIsZero

def exactIsZero (second : Int) : Nat → Bool :=
  branchOracle (decide (second = 0))

def externalTarget : ExternalOutcome →
    Nat → Nat → Nat → Nat → Nat
  | .value, valueTarget, _, _, _ => valueTarget
  | .languageFault, _, languageTarget, _, _ => languageTarget
  | .engineFault, _, _, engineTarget, _ => engineTarget
  | .resourceFault, _, _, _, resourceTarget => resourceTarget

def outcomeOfExternal : ExternalOutcome → Outcome
  | .value => .value
  | .languageFault => .languageFault
  | .engineFault => .engineFault
  | .resourceFault => .resourceFault

/-- Pure counterpart of the C reference loop.  The provider is represented by
two typed functions, so an out-of-range external outcome is unrepresentable.
Fuel exhaustion and malformed instruction targets remain explicit results. -/
def executeFrom (program : Program) (isZero : Nat → Bool)
    (callExternal : Nat → ExternalOutcome) :
    Nat → Nat → Nat → Nat → List Event → ExecutionResult
  | 0, _, _, _, _ => .stepLimit
  | fuel + 1, pc, stepCount, externalCallCount, events =>
      match program.instructions[pc]? with
      | none => .invalidProgram
      | some instruction =>
          let stepped := events ++ [.step pc]
          match instruction with
          | .branchZero slot zeroTarget nonzeroTarget =>
              executeFrom program isZero callExternal fuel
                (if isZero slot then zeroTarget else nonzeroTarget)
                (stepCount + 1) externalCallCount stepped
          | .callBinaryExternal external valueTarget languageTarget
              engineTarget resourceTarget =>
              let externalOutcome := callExternal external
              let next := externalTarget externalOutcome valueTarget
                languageTarget engineTarget resourceTarget
              executeFrom program isZero callExternal fuel next
                (stepCount + 1) (externalCallCount + 1)
                (stepped ++ [.external pc external externalOutcome])
          | .returnValue =>
              .success {
                outcome := .value
                stepCount := stepCount + 1
                externalCallCount := externalCallCount
                finalInstruction := pc
                events := stepped }
          | .returnDeclined =>
              .success {
                outcome := .declined
                stepCount := stepCount + 1
                externalCallCount := externalCallCount
                finalInstruction := pc
                events := stepped }
          | .returnLanguageFault =>
              .success {
                outcome := .languageFault
                stepCount := stepCount + 1
                externalCallCount := externalCallCount
                finalInstruction := pc
                events := stepped }
          | .returnEngineFault =>
              .success {
                outcome := .engineFault
                stepCount := stepCount + 1
                externalCallCount := externalCallCount
                finalInstruction := pc
                events := stepped }
          | .returnResourceFault =>
              .success {
                outcome := .resourceFault
                stepCount := stepCount + 1
                externalCallCount := externalCallCount
                finalInstruction := pc
                events := stepped }

def execute (program : Program) (isZero : Nat → Bool)
    (callExternal : Nat → ExternalOutcome) (stepLimit : Nat) :
    ExecutionResult :=
  executeFrom program isZero callExternal stepLimit
    program.entryInstruction 0 0 []

def targetInstruction (operation : CoreOp)
    (externalOutcome : ExternalOutcome) : Nat :=
  let base := if operation.isPartial then 3 else 1
  match externalOutcome with
  | .value => base
  | .languageFault => base + 1
  | .engineFault => base + 2
  | .resourceFault => base + 3

def expectedReceiptForZero (operation : CoreOp) (secondIsZero : Bool)
    (externalOutcome : ExternalOutcome) : ExecutionReceipt :=
  if operation.isPartial && secondIsZero then {
    outcome := .declined
    stepCount := 2
    externalCallCount := 0
    finalInstruction := 1
    events := [.step 0, .step 1]
  } else
    let callInstruction := if operation.isPartial then 2 else 0
    let target := targetInstruction operation externalOutcome
    {
      outcome := outcomeOfExternal externalOutcome
      stepCount := if operation.isPartial then 3 else 2
      externalCallCount := 1
      finalInstruction := target
      events :=
        (if operation.isPartial then [.step 0] else []) ++
          [.step callInstruction,
           .external callInstruction 0 externalOutcome,
           .step target]
    }

def expectedReceipt (operation : CoreOp) (second : Int)
    (externalOutcome : ExternalOutcome) : ExecutionReceipt :=
  expectedReceiptForZero operation (decide (second = 0)) externalOutcome

/-- Instruction execution itself depends on the typed provider answer, not on
the mathematical definition of exact integers. -/
theorem execute_lowerProgram_provider_exact
    (operation : CoreOp) (secondIsZero : Bool)
    (externalOutcome : ExternalOutcome) :
    execute (lowerProgram operation) (branchOracle secondIsZero)
        (fun _ => externalOutcome) 4 =
      .success
        (expectedReceiptForZero operation secondIsZero externalOutcome) := by
  cases operation <;> cases secondIsZero <;> cases externalOutcome <;> rfl

/-- All seven lowerings and all four provider outcome classes execute with
the exact C counters, final instruction, and chronological event sequence. -/
theorem execute_lowerProgram_exact
    (operation : CoreOp) (second : Int)
    (externalOutcome : ExternalOutcome) :
    execute (lowerProgram operation) (exactIsZero second)
        (fun _ => externalOutcome) 4 =
      .success (expectedReceipt operation second externalOutcome) := by
  exact execute_lowerProgram_provider_exact operation
    (decide (second = 0)) externalOutcome

/-- A limit below the required number of instructions fails rather than
installing a partial receipt. -/
theorem total_one_step_limit_fails
    (operation : CoreOp) (total : operation.isPartial = false)
    (second : Int) (externalOutcome : ExternalOutcome) :
    execute (lowerProgram operation) (exactIsZero second)
        (fun _ => externalOutcome) 1 = .stepLimit := by
  cases operation <;> simp_all [execute, executeFrom, lowerProgram,
    totalInstructions]

end IR

/-! ## Representation in the independently authored C0 presentation -/

private def a (head : String) (arguments : List Pattern := []) : Pattern :=
  .apply head arguments

private def natPattern : Nat → Pattern
  | 0 => a "c0:nat-zero"
  | n + 1 => a "c0:nat-succ" [natPattern n]

private def slotPattern (slot : Nat) : Pattern :=
  a "c0:slot-id" [natPattern slot]

private def labelPattern (label : Nat) : Pattern :=
  a "c0:label" [natPattern label]

private def externalPattern (external : Nat) : Pattern :=
  a "c0:external-id" [natPattern external]

private def faultPattern (name : String) : Pattern :=
  a "c0:fault" [a name]

private def instructionListPattern : List IR.Instruction → Pattern
  | [] => a "c0:instruction-nil"
  | instruction :: rest =>
      a "c0:instruction-cons"
        [instructionPattern instruction, instructionListPattern rest]
where
  instructionPattern : IR.Instruction → Pattern
    | .branchZero slot zeroTarget nonzeroTarget =>
        a "c0:branch-zero"
          [slotPattern slot, labelPattern zeroTarget,
           labelPattern nonzeroTarget]
    | .callBinaryExternal external valueTarget languageTarget
        engineTarget resourceTarget =>
        a "c0:call-binary"
          [externalPattern external, labelPattern valueTarget,
           labelPattern languageTarget, labelPattern engineTarget,
           labelPattern resourceTarget]
    | .returnValue => a "c0:return-value" [slotPattern 2]
    | .returnDeclined => a "c0:return-declined"
    | .returnLanguageFault =>
        a "c0:return-language-fault" [faultPattern "language-fault"]
    | .returnEngineFault =>
        a "c0:return-engine-fault" [faultPattern "engine-fault"]
    | .returnResourceFault =>
        a "c0:return-resource-fault" [faultPattern "resource-fault"]

private def externalListPattern : List IR.BinaryExternal → Pattern
  | [] => a "c0:external-nil"
  | declaration :: rest =>
      a "c0:external-cons"
        [a "c0:binary-external"
          [externalPattern 0, a declaration.linkName,
           slotPattern declaration.firstInputSlot,
           slotPattern declaration.secondInputSlot,
           slotPattern declaration.outputSlot],
         externalListPattern rest]

def programPattern (program : IR.Program) : Pattern :=
  a "c0:program"
    [instructionListPattern program.instructions,
     externalListPattern program.externals,
     labelPattern program.entryInstruction]

/-- The concrete instruction array denotes exactly the independently authored
C0 program term for every operation. -/
theorem lowerProgram_pattern_exact (operation : CoreOp) :
    programPattern (IR.lowerProgram operation) =
      ExactArithmeticToC0.compileCoreOperation operation := by
  cases operation <;> rfl

private def exactIntegerPattern (value : Int) : Pattern :=
  a "c0:exact-integer" [a (toString value)]

private def slotValuePattern (value : Pattern) : Pattern :=
  a "c0:slot-value" [value]

private def storePattern (first second output : Int) : Pattern :=
  a "c0:store-cons" [slotValuePattern (exactIntegerPattern first),
    a "c0:store-cons" [slotValuePattern (exactIntegerPattern second),
      a "c0:store-cons" [slotValuePattern (exactIntegerPattern output),
        a "c0:store-nil"]]]

def externalOutcomePattern (first second output : Int) :
    IR.ExternalOutcome → Pattern
  | .value => a "c0:external-value" [storePattern first second output]
  | .languageFault =>
      a "c0:external-language-fault" [faultPattern "language-fault"]
  | .engineFault =>
      a "c0:external-engine-fault" [faultPattern "engine-fault"]
  | .resourceFault =>
      a "c0:external-resource-fault" [faultPattern "resource-fault"]

def outcomePattern (output : Int) : IR.Outcome → Pattern
  | .value => a "c0:outcome-value" [exactIntegerPattern output]
  | .declined => a "c0:outcome-declined"
  | .languageFault =>
      a "c0:outcome-language-fault" [faultPattern "language-fault"]
  | .engineFault =>
      a "c0:outcome-engine-fault" [faultPattern "engine-fault"]
  | .resourceFault =>
      a "c0:outcome-resource-fault" [faultPattern "resource-fault"]

def eventPattern (first second output : Int) : IR.Event → Pattern
  | .step instruction => a "c0:step-event" [labelPattern instruction]
  | .external _ external externalOutcome =>
      a "c0:external-event"
        [externalPattern external,
         externalOutcomePattern first second output externalOutcome]

/-- Chronological C events become C0's newest-event-first nested receipt by a
left fold. -/
def receiptPattern (first second output : Int)
    (events : List IR.Event) : Pattern :=
  events.foldl
    (fun prior event =>
      a "c0:receipt-cons" [eventPattern first second output event, prior])
    (a "c0:receipt-nil")

def completionPattern (first second output : Int)
    (receipt : IR.ExecutionReceipt) : Pattern :=
  a "c0:halted"
    [outcomePattern output receipt.outcome,
     receiptPattern first second output receipt.events]

/-- Interpret a successful concrete execution as an authored C0 completion.
Validation, fuel exhaustion, and typed-provider failures do not masquerade as
guest-language completions. -/
def executionCompletionPattern (first second output : Int) :
    IR.ExecutionResult → Option Pattern
  | .success receipt => some (completionPattern first second output receipt)
  | .invalidProgram => none
  | .stepLimit => none

/-- Every provider outcome admitted by the typed instruction interpreter is
retained in the authored C0 outcome and receipt vocabulary.  Provider adequacy
is deliberately not assumed here. -/
theorem execute_lowerProgram_completion_exact
    (operation : CoreOp) (first second output : Int)
    (externalOutcome : IR.ExternalOutcome) :
    executionCompletionPattern first second output
        (IR.execute (IR.lowerProgram operation) (IR.exactIsZero second)
          (fun _ => externalOutcome) 4) =
      some (completionPattern first second output
        (IR.expectedReceipt operation second externalOutcome)) := by
  rw [IR.execute_lowerProgram_exact]
  rfl

/-- With an adequate value provider, the chronological C receipt maps exactly
to the authored C0 completion receipt for every defined operation input. -/
theorem value_receipt_refines_compiledC0
    (operation : CoreOp) (first second : Int)
    (defined : ¬ undefinedAt operation second) :
    receiptPattern first second (operation.fn first second)
        (IR.expectedReceipt operation second .value).events =
      ExactArithmeticToC0.compiledC0Receipt operation first second := by
  cases operation <;>
    simp_all [IR.expectedReceipt, IR.expectedReceiptForZero,
      IR.targetInstruction, receiptPattern,
      eventPattern, externalOutcomePattern, storePattern, slotValuePattern,
      exactIntegerPattern, faultPattern, externalPattern, labelPattern,
      natPattern, a, undefinedAt,
      ExactArithmeticToC0.compiledC0Receipt,
      ExactArithmeticToC0.targetUndefinedAt_iff,
      ExactArithmeticToC0.targetValue_eq,
      ExactArithmeticToC0.targetExternalValue,
      ExactArithmeticToC0.resultStore,
      ExactArithmeticToC0.store3, ExactArithmeticToC0.storeCons,
      ExactArithmeticToC0.storeNil, ExactArithmeticToC0.slotValue,
      ExactArithmeticToC0.exactIntegerValue,
      ExactArithmeticToC0.integerAtom, ExactArithmeticToC0.stepReceipt,
      ExactArithmeticToC0.externalReceipt, ExactArithmeticToC0.receiptNil,
      ExactArithmeticToC0.label, ExactArithmeticToC0.external,
      ExactArithmeticToC0.natPattern, ExactArithmeticToC0.a,
      CoreOp.fn, CoreOp.isPartial]

theorem value_outcome_refines_compiledC0
    (operation : CoreOp) (first second : Int)
    (defined : ¬ undefinedAt operation second) :
    outcomePattern (operation.fn first second) .value =
      ExactArithmeticToC0.compiledC0Outcome operation first second := by
  rw [ExactArithmeticToC0.compiledC0Outcome_commutes]
  simp [coreSem_neg defined, outcomePattern, exactIntegerPattern,
    ExactArithmeticToC0.exactIntegerValue,
    ExactArithmeticToC0.integerAtom, ExactArithmeticToC0.a, a]

/-- Undefined partial operations never consult the external provider and their
two C step events map exactly to C0's declared decline receipt. -/
theorem declined_receipt_refines_compiledC0
    (operation : CoreOp) (first second : Int)
    (undefined : undefinedAt operation second) :
    receiptPattern first second 0
        (IR.expectedReceipt operation second .value).events =
      ExactArithmeticToC0.compiledC0Receipt operation first second := by
  cases operation <;>
    simp_all [IR.expectedReceipt, IR.expectedReceiptForZero,
      receiptPattern, eventPattern,
      externalOutcomePattern, externalPattern, labelPattern, natPattern, a,
      undefinedAt, ExactArithmeticToC0.compiledC0Receipt,
      ExactArithmeticToC0.targetUndefinedAt_iff,
      ExactArithmeticToC0.stepReceipt, ExactArithmeticToC0.receiptNil,
      ExactArithmeticToC0.label, ExactArithmeticToC0.natPattern,
      ExactArithmeticToC0.a, CoreOp.isPartial]

theorem declined_outcome_refines_compiledC0
    (operation : CoreOp) (first second : Int)
    (undefined : undefinedAt operation second) :
    outcomePattern 0 .declined =
      ExactArithmeticToC0.compiledC0Outcome operation first second := by
  rw [ExactArithmeticToC0.compiledC0Outcome_commutes]
  simp [coreSem_pos undefined, outcomePattern, ExactArithmeticToC0.a, a]

/-- The concrete representation theorem joins the already-proved semantic
hosting square without making the C interpreter or provider authoritative. -/
theorem arithmetic_hosting_with_instruction_representation
    (operation : CoreOp) (first second : Int) :
    programPattern (IR.lowerProgram operation) =
        ExactArithmeticToC0.compileCoreOperation operation ∧
      Relation.ReflTransGen
        (Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing
          (ExactArithmeticToC0.arithmeticC0ReferenceEnv
            operation first second) C0PureNTT.c0Pure)
        (ExactArithmeticToC0.compiledC0Start operation first second)
        (ExactArithmeticToC0.compiledC0Done operation first second) := by
  exact ⟨lowerProgram_pattern_exact operation,
    (ExactArithmeticToC0.exactArithmetic_to_C0_hosts_completion
      operation first second).2.1⟩

/-! ## Negative controls -/

def inventedLanguageTarget : IR.Program :=
  { IR.lowerProgram .add with
    instructions := [
      .callBinaryExternal 0 1 1 3 4,
      .returnValue,
      .returnLanguageFault,
      .returnEngineFault,
      .returnResourceFault] }

theorem invented_language_target_changes_program :
    programPattern inventedLanguageTarget ≠
      ExactArithmeticToC0.compileCoreOperation .add := by
  decide

/-- Equal completion outcomes do not make receipts equal: deleting the
external event is observable. -/
theorem deleted_external_event_changes_receipt :
    receiptPattern 2 3 5
        [.step 0, .external 0 0 .value, .step 1] ≠
      receiptPattern 2 3 5 [.step 0, .step 1] := by
  decide

/-- Reordering two chronological events changes the nested receipt. -/
theorem reordered_events_change_receipt :
    receiptPattern 2 3 5
        [.step 0, .external 0 0 .value, .step 1] ≠
      receiptPattern 2 3 5
        [.external 0 0 .value, .step 0, .step 1] := by
  decide

theorem external_fault_classes_remain_distinct :
    eventPattern 2 3 0 (.external 0 0 .languageFault) ≠
        eventPattern 2 3 0 (.external 0 0 .engineFault) ∧
      eventPattern 2 3 0 (.external 0 0 .engineFault) ≠
        eventPattern 2 3 0 (.external 0 0 .resourceFault) := by
  decide

end Mettapedia.GSLT.LanguageDef.ExactArithmeticC0IRRefinement
