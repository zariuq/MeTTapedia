import Mettapedia.Machines.NativeCostLedger
import Mettapedia.GSLT.LanguageDef.NativeOpsCNormalization
import Mettapedia.GSLT.LanguageDef.NativeOpsCFunctionComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsScalarLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsInstructionComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsFiniteStorage
import Mettapedia.GSLT.LanguageDef.NativeOpsTargetParameterFacts
import Mettapedia.GSLT.Core.RouteTrace

/-!
# CeTTa cost-counter and receipt-guard source

The body is consumed by the common C lexer and complete statement parser.
The ordinary-parameter reader lowers it to the shared operational IR; its
execution is compared with the independent natural-number cost specification.

The boundary is explicit: unsigned 64-bit arithmetic, immutable by-value
parameters, the admitted `UINT64_MAX` value, and a defined live Boolean
pointer destination. This is not a theorem about an ISO C compiler, the
physical allocator, concurrent pointer access or the whole cost ledger.
Source identity and the rest of the ledger remain separate obligations.
The receipt wrapper additionally uses two explicitly declared services.
Its inactive path retains the whole query post-state and releases its
invocation cells. Caller noninterference requires a state-preserving query;
no contract for the unexecuted observed service is used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.CeTTaNativeCost

open Mettapedia.GSLT.LanguageDef.NativeOps
open NativeIR (Atom Instruction)


/-- The complete body of the counter's `add_lower_bound` operation. -/
def counterBody : List Char := "{\n    if (right > UINT64_MAX - left) {\n        *overflow = true;\n        return UINT64_MAX;\n    }\n    return left + right;\n}".toList

private def counterTokens : List NativeC.Token := [.punctuation ['{'],
 .identifier ['i', 'f'],
 .punctuation ['('],
 .identifier ['r', 'i', 'g', 'h', 't'],
 .punctuation ['>'],
 .identifier ['U', 'I', 'N', 'T', '6', '4', '_', 'M', 'A', 'X'],
 .punctuation ['-'],
 .identifier ['l', 'e', 'f', 't'],
 .punctuation [')'],
 .punctuation ['{'],
 .punctuation ['*'],
 .identifier ['o', 'v', 'e', 'r', 'f', 'l', 'o', 'w'],
 .punctuation ['='],
 .identifier ['t', 'r', 'u', 'e'],
 .punctuation [';'],
 .identifier ['r', 'e', 't', 'u', 'r', 'n'],
 .identifier ['U', 'I', 'N', 'T', '6', '4', '_', 'M', 'A', 'X'],
 .punctuation [';'],
 .punctuation ['}'],
 .identifier ['r', 'e', 't', 'u', 'r', 'n'],
 .identifier ['l', 'e', 'f', 't'],
 .punctuation ['+'],
 .identifier ['r', 'i', 'g', 'h', 't'],
 .punctuation [';'],
 .punctuation ['}']]

private theorem counter_lexed : NativeC.lex counterBody = .ok counterTokens :=
  by decide +kernel

private def counterStatements : List NativeC.CStatement :=
  [.branch (.binary .gt (.identifier "right".toList)
      (.binary .sub (.identifier "UINT64_MAX".toList) (.identifier "left".toList)))
    [.assign (.unary .dereference (.identifier "overflow".toList)) (.bool true),
     .return (some (.identifier "UINT64_MAX".toList))] [],
   .return (some (.binary .add (.identifier "left".toList) (.identifier "right".toList)))]

private theorem counter_parsed : NativeC.blockText?
    ["uint64_t".toList, "bool".toList] counterBody = some counterStatements := by
  unfold NativeC.blockText?
  rw [counter_lexed]
  rfl

def counterBindings : NativeC.PrimitiveBindings :=
  [("left".toList, .temporary 1 .word),
   ("right".toList, .temporary 2 .word),
   ("overflow".toList, .temporary 3 (.ref .bool)),
   ("UINT64_MAX".toList, .word (BitVec.allOnes 64))]

def counterCode : List Instruction :=
  [.temporary 4 .word (.binary (.word .sub) (.word (BitVec.allOnes 64)) (.temporary 1 .word)),
   .temporary 5 .bool (.binary (.compare .gt) (.temporary 2 .word) (.temporary 4 .word)),
   .branch (.value (.temporary 5 .bool))
     [.temporary 6 .bool (.bool true),
      .write (.temporary 3 (.ref .bool)) (.temporary 6 .bool),
      .return (.word (BitVec.allOnes 64))] [],
   .temporary 7 .word (.binary (.word .add) (.temporary 1 .word) (.temporary 2 .word)),
   .return (.temporary 7 .word)]

theorem counter_source_admitted : NativeC.primitiveBodyText?
    ["uint64_t".toList, "bool".toList] counterBindings .word counterBody ⟨3⟩ =
    some (counterCode, ⟨7⟩) := by
  unfold NativeC.primitiveBodyText?
  rw [counter_parsed]
  cbv

/-- The independently declared ordinary C prototype, including its caller
pointer parameter. -/
def counterHeader : Header :=
  ⟨"add_lower_bound", [⟨"left", .word⟩, ⟨"right", .word⟩,
    ⟨"overflow", .ref .bool⟩], .word⟩

def counterFunction : NativeIR.Function :=
  ⟨counterHeader,
    [.temporary 1 .word (.readLocal "left"),
     .temporary 2 .word (.readLocal "right"),
     .temporary 3 (.ref .bool) (.readLocal "overflow")] ++ counterCode, 7⟩

def counterSource : List Char :=
  "static uint64_t add_lower_bound(uint64_t left, uint64_t right, bool *overflow) ".toList ++
    counterBody

private def counterRepresentation : NativeC.Representation := ⟨"OrdinaryCounter", ⟨[], [], [], []⟩, []⟩

private def counterMacros : NativeC.PrimitiveBindings :=
  [("UINT64_MAX".toList, .word (BitVec.allOnes 64))]

private def counterPrototypeTokens : List NativeC.Token :=
  [.identifier "static".toList, .identifier "uint64_t".toList,
   .identifier "add_lower_bound".toList, .punctuation ['('],
   .identifier "uint64_t".toList, .identifier "left".toList, .punctuation [','],
   .identifier "uint64_t".toList, .identifier "right".toList, .punctuation [','],
   .identifier "bool".toList, .punctuation ['*'], .identifier "overflow".toList,
   .punctuation [')']]

private theorem counter_function_lexed : NativeC.lex counterSource =
    .ok (counterPrototypeTokens ++ counterTokens) := by decide +kernel

private def counterParsedFunction : NativeC.CFunction :=
  ⟨⟨"uint64_t".toList, 0⟩, "add_lower_bound".toList,
    [⟨⟨"uint64_t".toList, 0⟩, "left".toList⟩,
     ⟨⟨"uint64_t".toList, 0⟩, "right".toList⟩,
     ⟨⟨"bool".toList, 1⟩, "overflow".toList⟩], counterStatements⟩

private theorem counter_function_parsed : NativeC.function?
    (2 * (counterPrototypeTokens ++ counterTokens).length + 4)
    ["uint64_t".toList, "bool".toList]
    (counterPrototypeTokens.tail ++ counterTokens) = some (counterParsedFunction, []) := by
  rfl

private theorem counter_function_text_parts (header : Header)
    (macros : NativeC.PrimitiveBindings) :
    NativeC.primitiveFunctionText? counterRepresentation ["uint64_t".toList, "bool".toList]
      header macros counterSource =
    NativeC.primitiveFunction? counterRepresentation header macros
      (counterSource.length + 1) counterParsedFunction :=
  NativeC.primitive_function_text_of_parts counterRepresentation
    ["uint64_t".toList, "bool".toList] header macros counterSource
    (counterPrototypeTokens ++ counterTokens) counterParsedFunction
    counter_function_lexed counter_function_parsed

/-- The whole source, not merely its body, admits the function with actual
invocation-cell reads and the previously checked scalar operation. -/
theorem counter_function_source_admitted : NativeC.primitiveFunctionText?
    counterRepresentation ["uint64_t".toList, "bool".toList] counterHeader counterMacros
    counterSource = some counterFunction := by
  rw [counter_function_text_parts]
  have normalized : NativeC.primitiveStatements? counterBindings .word
      (counterSource.length + 1) counterStatements ⟨3⟩ [] counterRepresentation =
      some (counterCode, ⟨7⟩) := by
    have length : counterSource.length + 1 = 204 := by decide +kernel
    rw [length]
    simp only [counterStatements, NativeC.primitiveStatements?, NativeC.primitiveStatement?,
      NativeC.primitiveExpression?]
    rfl
  exact NativeC.primitive_function_of_parts counterRepresentation counterHeader counterMacros
    (counterSource.length + 1) counterParsedFunction .word counterCode ⟨7⟩
    (by rfl) (by rfl) (by rfl) normalized

theorem counter_function_wrong_return_type_refused : NativeC.primitiveFunctionText?
    counterRepresentation ["uint64_t".toList, "bool".toList]
    { counterHeader with result := .bool } counterMacros counterSource = none := by
  rw [counter_function_text_parts]
  rfl

theorem counter_function_macro_shadow_refused : NativeC.primitiveFunctionText?
    counterRepresentation ["uint64_t".toList, "bool".toList] counterHeader
    (("left".toList, .word 0) :: counterMacros) counterSource = none := by
  rw [counter_function_text_parts]
  rfl

/-- The same spelling without an admitted macro meaning is refused. -/
theorem counter_macro_authority_required : NativeC.primitiveBodyText?
    ["uint64_t".toList, "bool".toList] (counterBindings.take 3) .word counterBody ⟨3⟩ =
    none := by
  unfold NativeC.primitiveBodyText?
  rw [counter_parsed]
  cbv

/-- Trailing text is never silently dropped by source admission. -/
theorem counter_trailing_source_refused : NativeC.primitiveBodyText?
    ["uint64_t".toList, "bool".toList] counterBindings .word
    (counterBody ++ " return wrong;".toList) ⟨3⟩ = none := by
  have extended : NativeC.lex (counterBody ++ " return wrong;".toList) =
      .ok (counterTokens ++ [.identifier "return".toList, .identifier "wrong".toList,
        .punctuation [';']]) := by decide +kernel
  unfold NativeC.primitiveBodyText? NativeC.blockText?
  rw [extended]
  rfl

def parameterFrame (left right : BitVec 64) (address : Address)
    (base : TargetFrame := targetEmptyFrame 0) : TargetFrame where
  storage := base.storage
  nextLocal := base.nextLocal
  bindings := base.bindings
  temporaryNames := [3, 2, 1]
  temporaries := fun identity =>
    if identity = 1 then some (.word left) else
    if identity = 2 then some (.word right) else
    if identity = 3 then some (.reference (some address)) else none


private theorem parameterFrame_complete (left right : BitVec 64) (address : Address)
    (base : TargetFrame := targetEmptyFrame 0) :
    ∀ identity, (parameterFrame left right address base).temporaryNames.contains identity = false →
      (parameterFrame left right address base).temporaries identity = none := by
  intro identity absent
  by_cases first : identity = 1 <;> by_cases second : identity = 2 <;>
    by_cases third : identity = 3 <;>
    simp [parameterFrame, first, second, third] at absent ⊢

private abbrev subtractionFrame (left right : BitVec 64) (address : Address)
    (base : TargetFrame := targetEmptyFrame 0) : TargetFrame :=
  targetDeclareTemporary (parameterFrame left right address base) 4
    (.word (BitVec.allOnes 64 - left))

private abbrev conditionFrame (left right : BitVec 64) (address : Address)
    (base : TargetFrame := targetEmptyFrame 0) : TargetFrame :=
  targetDeclareTemporary (subtractionFrame left right address base) 5
    (.bool (decide (right > BitVec.allOnes 64 - left)))

/-- The entire frame and state, including the lexical close of the early-return
branch, are retained in this outcome. -/
def counterOutcome {World : Type} (left right : BitVec 64) (address : Address)
    (state : TargetState World) (writtenMemory : TargetMemory)
    (base : TargetFrame := targetEmptyFrame 0) : TargetBlockOutcome World :=
  let frame := conditionFrame left right address base
  if right > BitVec.allOnes 64 - left then
    targetCloseBlock frame
      ⟨.returned (.word (BitVec.allOnes 64)), targetDeclareTemporary frame 6 (.bool true),
        { state with memory := writtenMemory }⟩
  else
    ⟨.returned (.word (left + right)), targetDeclareTemporary frame 7 (.word (left + right)), state⟩

/-- Two-way execution correspondence for the complete admitted helper body.
The defined pointer write is a memory precondition, not a conclusion assumed
about the helper or its returned answer. Allocation and external call models
are arbitrary: this body cannot invoke either of them. -/
theorem counter_run_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (left right : BitVec 64) (address : Address) (state : TargetState World)
    (writtenMemory : TargetMemory)
    (writeDefined : targetWrite state.memory address (.bool true) = some writtenMemory)
    (out : TargetBlockOutcome World) (base : TargetFrame := targetEmptyFrame 0)
    (root : List Instruction := counterCode) :
    TargetRun interface heap calls .word root counterCode
      (parameterFrame left right address base) state out ↔
      out = counterOutcome left right address state writtenMemory base := by
  let initial := parameterFrame left right address base
  let subFrame := subtractionFrame left right address base
  let testFrame := conditionFrame left right address base
  have leftInitial : TargetAtomEval interface initial state (.temporary 1 .word) (.word left) :=
    .temporary (by simp [initial, parameterFrame]) (by rfl)
  have subtraction : TargetPureEval interface initial state
      (.binary (.word .sub) (.word (BitVec.allOnes 64)) (.temporary 1 .word))
      (.word (BitVec.allOnes 64 - left)) :=
    .binary (.word _) leftInitial (by rfl)
  have leftSub : TargetAtomEval interface subFrame state (.temporary 1 .word) (.word left) :=
    .temporary (by simp [subFrame, targetDeclareTemporary, parameterFrame])
      (by rfl)
  have rightSub : TargetAtomEval interface subFrame state (.temporary 2 .word) (.word right) :=
    .temporary (by simp [subFrame, targetDeclareTemporary, parameterFrame])
      (by rfl)
  have subRead : TargetAtomEval interface subFrame state (.temporary 4 .word)
      (.word (BitVec.allOnes 64 - left)) :=
    .temporary (declare_temporary_read _ _ _) (by rfl)
  have comparison : TargetPureEval interface subFrame state
      (.binary (.compare .gt) (.temporary 2 .word) (.temporary 4 .word))
      (.bool (decide (right > BitVec.allOnes 64 - left))) :=
    .binary rightSub subRead (by rfl)
  have testRead : TargetAtomEval interface testFrame state (.temporary 5 .bool)
      (.bool (decide (right > BitVec.allOnes 64 - left))) :=
    .temporary (declare_temporary_read _ _ _) (by rfl)
  have tested : TargetConditionEval interface testFrame state (.value (.temporary 5 .bool))
      (decide (right > BitVec.allOnes 64 - left)) := .value testRead
  have testComplete : ∀ identity, testFrame.temporaryNames.contains identity = false →
      testFrame.temporaries identity = none :=
    declare_temporary_scoped subFrame 5 _
      (declare_temporary_scoped initial 4 _ (parameterFrame_complete left right address base))
  have selfClose : targetCloseBlock testFrame ⟨.normal, testFrame, state⟩ =
      ⟨.normal, testFrame, state⟩ := by
    simp only [targetCloseBlock, targetLeaveScope_self testFrame state testComplete]
  unfold counterCode
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : initial.temporaryNames.contains 4 = false) subtraction)]
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : subFrame.temporaryNames.contains 5 = false) comparison)]
  by_cases overflow : right > BitVec.allOnes 64 - left
  · let trueFrame := targetDeclareTemporary testFrame 6 (.bool true)
    have pointerRead : TargetAtomEval interface trueFrame state (.temporary 3 (.ref .bool))
        (.reference (some address)) :=
      .temporary (by simp [trueFrame, testFrame, subtractionFrame,
        targetDeclareTemporary, parameterFrame]) (by rfl)
    have trueRead : TargetAtomEval interface trueFrame state (.temporary 6 .bool) (.bool true) :=
      .temporary (declare_temporary_read _ _ _) (by rfl)
    have bodyExact : ∀ inner, TargetRun interface heap calls .word
        [.temporary 6 .bool (.bool true),
         .write (.temporary 3 (.ref .bool)) (.temporary 6 .bool),
         .return (.word (BitVec.allOnes 64))]
        [.temporary 6 .bool (.bool true),
         .write (.temporary 3 (.ref .bool)) (.temporary 6 .bool),
         .return (.word (BitVec.allOnes 64))] testFrame state inner ↔
        inner = ⟨.returned (.word (BitVec.allOnes 64)), trueFrame,
          { state with memory := writtenMemory }⟩ := by
      intro inner
      rw [target_normal_then_exact (target_temporary_instruction_exact
        (by rfl : testFrame.temporaryNames.contains 6 = false) (.bool true))]
      rw [target_normal_then_exact (target_write_instruction_exact pointerRead trueRead writeDefined)]
      exact target_return_then_exact (.word _) _ _ _
    have branchExact : ∀ inner, TargetInstructionEval interface heap calls .word
        (.branch (.value (.temporary 5 .bool))
          [.temporary 6 .bool (.bool true),
           .write (.temporary 3 (.ref .bool)) (.temporary 6 .bool),
           .return (.word (BitVec.allOnes 64))] []) testFrame state inner ↔
        inner = counterOutcome left right address state writtenMemory base := by
      intro inner
      rw [target_branch_instruction_exact tested]
      simp only [overflow, decide_true, ↓reduceIte, bodyExact]
      constructor
      · rintro ⟨beforeClose, rfl, same⟩
        simpa only [counterOutcome, if_pos overflow] using same
      · intro same
        exact ⟨_, rfl, by simpa only [counterOutcome, if_pos overflow] using same⟩
    have outcomeReturning : counterOutcome left right address state writtenMemory base =
        ⟨.returned (.word (BitVec.allOnes 64)),
          (targetLeaveScope testFrame trueFrame { state with memory := writtenMemory }).1,
          (targetLeaveScope testFrame trueFrame { state with memory := writtenMemory }).2⟩ := by
      simp only [counterOutcome, overflow, ↓reduceIte, targetCloseBlock]
      rfl
    rw [outcomeReturning] at branchExact ⊢
    exact target_returning_then_exact branchExact _ _ _
  · have branchExact : ∀ inner, TargetInstructionEval interface heap calls .word
        (.branch (.value (.temporary 5 .bool))
          [.temporary 6 .bool (.bool true),
           .write (.temporary 3 (.ref .bool)) (.temporary 6 .bool),
           .return (.word (BitVec.allOnes 64))] []) testFrame state inner ↔
        inner = ⟨.normal, testFrame, state⟩ := by
      intro inner
      rw [target_branch_instruction_exact tested]
      simp only [overflow, decide_false, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨body, ran, same⟩
        cases (target_run_empty_exact [] testFrame state body).mp ran
        exact same.trans selfClose
      · intro same
        exact ⟨_, .nil _ _ _, same.trans selfClose.symm⟩
    rw [target_normal_then_exact branchExact]
    have leftTest : TargetAtomEval interface testFrame state (.temporary 1 .word) (.word left) :=
      .temporary (by simp [testFrame, subtractionFrame,
        targetDeclareTemporary, parameterFrame]) (by rfl)
    have rightTest : TargetAtomEval interface testFrame state (.temporary 2 .word) (.word right) :=
      .temporary (by simp [testFrame, subtractionFrame,
        targetDeclareTemporary, parameterFrame]) (by rfl)
    have addition : TargetPureEval interface testFrame state
        (.binary (.word .add) (.temporary 1 .word) (.temporary 2 .word))
        (.word (left + right)) := .binary leftTest rightTest (by rfl)
    rw [target_normal_then_exact (target_temporary_instruction_exact
      (by rfl : testFrame.temporaryNames.contains 7 = false) addition)]
    have resultRead : TargetAtomEval interface
        (targetDeclareTemporary testFrame 7 (.word (left + right))) state
        (.temporary 7 .word) (.word (left + right)) :=
      .temporary (declare_temporary_read _ _ _) (by simp [targetDeclareTemporary])
    simpa only [counterOutcome, overflow, ↓reduceIte] using
      target_return_then_exact resultRead _ _ out


private theorem counterOutcome_state {World : Type} (left right : BitVec 64) (address : Address)
    (state : TargetState World) (writtenMemory : TargetMemory)
    (base : TargetFrame := targetEmptyFrame 0) :
    (counterOutcome left right address state writtenMemory base).state =
      if right > BitVec.allOnes 64 - left then
        { state with memory := writtenMemory } else state := by
  by_cases overflow : right > BitVec.allOnes 64 - left
  · simp only [counterOutcome, if_pos overflow, targetCloseBlock, targetLeaveScope,
      conditionFrame, subtractionFrame, targetDeclareTemporary, parameterFrame,
      targetDropLocals_empty]
  · simp only [counterOutcome, if_neg overflow]

private theorem counterOutcome_flow {World : Type} (left right : BitVec 64)
    (address : Address) (previousOverflow : Bool) (state : TargetState World)
    (writtenMemory : TargetMemory) (base : TargetFrame := targetEmptyFrame 0) :
    (counterOutcome left right address state writtenMemory base).flow =
      .returned (.word
        (Mettapedia.Machines.NativeCostLedger.wordAddLowerBound left right previousOverflow).1) := by
  by_cases overflow : right > BitVec.allOnes 64 - left
  · simp only [counterOutcome, Mettapedia.Machines.NativeCostLedger.wordAddLowerBound,
      if_pos overflow, targetCloseBlock]
  · simp only [counterOutcome, Mettapedia.Machines.NativeCostLedger.wordAddLowerBound,
      if_neg overflow]

private theorem counterOutcome_flag {World : Type} (left right : BitVec 64)
    (address : Address) (previousOverflow : Bool) (state : TargetState World)
    (writtenMemory : TargetMemory)
    (flagRead : targetRead state.memory address = some (.bool previousOverflow))
    (writeDefined : targetWrite state.memory address (.bool true) = some writtenMemory)
    (base : TargetFrame := targetEmptyFrame 0) :
    targetRead (counterOutcome left right address state writtenMemory base).state.memory address =
      some (.bool
        (Mettapedia.Machines.NativeCostLedger.wordAddLowerBound left right previousOverflow).2) := by
  rw [counterOutcome_state left right address state writtenMemory base]
  by_cases overflow : right > BitVec.allOnes 64 - left
  · simp only [Mettapedia.Machines.NativeCostLedger.wordAddLowerBound, if_pos overflow]
    exact (targetRead_after_write writeDefined).1
  · simp only [Mettapedia.Machines.NativeCostLedger.wordAddLowerBound, if_neg overflow]
    exact flagRead

private theorem counterOutcome_preserves_state {World : Type} (left right : BitVec 64)
    (address : Address) (state : TargetState World) (writtenMemory : TargetMemory)
    (writeDefined : targetWrite state.memory address (.bool true) = some writtenMemory)
    (base : TargetFrame := targetEmptyFrame 0) :
    (counterOutcome left right address state writtenMemory base).state.external = state.external ∧
    (counterOutcome left right address state writtenMemory base).state.fault = state.fault ∧
    (counterOutcome left right address state writtenMemory base).state.memory.owned =
      state.memory.owned := by
  rw [counterOutcome_state left right address state writtenMemory base]
  by_cases overflow : right > BitVec.allOnes 64 - left
  · rw [if_pos overflow]
    exact ⟨rfl, rfl, (targetRead_after_write writeDefined).2⟩
  · rw [if_neg overflow]
    exact ⟨rfl, rfl, rfl⟩

/-- Parameter cells allocated by the ordinary function-entry relation. -/
private def counterBound {World : Type} (state : TargetState World) (storage : Nat)
    (left right : BitVec 64) (address : Address) : TargetFrame × TargetState World :=
  let first := targetDeclareLocal (targetEmptyFrame storage) state "left" .word (.word left)
  let second := targetDeclareLocal first.1 first.2 "right" .word (.word right)
  targetDeclareLocal second.1 second.2 "overflow" (.ref .bool) (.reference (some address))

private def counterParameterMemory (memory : TargetMemory) (storage : Nat)
    (left right : BitVec 64) (address : Address) : TargetMemory :=
  targetParameterMemory memory storage 0 [.word left, .word right, .reference (some address)]

private theorem counter_bound_state {World : Type} (state : TargetState World) (storage : Nat)
    (left right : BitVec 64) (address : Address) :
    (counterBound state storage left right address).2 =
      { state with memory := (counterParameterMemory state.memory storage left right address) } := rfl

private theorem counter_parameters_release (memory : TargetMemory) (storage : Nat)
    (left right : BitVec 64) (address : Address) (fresh : targetFreshFrame memory storage) :
    targetDropLocals (counterParameterMemory memory storage left right address) storage 0 3 =
      memory := by
  exact target_parameter_memory_release memory storage
    [.word left, .word right, .reference (some address)] fresh

private theorem counter_parameters_write (memory : TargetMemory) (storage : Nat)
    (left right : BitVec 64) (address : Address) (writtenMemory : TargetMemory)
    (different : address.storage ≠ storage)
    (writeDefined : targetWrite memory address (.bool true) = some writtenMemory) :
    targetWrite (counterParameterMemory memory storage left right address) address (.bool true) =
      some (counterParameterMemory writtenMemory storage left right address) := by
  unfold counterParameterMemory
  rw [targetWrite_parameter_memory_other_storage _ _ _ _ _ _ different, writeDefined]
  rfl

private theorem counterOutcome_extent {World : Type} (left right : BitVec 64) (address : Address)
    (state : TargetState World) (writtenMemory : TargetMemory) (base : TargetFrame) :
    (counterOutcome left right address state writtenMemory base).frame.storage = base.storage ∧
    (counterOutcome left right address state writtenMemory base).frame.nextLocal = base.nextLocal := by
  by_cases overflow : right > BitVec.allOnes 64 - left
  · simp only [counterOutcome, if_pos overflow, targetCloseBlock, targetLeaveScope,
      conditionFrame, subtractionFrame, targetDeclareTemporary, parameterFrame]
    trivial
  · simp only [counterOutcome, if_neg overflow, targetDeclareTemporary,
      conditionFrame, subtractionFrame, parameterFrame]
    trivial

private theorem counter_function_teardown {World : Type} (state : TargetState World)
    (storage : Nat) (left right : BitVec 64) (address : Address) (writtenMemory : TargetMemory)
    (fresh : targetFreshFrame state.memory storage)
    (different : storage ≠ address.storage)
    (writeDefined : targetWrite state.memory address (.bool true) = some writtenMemory)
    (out : TargetBlockOutcome World)
    (outExact : out = counterOutcome left right address
      (counterBound state storage left right address).2
      (counterParameterMemory writtenMemory storage left right address)
      (counterBound state storage left right address).1) :
    (targetLeaveScope (targetEmptyFrame storage) out.frame out.state).2 =
      if right > BitVec.allOnes 64 - left then { state with memory := writtenMemory } else state := by
  let bound := counterBound state storage left right address
  have shape := counterOutcome_extent left right address bound.2
    (counterParameterMemory writtenMemory storage left right address) bound.1
  have sameStorage : out.frame.storage = storage :=
    (congrArg (fun result => result.frame.storage) outExact).trans shape.1
  have extent : out.frame.nextLocal = 3 :=
    (congrArg (fun result => result.frame.nextLocal) outExact).trans shape.2
  have stateExact : out.state =
      if right > BitVec.allOnes 64 - left then
        { state with memory := (counterParameterMemory writtenMemory storage left right address) }
      else { state with memory := (counterParameterMemory state.memory storage left right address) } := by
    calc
      out.state = (counterOutcome left right address bound.2
        (counterParameterMemory writtenMemory storage left right address) bound.1).state :=
          congrArg TargetBlockOutcome.state outExact
      _ = if right > BitVec.allOnes 64 - left then
          { (bound.2) with memory := (counterParameterMemory writtenMemory storage left right address) }
        else bound.2 := counterOutcome_state left right address bound.2
          (counterParameterMemory writtenMemory storage left right address) bound.1
      _ = _ := by rw [counter_bound_state]
  exact target_conditional_invocation_teardown state storage 3 out.frame out.state
    (counterParameterMemory state.memory storage left right address)
    (counterParameterMemory writtenMemory storage left right address) writtenMemory
    (right > BitVec.allOnes 64 - left) sameStorage extent stateExact
    (counter_parameters_release state.memory storage left right address fresh)
    (counter_parameters_release writtenMemory storage left right address
      (targetFreshFrame_after_write fresh different writeDefined))

private theorem counter_parameters_readback {World : Type} (state : TargetState World)
    (storage : Nat) (left right : BitVec 64) (address : Address) :
    let bound := counterBound state storage left right address
    targetLocalValue bound.1 bound.2 "left" = some (.word left) ∧
    targetLocalValue bound.1 bound.2 "right" = some (.word right) ∧
    targetLocalValue bound.1 bound.2 "overflow" = some (.reference (some address)) := by
  simp [counterBound, targetDeclareLocal, targetEmptyFrame, targetLocalValue,
    targetLocalAddress, targetRead, targetStoreCell, targetReadPath]

private theorem counter_capture_frame {World : Type} (state : TargetState World)
    (storage : Nat) (left right : BitVec 64) (address : Address) :
    targetDeclareTemporary (targetDeclareTemporary (targetDeclareTemporary
      (counterBound state storage left right address).1 1 (.word left)) 2 (.word right))
      3 (.reference (some address)) =
    parameterFrame left right address (counterBound state storage left right address).1 := by
  have temporaries : (targetDeclareTemporary (targetDeclareTemporary (targetDeclareTemporary
      (counterBound state storage left right address).1 1 (.word left)) 2 (.word right))
      3 (.reference (some address))).temporaries =
      (parameterFrame left right address (counterBound state storage left right address).1).temporaries := by
    funext identity
    by_cases first : identity = 1 <;> by_cases second : identity = 2 <;>
      by_cases third : identity = 3 <;>
      simp [targetDeclareTemporary, parameterFrame, counterBound, targetDeclareLocal,
        targetEmptyFrame, first, second, third] at *
  change TargetFrame.mk storage 3 _ [3, 2, 1] _ = TargetFrame.mk storage 3 _ [3, 2, 1] _
  exact congrArg (fun values => TargetFrame.mk storage 3
    (counterBound state storage left right address).1.bindings [3, 2, 1] values) temporaries

private theorem counter_function_body_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (left right : BitVec 64) (address : Address)
    (writtenMemory : TargetMemory)
    (writeDefined : targetWrite (counterBound state storage left right address).2.memory
      address (.bool true) = some writtenMemory)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    let bound := counterBound state storage left right address
    TargetRun interface heap calls .word root counterFunction.body bound.1 bound.2 out ↔
      out = counterOutcome left right address bound.2 writtenMemory bound.1 := by
  let bound := counterBound state storage left right address
  obtain ⟨leftRead, rightRead, pointerRead⟩ :=
    counter_parameters_readback state storage left right address
  change TargetRun interface heap calls .word root
    (.temporary 1 .word (.readLocal "left") ::
     .temporary 2 .word (.readLocal "right") ::
     .temporary 3 (.ref .bool) (.readLocal "overflow") :: counterCode)
    bound.1 bound.2 out ↔ _
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : bound.1.temporaryNames.contains 1 = false) (.local leftRead))]
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : (targetDeclareTemporary bound.1 1 (.word left)).temporaryNames.contains 2 = false)
    (.local rightRead))]
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : (targetDeclareTemporary (targetDeclareTemporary bound.1 1 (.word left))
      2 (.word right)).temporaryNames.contains 3 = false) (.local pointerRead))]
  rw [counter_capture_frame]
  exact counter_run_exact interface heap calls left right address bound.2 writtenMemory
    writeDefined out bound.1 root

/-- The counter's full return retains the caller's state and changes only the
defined overflow destination when unsigned addition would overflow. -/
def counterFunctionOutcome {World : Type} (left right : BitVec 64)
    (state : TargetState World) (writtenMemory : TargetMemory) : TargetRawResult World :=
  ⟨.word (Mettapedia.Machines.NativeCostLedger.wordAddLowerBound left right false).1,
    if right > BitVec.allOnes 64 - left then { state with memory := writtenMemory } else state⟩

/-- Complete function entry, execution and return correspond in both
directions. The caller's live flag separates its storage from the newly
allocated parameter frame; no parameter cells remain in the result. -/
theorem counter_function_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (left right : BitVec 64) (address : Address) (previousOverflow : Bool)
    (state : TargetState World) (writtenMemory : TargetMemory)
    (flagRead : targetRead state.memory address = some (.bool previousOverflow))
    (writeDefined : targetWrite state.memory address (.bool true) = some writtenMemory)
    (result : TargetRawResult World) :
    TargetFunctionBody interface heap calls counterFunction
      [.word left, .word right, .reference (some address)] state result ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧
        result = counterFunctionOutcome left right state writtenMemory := by
  constructor
  · intro ran
    cases ran with
    | @run storage frame bound out raw fresh parameters body returned =>
      have parameterPair : (frame, bound) = counterBound state storage left right address :=
        (Option.some.inj parameters).symm
      have frameEq : frame = (counterBound state storage left right address).1 :=
        congrArg Prod.fst parameterPair
      have stateEq : bound = (counterBound state storage left right address).2 :=
        congrArg Prod.snd parameterPair
      subst frame
      subst bound
      have different := targetFreshFrame_storage_ne_read fresh flagRead
      have boundWrite := counter_parameters_write state.memory storage left right address
        writtenMemory different.symm writeDefined
      have executed := (counter_function_body_exact interface heap calls state storage
        left right address _ boundWrite counterFunction.body out).mp body
      have flowExact := (congrArg TargetBlockOutcome.flow executed).trans
        (counterOutcome_flow left right address false
          (counterBound state storage left right address).2
          (counterParameterMemory writtenMemory storage left right address)
          (counterBound state storage left right address).1)
      have valueExact : raw = .word
          (Mettapedia.Machines.NativeCostLedger.wordAddLowerBound left right false).1 :=
        TargetFlow.returned.inj (returned.symm.trans flowExact)
      have teardown := counter_function_teardown state storage left right address writtenMemory
        fresh different writeDefined out executed
      refine ⟨⟨storage, fresh⟩, ?_⟩
      rw [valueExact, teardown]
      rfl
  · rintro ⟨⟨storage, fresh⟩, rfl⟩
    let bound := counterBound state storage left right address
    let written := counterParameterMemory writtenMemory storage left right address
    have different := targetFreshFrame_storage_ne_read fresh flagRead
    have boundWrite : targetWrite bound.2.memory address (.bool true) = some written :=
      counter_parameters_write state.memory storage left right address writtenMemory
        different.symm writeDefined
    have executed : TargetFunctionBody interface heap calls counterFunction
        [.word left, .word right, .reference (some address)] state
        ⟨.word (Mettapedia.Machines.NativeCostLedger.wordAddLowerBound left right false).1,
          (targetLeaveScope (targetEmptyFrame storage)
            (counterOutcome left right address bound.2 written bound.1).frame
            (counterOutcome left right address bound.2 written bound.1).state).2⟩ :=
      .run fresh (by rfl)
        ((counter_function_body_exact interface heap calls state storage left right address
          written boundWrite counterFunction.body _).mpr rfl)
        (counterOutcome_flow left right address false bound.2 written bound.1)
    rw [counter_function_teardown state storage left right address writtenMemory
      fresh different writeDefined _ rfl] at executed
    exact executed

/-- Finite logical caller storage supplies a fresh invocation frame and an
actual execution, rather than an assumed function result. -/
theorem counter_function_exists {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (left right : BitVec 64) (address : Address) (previousOverflow : Bool)
    (state : TargetState World) (finite : TargetFiniteStorage state.memory)
    (flagRead : targetRead state.memory address = some (.bool previousOverflow)) :
    ∃ result, TargetFunctionBody interface heap calls counterFunction
      [.word left, .word right, .reference (some address)] state result := by
  obtain ⟨writtenMemory, writeDefined⟩ := targetWrite_defined_of_read flagRead (.bool true)
  exact ⟨counterFunctionOutcome left right state writtenMemory,
    (counter_function_exact interface heap calls left right address previousOverflow state
      writtenMemory flagRead writeDefined _).mpr ⟨target_finite_fresh finite, rfl⟩⟩

/-- A missing pointer parameter cannot be repaired by an otherwise valid
body or return. -/
theorem counter_function_wrong_arity_refused {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (left right : BitVec 64) (state : TargetState World) (result : TargetRawResult World) :
    ¬ TargetFunctionBody interface heap calls counterFunction [.word left, .word right]
      state result := by
  intro ran
  cases ran with
  | run _ parameters _ _ => cases parameters

/-- The full function's value and caller-visible flag implement the
independent natural-number counter; its exact state update preserves all
other caller fields, including allocation availability and statistics. -/
theorem counter_function_correspondence {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (left right : BitVec 64) (address : Address) (previousOverflow : Bool)
    (state : TargetState World) (writtenMemory : TargetMemory)
    (flagRead : targetRead state.memory address = some (.bool previousOverflow))
    (writeDefined : targetWrite state.memory address (.bool true) = some writtenMemory)
    {result : TargetRawResult World}
    (ran : TargetFunctionBody interface heap calls counterFunction
      [.word left, .word right, .reference (some address)] state result) :
    ∃ word : BitVec 64,
      result.value = .word word ∧
      word.toNat = (Mettapedia.Machines.NativeCostLedger.addLowerBound (2 ^ 64 - 1)
        left.toNat right.toNat).1 ∧
      targetRead result.state.memory address = some (.bool (previousOverflow ||
        (Mettapedia.Machines.NativeCostLedger.addLowerBound (2 ^ 64 - 1)
          left.toNat right.toNat).2)) ∧
      result.state = if right > BitVec.allOnes 64 - left then
        { state with memory := writtenMemory } else state := by
  have exactResult := (counter_function_exact interface heap calls left right address
    previousOverflow state writtenMemory flagRead writeDefined result).mp ran |>.2
  have stateExact : result.state = (counterOutcome left right address state writtenMemory).state :=
    (congrArg TargetRawResult.state exactResult).trans
      (counterOutcome_state left right address state writtenMemory).symm
  refine ⟨(Mettapedia.Machines.NativeCostLedger.wordAddLowerBound left right false).1,
    congrArg TargetRawResult.value exactResult,
    Mettapedia.Machines.NativeCostLedger.wordAddLowerBound_value left right false, ?_,
    congrArg TargetRawResult.state exactResult⟩
  rw [stateExact]
  exact (counterOutcome_flag left right address previousOverflow state writtenMemory
    flagRead writeDefined).trans
    (congrArg (fun flag : Bool => some (TargetValue.bool flag))
      (Mettapedia.Machines.NativeCostLedger.wordAddLowerBound_flag left right previousOverflow))

/-- Both the raw returned counter and the stored sticky flag agree with
independent natural-number saturation. An inherited overflow flag is retained
on the non-overflow path; an overflowing sum cannot wrap into a small value. -/
theorem counter_run_correspondence {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (left right : BitVec 64) (address : Address) (previousOverflow : Bool)
    (state : TargetState World) (writtenMemory : TargetMemory)
    (flagRead : targetRead state.memory address = some (.bool previousOverflow))
    (writeDefined : targetWrite state.memory address (.bool true) = some writtenMemory)
    {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls .word counterCode counterCode
      (parameterFrame left right address) state out) :
    ∃ result : BitVec 64,
      out.flow = .returned (.word result) ∧
      result.toNat = (Mettapedia.Machines.NativeCostLedger.addLowerBound (2 ^ 64 - 1)
        left.toNat right.toNat).1 ∧
      targetRead out.state.memory address = some (.bool (previousOverflow ||
        (Mettapedia.Machines.NativeCostLedger.addLowerBound (2 ^ 64 - 1)
          left.toNat right.toNat).2)) ∧
      out.state.external = state.external ∧
      out.state.fault = state.fault ∧ out.state.memory.owned = state.memory.owned := by
  have outcome : out = counterOutcome left right address state writtenMemory :=
    (counter_run_exact interface heap calls left right address state writtenMemory
      writeDefined out).mp ran
  rw [outcome]
  refine ⟨(Mettapedia.Machines.NativeCostLedger.wordAddLowerBound
    left right previousOverflow).1,
    counterOutcome_flow left right address previousOverflow state writtenMemory,
    Mettapedia.Machines.NativeCostLedger.wordAddLowerBound_value left right previousOverflow,
    ?_, counterOutcome_preserves_state left right address state writtenMemory writeDefined⟩
  exact (counterOutcome_flag left right address previousOverflow state writtenMemory
    flagRead writeDefined).trans
      (congrArg (fun flag : Bool => some (TargetValue.bool flag))
        (Mettapedia.Machines.NativeCostLedger.wordAddLowerBound_flag
          left right previousOverflow))

/-- A call receipt records an execution of the admitted helper body. The
increment is explicit; neither the returned counter nor the post-state is
defined by the ledger specification. -/
structure CounterCall {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (address : Address)
    (before after : BitVec 64 × TargetState World) where
  increment : BitVec 64
  outcome : TargetBlockOutcome World
  executed : TargetRun interface heap calls .word counterCode counterCode
    (parameterFrame before.1 increment address) before.2 outcome
  returned : outcome.flow = .returned (.word after.1)
  postState : outcome.state = after.2

private theorem counter_call_word_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {address : Address}
    {before after : BitVec 64 × TargetState World}
    (call : CounterCall interface heap calls address before after) (overflow : Bool)
    (flagRead : targetRead before.2.memory address = some (.bool overflow)) :
    after.1 = (Mettapedia.Machines.NativeCostLedger.wordAddLowerBound
      before.1 call.increment overflow).1 ∧
    targetRead after.2.memory address = some (.bool
      (Mettapedia.Machines.NativeCostLedger.wordAddLowerBound
        before.1 call.increment overflow).2) ∧
    after.2.external = before.2.external ∧ after.2.fault = before.2.fault ∧
      after.2.memory.owned = before.2.memory.owned := by
  obtain ⟨writtenMemory, writeDefined⟩ := targetWrite_defined_of_read flagRead (.bool true)
  have executed := (counter_run_exact interface heap calls before.1 call.increment
    address before.2 writtenMemory writeDefined call.outcome).mp call.executed
  have returned := (congrArg TargetBlockOutcome.flow executed).trans
    (counterOutcome_flow before.1 call.increment address overflow before.2 writtenMemory)
  refine ⟨TargetValue.word.inj (TargetFlow.returned.inj (call.returned.symm.trans returned)),
    ?_, ?_⟩
  · rw [← call.postState, executed]
    exact counterOutcome_flag before.1 call.increment address overflow before.2 writtenMemory
      flagRead writeDefined
  · rw [← call.postState, executed]
    exact counterOutcome_preserves_state before.1 call.increment address before.2
      writtenMemory writeDefined

/-- Existing body receipts realize the same complete function call when the
caller has finite storage. Entry and teardown therefore introduce no new
meter state or residual parameter allocation. -/
theorem counter_call_function_realization {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {address : Address}
    {before after : BitVec 64 × TargetState World}
    (call : CounterCall interface heap calls address before after)
    (finite : TargetFiniteStorage before.2.memory) (overflow : Bool)
    (flagRead : targetRead before.2.memory address = some (.bool overflow)) :
    TargetFunctionBody interface heap calls counterFunction
      [.word before.1, .word call.increment, .reference (some address)] before.2
      ⟨.word after.1, after.2⟩ := by
  obtain ⟨writtenMemory, writeDefined⟩ := targetWrite_defined_of_read flagRead (.bool true)
  have executed := (counter_run_exact interface heap calls before.1 call.increment address
    before.2 writtenMemory writeDefined call.outcome).mp call.executed
  have flowExact := (congrArg TargetBlockOutcome.flow executed).trans
    (counterOutcome_flow before.1 call.increment address false before.2 writtenMemory)
  have wordExact := TargetValue.word.inj (TargetFlow.returned.inj
    (call.returned.symm.trans flowExact))
  have stateExact := call.postState.symm.trans
    ((congrArg TargetBlockOutcome.state executed).trans
      (counterOutcome_state before.1 call.increment address before.2 writtenMemory))
  apply (counter_function_exact interface heap calls before.1 call.increment address overflow
    before.2 writtenMemory flagRead writeDefined _).mpr
  refine ⟨target_finite_fresh finite, ?_⟩
  rw [wordExact, stateExact]
  rfl

/-- Each existing receipt retains its caller's storage support bound. The
fresh invocation storage used by its full realization never leaks. -/
theorem counter_call_storage_bound {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {address : Address}
    {before after : BitVec 64 × TargetState World}
    (call : CounterCall interface heap calls address before after) (bound : Nat)
    (bounded : TargetStorageBound before.2.memory bound) (overflow : Bool)
    (flagRead : targetRead before.2.memory address = some (.bool overflow)) :
    TargetStorageBound after.2.memory bound := by
  obtain ⟨writtenMemory, writeDefined⟩ := targetWrite_defined_of_read flagRead (.bool true)
  have executed := (counter_run_exact interface heap calls before.1 call.increment address
    before.2 writtenMemory writeDefined call.outcome).mp call.executed
  have stateExact := call.postState.symm.trans
    ((congrArg TargetBlockOutcome.state executed).trans
      (counterOutcome_state before.1 call.increment address before.2 writtenMemory))
  rw [stateExact]
  by_cases exceeded : call.increment > BitVec.allOnes 64 - before.1
  · rw [if_pos exceeded]
    exact target_write_bound bounded writeDefined
  · rw [if_neg exceeded]
    exact bounded

private theorem counter_call_of_execution {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (address : Address)
    (before : BitVec 64 × TargetState World) (increment result : BitVec 64)
    (outcome : TargetBlockOutcome World) (finalOverflow : Bool)
    (ran : TargetRun interface heap calls .word counterCode counterCode
      (parameterFrame before.1 increment address) before.2 outcome)
    (returned : outcome.flow = .returned (.word result))
    (flag : targetRead outcome.state.memory address = some (.bool finalOverflow)) :
    ∃ after : BitVec 64 × TargetState World,
      ∃ call : CounterCall interface heap calls address before after,
        call.increment = increment ∧
        targetRead after.2.memory address = some (.bool finalOverflow) := by
  let call : CounterCall interface heap calls address before (result, outcome.state) := {
    increment, outcome, executed := ran, returned, postState := rfl }
  exact ⟨(result, outcome.state), call, rfl, flag⟩

/-- A live flag admits an actual helper execution for every unsigned
increment. This supplies call receipts rather than assuming routes exist. -/
theorem counter_call_exists {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (address : Address)
    (before : BitVec 64 × TargetState World) (increment : BitVec 64) (overflow : Bool)
    (flagRead : targetRead before.2.memory address = some (.bool overflow)) :
    ∃ after : BitVec 64 × TargetState World,
      ∃ call : CounterCall interface heap calls address before after,
        call.increment = increment ∧
        targetRead after.2.memory address = some (.bool
          (Mettapedia.Machines.NativeCostLedger.wordAddLowerBound
            before.1 increment overflow).2) := by
  obtain ⟨writtenMemory, writeDefined⟩ := targetWrite_defined_of_read flagRead (.bool true)
  exact counter_call_of_execution interface heap calls address before increment
    (Mettapedia.Machines.NativeCostLedger.wordAddLowerBound before.1 increment overflow).1
    (counterOutcome before.1 increment address before.2 writtenMemory)
    (Mettapedia.Machines.NativeCostLedger.wordAddLowerBound before.1 increment overflow).2
    ((counter_run_exact interface heap calls before.1 increment address before.2
      writtenMemory writeDefined _).mpr rfl)
    (counterOutcome_flow before.1 increment address overflow before.2 writtenMemory)
    (counterOutcome_flag before.1 increment address overflow before.2 writtenMemory
      flagRead writeDefined)

/-- Every finite list of increments has a route made of executions of the
admitted helper. Its event trace is exactly the supplied ordered list. -/
theorem counter_route_exists {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (address : Address)
    (increments : List (BitVec 64)) :
    ∀ (before : BitVec 64 × TargetState World) (overflow : Bool),
      targetRead before.2.memory address = some (.bool overflow) →
      ∃ after : BitVec 64 × TargetState World,
        ∃ route : Mettapedia.GSLT.Ultrainfinite.Route
            (CounterCall interface heap calls address) before after,
          (route.trace fun call => call.increment) = increments ∧
          ∃ finalOverflow : Bool,
            targetRead after.2.memory address = some (.bool finalOverflow) := by
  induction increments with
  | nil =>
      intro before overflow read
      exact ⟨before, .refl before, rfl, overflow, read⟩
  | cons increment rest ih =>
      intro before overflow read
      obtain ⟨middle, call, event, nextRead⟩ :=
        counter_call_exists interface heap calls address before increment overflow read
      obtain ⟨after, route, trace, finalOverflow, finalRead⟩ :=
        ih middle (Mettapedia.Machines.NativeCostLedger.wordAddLowerBound
          before.1 increment overflow).2 nextRead
      exact ⟨after, .cons call route, by simp only
        [Mettapedia.GSLT.Ultrainfinite.Route.trace, event, trace], finalOverflow, finalRead⟩

private theorem counter_route_word_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {address : Address}
    {before after : BitVec 64 × TargetState World}
    (route : Mettapedia.GSLT.Ultrainfinite.Route
      (CounterCall interface heap calls address) before after) :
    ∀ overflow : Bool, targetRead before.2.memory address = some (.bool overflow) →
      after.1 = (Mettapedia.Machines.NativeCostLedger.wordAccumulate before.1 overflow
        (route.trace fun call => call.increment)).1 ∧
      targetRead after.2.memory address = some (.bool
        (Mettapedia.Machines.NativeCostLedger.wordAccumulate before.1 overflow
          (route.trace fun call => call.increment)).2) ∧
      after.2.external = before.2.external ∧ after.2.fault = before.2.fault ∧
        after.2.memory.owned = before.2.memory.owned := by
  induction route with
  | refl state =>
      intro overflow read
      exact ⟨rfl, read, rfl, rfl, rfl⟩
  | @cons source middle target call rest ih =>
      intro overflow read
      obtain ⟨word, flag, external, fault, owned⟩ := counter_call_word_exact call overflow read
      obtain ⟨lastWord, lastFlag, lastExternal, lastFault, lastOwned⟩ :=
        ih (Mettapedia.Machines.NativeCostLedger.wordAddLowerBound
          source.1 call.increment overflow).2 flag
      rw [word] at lastWord lastFlag
      exact ⟨lastWord, lastFlag, lastExternal.trans external,
        lastFault.trans fault, lastOwned.trans owned⟩

/-- Every finite route of admitted helper calls implements cumulative
natural-number saturation and preserves the inherited overflow flag. The
external state, fault and allocation ownership survive the whole route. -/
theorem counter_route_correspondence {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {address : Address}
    {before after : BitVec 64 × TargetState World}
    (route : Mettapedia.GSLT.Ultrainfinite.Route
      (CounterCall interface heap calls address) before after)
    (overflow : Bool)
    (flagRead : targetRead before.2.memory address = some (.bool overflow)) :
    after.1.toNat = Mettapedia.Machines.NativeCostLedger.boundedTotal (2 ^ 64 - 1)
      (before.1.toNat + ((route.trace fun call => call.increment).map BitVec.toNat).sum) ∧
    targetRead after.2.memory address = some (.bool (overflow || decide
      (2 ^ 64 - 1 < before.1.toNat +
        ((route.trace fun call => call.increment).map BitVec.toNat).sum))) ∧
    after.2.external = before.2.external ∧ after.2.fault = before.2.fault ∧
      after.2.memory.owned = before.2.memory.owned := by
  obtain ⟨word, flag, external, fault, owned⟩ := counter_route_word_exact route overflow flagRead
  refine ⟨?_, ?_, external, fault, owned⟩
  · rw [word]
    exact Mettapedia.Machines.NativeCostLedger.wordAccumulate_value _ _ _
  · rw [Mettapedia.Machines.NativeCostLedger.wordAccumulate_flag] at flag
    exact flag

/-- The actual admitted helper's work-counter calls implement the numerical
coordinate of the observed ledger even when event identities or storage are
unavailable. The correspondence relates actual input increments, not returned
answers. It does not admit the enclosing C append or storage service. -/
theorem counter_route_recording_work {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {address : Address}
    {before after : BitVec 64 × TargetState World}
    (route : Mettapedia.GSLT.Ultrainfinite.Route
      (CounterCall interface heap calls address) before after)
    (overflow : Bool)
    (flagRead : targetRead before.2.memory address = some (.bool overflow))
    (maximum : Nat) (charges : List (Mettapedia.Machines.NativeCostLedger.Recording.Charge 64))
    (recording : Mettapedia.Machines.NativeCostLedger.Recording.State 64)
    (started : before.1 = recording.work)
    (increments : route.trace (fun call => call.increment) = charges.map (fun charge => charge.units)) :
    after.1.toNat =
        (Mettapedia.Machines.NativeCostLedger.Recording.run maximum charges recording).work.toNat ∧
      after.2.external = before.2.external ∧ after.2.fault = before.2.fault ∧
        after.2.memory.owned = before.2.memory.owned := by
  obtain ⟨work, _, external, fault, owned⟩ := counter_route_correspondence route overflow flagRead
  refine ⟨?_, external, fault, owned⟩
  rw [Mettapedia.Machines.NativeCostLedger.Recording.run_work]
  simpa only [started, increments, List.map_map, Function.comp_def] using work

/-- A complete newly initialized ledger's recorded history recovers the
actual admitted helper route's saturated work. Incomplete histories retain
the numerical comparison above, without this stronger reconstruction claim. -/
theorem counter_route_complete_recording_history {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {address : Address}
    {before after : BitVec 64 × TargetState World}
    (route : Mettapedia.GSLT.Ultrainfinite.Route
      (CounterCall interface heap calls address) before after)
    (overflow : Bool)
    (flagRead : targetRead before.2.memory address = some (.bool overflow))
    (maximum : Nat) (charges : List (Mettapedia.Machines.NativeCostLedger.Recording.Charge 64))
    (started : before.1 = 0)
    (increments : route.trace (fun call => call.increment) = charges.map (fun charge => charge.units))
    (complete : (Mettapedia.Machines.NativeCostLedger.Recording.run maximum charges
      (Mettapedia.Machines.NativeCostLedger.Recording.initial 64)).traceIncomplete = false) :
    after.1.toNat = Mettapedia.Machines.NativeCostLedger.boundedTotal (2 ^ 64 - 1)
      (Mettapedia.Machines.NativeCostLedger.snapshot
        (Mettapedia.Machines.NativeCostLedger.Recording.run maximum charges
          (Mettapedia.Machines.NativeCostLedger.Recording.initial 64)).history).2 :=
  (counter_route_recording_work route overflow flagRead maximum charges
    (Mettapedia.Machines.NativeCostLedger.Recording.initial 64) started increments).1.trans
    (Mettapedia.Machines.NativeCostLedger.Recording.complete_work maximum charges complete)

/-- A whole cumulative route preserves its initial finite storage bound.
Every intermediate receipt consequently retains fresh function-entry
capacity for further calls or resumed increments. -/
theorem counter_route_storage_bound {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {address : Address}
    {before after : BitVec 64 × TargetState World}
    (route : Mettapedia.GSLT.Ultrainfinite.Route
      (CounterCall interface heap calls address) before after) (bound : Nat) :
    TargetStorageBound before.2.memory bound →
    ∀ overflow : Bool, targetRead before.2.memory address = some (.bool overflow) →
      TargetStorageBound after.2.memory bound := by
  induction route with
  | refl _ => intro bounded _ _; exact bounded
  | @cons source middle target call rest ih =>
      intro bounded overflow read
      have nextBound := counter_call_storage_bound call bound bounded overflow read
      have nextFlag := (counter_call_word_exact call overflow read).2.1
      exact ih nextBound
        (Mettapedia.Machines.NativeCostLedger.wordAddLowerBound source.1 call.increment overflow).2
        nextFlag

/-- Positive control at the full function boundary: reading or resuming a
counter with a zero increment preserves a previously true flag and the
complete caller state. -/
theorem counter_function_zero_preserves_caller {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (left : BitVec 64) (address : Address) (state : TargetState World)
    (finite : TargetFiniteStorage state.memory)
    (flagRead : targetRead state.memory address = some (.bool true)) :
    TargetFunctionBody interface heap calls counterFunction
      [.word left, .word 0, .reference (some address)] state ⟨.word left, state⟩ := by
  obtain ⟨writtenMemory, writeDefined⟩ := targetWrite_defined_of_read flagRead (.bool true)
  apply (counter_function_exact interface heap calls left 0 address true state writtenMemory
    flagRead writeDefined _).mpr
  refine ⟨target_finite_fresh finite, ?_⟩
  have value := Mettapedia.Machines.NativeCostLedger.word_add_zero left false
  have notExceeded : ¬(0 : BitVec 64) > BitVec.allOnes 64 - left := by
    change ¬BitVec.allOnes 64 - left < (0 : BitVec 64)
    have zeroRead : (0 : BitVec 64).toNat = 0 := rfl
    rw [BitVec.lt_def, zeroRead]
    exact Nat.not_lt_zero _
  simp only [counterFunctionOutcome, value, if_neg notExceeded]

/-- The complete function can reach the exact maximum without setting
overflow or changing any caller storage. Equality at the bound belongs to
the ordinary-addition branch, so changing its strict guard is unsound. -/
theorem counter_function_exact_maximum_preserves_caller {World : Type}
    (interface : Interface) (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (address : Address) (state : TargetState World)
    (finite : TargetFiniteStorage state.memory)
    (flagRead : targetRead state.memory address = some (.bool false)) :
    TargetFunctionBody interface heap calls counterFunction
      [.word 0, .word (BitVec.allOnes 64), .reference (some address)] state
      ⟨.word (BitVec.allOnes 64), state⟩ := by
  obtain ⟨writtenMemory, writeDefined⟩ := targetWrite_defined_of_read flagRead (.bool true)
  apply (counter_function_exact interface heap calls 0 (BitVec.allOnes 64) address false
    state writtenMemory flagRead writeDefined _).mpr
  refine ⟨target_finite_fresh finite, ?_⟩
  have notExceeded : ¬BitVec.allOnes 64 > BitVec.allOnes 64 - (0 : BitVec 64) := by simp
  simp only [counterFunctionOutcome,
    Mettapedia.Machines.NativeCostLedger.word_exact_maximum, if_neg notExceeded]

/-- Adding zero units preserves an inherited overflow flag. -/
theorem counter_sticky_control (left : BitVec 64) :
    Mettapedia.Machines.NativeCostLedger.wordAddLowerBound left 0 true =
      (left, true) :=
  Mettapedia.Machines.NativeCostLedger.word_add_zero left true

/-- Negative control for every call-return source recognized by the common
parser. Syntax recognition cannot authorize an external call in this profile. -/
theorem counter_call_source_refused (source : List Char) (callee : NativeC.Name)
    (arguments : List NativeC.CExpr)
    (parsed : NativeC.blockText? ["uint64_t".toList, "bool".toList] source =
      some [.return (some (.call callee arguments))]) :
    NativeC.primitiveBodyText? ["uint64_t".toList, "bool".toList]
      counterBindings .word source ⟨3⟩ = none := by
  unfold NativeC.primitiveBodyText?
  rw [parsed]
  exact NativeC.primitiveStatements_return_call_refused _ _ _ _ _ _

/-! ## The actual receipt wrapper

The active-scope query and observed charge have separately declared types.
Admitting the wrapper does not certify either service implementation. The
disabled-path theorem below needs only the query's whole-state contract.
-/

def chargeGuardSource : List Char :=
  "static inline uint64_t cetta_native_cost_charge(CettaNativeCostKind kind, uint64_t units) {\n    return cetta_native_cost_active()\n        ? cetta_native_cost_charge_observed(kind, units) : 0u;\n}".toList

def chargeGuardHeader : Header :=
  ⟨"cetta_native_cost_charge", [⟨"kind", .named "CostKind"⟩, ⟨"units", .word⟩], .word⟩

def chargeGuardActive : External :=
  ⟨⟨"cetta_native_cost_active", [], .bool⟩, "cetta_native_cost_active", .pure, none⟩

def chargeGuardObserved : External :=
  ⟨⟨"cetta_native_cost_charge_observed", chargeGuardHeader.parameters, .word⟩,
    "cetta_native_cost_charge_observed", .effect, none⟩

def chargeGuardRepresentation : NativeC.Representation :=
  ⟨"NativeCostGuard", ⟨[], [⟨"CostKind", "CettaNativeCostKind", "native_cost.h"⟩], [],
    [chargeGuardActive, chargeGuardObserved]⟩, []⟩

def chargeGuardCode : List Instruction :=
  [.call (some (.temporary 3 .bool)) (.external "cetta_native_cost_active") [],
   .branch (.value (.temporary 3 .bool))
     [.call (some (.temporary 4 .word)) (.external "cetta_native_cost_charge_observed")
       [.temporary 1 (.named "CostKind"), .temporary 2 .word],
      .return (.temporary 4 .word)] [.return (.word 0)]]

def chargeGuardFunction : NativeIR.Function :=
  ⟨chargeGuardHeader,
    [.temporary 1 (.named "CostKind") (.readLocal "kind"),
     .temporary 2 .word (.readLocal "units")] ++ chargeGuardCode, 4⟩

def chargeGuardProgram : NativeIR.Program :=
  ⟨chargeGuardRepresentation.moduleName, chargeGuardRepresentation.interface, [chargeGuardFunction]⟩

private def chargeGuardTokens : List NativeC.Token :=
  [.identifier "static".toList, .identifier "inline".toList,
   .identifier "uint64_t".toList, .identifier "cetta_native_cost_charge".toList,
   .punctuation ['('], .identifier "CettaNativeCostKind".toList,
   .identifier "kind".toList, .punctuation [','], .identifier "uint64_t".toList,
   .identifier "units".toList, .punctuation [')'], .punctuation ['{'],
   .identifier "return".toList, .identifier "cetta_native_cost_active".toList,
   .punctuation ['('], .punctuation [')'], .punctuation ['?'],
   .identifier "cetta_native_cost_charge_observed".toList, .punctuation ['('],
   .identifier "kind".toList, .punctuation [','], .identifier "units".toList,
   .punctuation [')'], .punctuation [':'], .number ['0', 'u'],
   .punctuation [';'], .punctuation ['}']]

private def chargeGuardParsed : NativeC.CFunction :=
  ⟨⟨"uint64_t".toList, 0⟩, "cetta_native_cost_charge".toList,
    [⟨⟨"CettaNativeCostKind".toList, 0⟩, "kind".toList⟩,
     ⟨⟨"uint64_t".toList, 0⟩, "units".toList⟩],
    [.return (some (.conditional (.call "cetta_native_cost_active".toList [])
      (.call "cetta_native_cost_charge_observed".toList
        [.identifier "kind".toList, .identifier "units".toList])
      (.unsignedInteger 0)))]⟩

private theorem chargeGuard_lexed : NativeC.lex chargeGuardSource = .ok chargeGuardTokens :=
  by decide +kernel

private theorem chargeGuard_parsed : NativeC.function?
    (2 * chargeGuardTokens.length + 4) ["uint64_t".toList, "CettaNativeCostKind".toList]
    (NativeC.ordinaryFunctionTokens chargeGuardTokens) = some (chargeGuardParsed, []) := by rfl

private def chargeGuardBindings : NativeC.PrimitiveBindings :=
  [("kind".toList, .temporary 1 (.named "CostKind")), ("units".toList, .temporary 2 .word)]

private theorem chargeGuard_active_normalized (representation : NativeC.Representation) :
    NativeC.primitiveExpression?
    chargeGuardBindings 193 (.call "cetta_native_cost_active".toList []) ⟨2⟩
    [chargeGuardActive, chargeGuardObserved] representation =
    some ⟨[.call (some (.temporary 3 .bool)) (.external "cetta_native_cost_active") []],
      .temporary 3 .bool, ⟨3⟩⟩ := by
  simp only [NativeC.primitiveExpression?]
  rfl

private theorem chargeGuard_observed_normalized (representation : NativeC.Representation) :
    NativeC.primitiveExpression?
    chargeGuardBindings 192 (.call "cetta_native_cost_charge_observed".toList
      [.identifier "kind".toList, .identifier "units".toList]) ⟨3⟩
    [chargeGuardActive, chargeGuardObserved] representation =
    some ⟨[.call (some (.temporary 4 .word)) (.external "cetta_native_cost_charge_observed")
      [.temporary 1 (.named "CostKind"), .temporary 2 .word]],
      .temporary 4 .word, ⟨4⟩⟩ := by
  simp only [NativeC.primitiveExpression?]
  rfl

private theorem chargeGuard_observed_return_normalized (representation : NativeC.Representation) :
    NativeC.primitiveStatement?
    chargeGuardBindings .word 193
    (.return (some (.call "cetta_native_cost_charge_observed".toList
      [.identifier "kind".toList, .identifier "units".toList]))) ⟨3⟩
    [chargeGuardActive, chargeGuardObserved] representation =
    some ([.call (some (.temporary 4 .word)) (.external "cetta_native_cost_charge_observed")
      [.temporary 1 (.named "CostKind"), .temporary 2 .word],
      .return (.temporary 4 .word)], ⟨4⟩) := by
  simp only [NativeC.primitiveStatement?, chargeGuard_observed_normalized]
  rfl

private theorem chargeGuard_conditional_normalized (representation : NativeC.Representation) :
    NativeC.primitiveStatement?
    chargeGuardBindings .word 194
    (.return (some (.conditional (.call "cetta_native_cost_active".toList [])
      (.call "cetta_native_cost_charge_observed".toList
        [.identifier "kind".toList, .identifier "units".toList])
      (.unsignedInteger 0)))) ⟨2⟩
    [chargeGuardActive, chargeGuardObserved] representation = some (chargeGuardCode, ⟨4⟩) := by
  rw [NativeC.primitiveStatement?, chargeGuard_active_normalized]
  dsimp only [bind, Option.bind]
  change (do
    let first ← NativeC.primitiveStatement? chargeGuardBindings .word 193
      (.return (some (.call "cetta_native_cost_charge_observed".toList
        [.identifier "kind".toList, .identifier "units".toList]))) ⟨3⟩
      [chargeGuardActive, chargeGuardObserved] representation
    let second ← NativeC.primitiveStatement? chargeGuardBindings .word 193
      (.return (some (.unsignedInteger 0))) first.2
      [chargeGuardActive, chargeGuardObserved] representation
    some ([Instruction.call (some (.temporary 3 .bool)) (.external "cetta_native_cost_active") []] ++
      [Instruction.branch (.value (.temporary 3 .bool)) first.1 second.1], second.2)) = _
  rw [chargeGuard_observed_return_normalized]
  rfl

private theorem chargeGuard_body_normalized (representation : NativeC.Representation) :
    NativeC.primitiveStatements?
    chargeGuardBindings .word 195 chargeGuardParsed.body ⟨2⟩
    [chargeGuardActive, chargeGuardObserved] representation = some (chargeGuardCode, ⟨4⟩) := by
  change NativeC.primitiveStatements? chargeGuardBindings .word 195
    [.return (some (.conditional (.call "cetta_native_cost_active".toList [])
      (.call "cetta_native_cost_charge_observed".toList
        [.identifier "kind".toList, .identifier "units".toList])
      (.unsignedInteger 0)))] ⟨2⟩
    [chargeGuardActive, chargeGuardObserved] representation = _
  rw [NativeC.primitiveStatements?, chargeGuard_conditional_normalized]
  rfl

theorem chargeGuard_source_admitted : NativeC.primitiveFunctionText?
    chargeGuardRepresentation ["uint64_t".toList, "CettaNativeCostKind".toList]
    chargeGuardHeader [] chargeGuardSource = some chargeGuardFunction := by
  rw [NativeC.primitive_function_text_of_parts chargeGuardRepresentation
    ["uint64_t".toList, "CettaNativeCostKind".toList] chargeGuardHeader []
    chargeGuardSource chargeGuardTokens chargeGuardParsed chargeGuard_lexed chargeGuard_parsed]
  apply NativeC.primitive_function_of_parts chargeGuardRepresentation chargeGuardHeader []
    (chargeGuardSource.length + 1) chargeGuardParsed .word chargeGuardCode ⟨4⟩
  · rfl
  · rfl
  · rfl
  · have length : chargeGuardSource.length + 1 = 195 := by decide +kernel
    rw [length]
    exact chargeGuard_body_normalized chargeGuardRepresentation

/-- The same source without explicit action declarations cannot be admitted,
even though the active query and conditional syntax have been recognized. -/
theorem chargeGuard_missing_catalogue_refused : NativeC.primitiveFunctionText?
    { chargeGuardRepresentation with interface :=
      { chargeGuardRepresentation.interface with externals := [] } }
    ["uint64_t".toList, "CettaNativeCostKind".toList]
    chargeGuardHeader [] chargeGuardSource = none := by
  rw [NativeC.primitive_function_text_of_parts _
    ["uint64_t".toList, "CettaNativeCostKind".toList] chargeGuardHeader []
    chargeGuardSource chargeGuardTokens chargeGuardParsed chargeGuard_lexed chargeGuard_parsed]
  have length : chargeGuardSource.length + 1 = 195 := by decide +kernel
  rw [length]
  have bodyRefused : NativeC.primitiveStatements? chargeGuardBindings .word 195
      chargeGuardParsed.body ⟨2⟩ []
      { chargeGuardRepresentation with interface :=
        { chargeGuardRepresentation.interface with externals := [] } } = none := by
    dsimp only [chargeGuardParsed]
    rw [NativeC.primitiveStatements?, NativeC.primitiveStatement?,
      NativeC.primitiveExpression?]
    rfl
  exact NativeC.primitive_function_body_refused _ chargeGuardHeader [] 195 chargeGuardParsed
    .word (by rfl) (by rfl) (by rfl) bodyRefused

/-- The wrapper's two ordinary by-value parameter cells at invocation entry. -/
def chargeGuardBound {World : Type} (state : TargetState World) (storage : Nat)
    (kind : TargetValue) (units : BitVec 64) : TargetFrame × TargetState World :=
  let first := targetDeclareLocal (targetEmptyFrame storage) state "kind" (.named "CostKind") kind
  targetDeclareLocal first.1 first.2 "units" .word (.word units)

private def chargeGuardCaptured (frame : TargetFrame) (kind : TargetValue)
    (units : BitVec 64) : TargetFrame :=
  targetDeclareTemporary (targetDeclareTemporary frame 1 kind) 2 (.word units)

private def chargeGuardOutcome {World : Type} (frame : TargetFrame) (kind : TargetValue)
    (units : BitVec 64) (post : TargetState World) : TargetBlockOutcome World :=
  ⟨.returned (.word 0),
    targetDeclareTemporary (chargeGuardCaptured frame kind units) 3 (.bool false), post⟩

private theorem chargeGuard_parameters_readback {World : Type} (state : TargetState World)
    (storage : Nat) (kind : TargetValue) (units : BitVec 64) :
    let bound := chargeGuardBound state storage kind units
    targetLocalValue bound.1 bound.2 "kind" = some kind ∧
      targetLocalValue bound.1 bound.2 "units" = some (.word units) := by
  simp [chargeGuardBound, targetDeclareLocal, targetEmptyFrame, targetLocalValue,
    targetLocalAddress, targetRead, targetStoreCell, targetReadPath]

/-- Both arms use the same argument-capture prefix, before the query runs. -/
private theorem chargeGuard_capture_prefix_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (kind : TargetValue) (units : BitVec 64)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .word root chargeGuardFunction.body
      (chargeGuardBound state storage kind units).1 (chargeGuardBound state storage kind units).2 out ↔
      TargetRun interface heap calls .word root chargeGuardCode
        (chargeGuardCaptured (chargeGuardBound state storage kind units).1 kind units)
        (chargeGuardBound state storage kind units).2 out := by
  let bound := chargeGuardBound state storage kind units
  obtain ⟨kindRead, unitsRead⟩ := chargeGuard_parameters_readback state storage kind units
  change TargetRun interface heap calls .word root
    (.temporary 1 (.named "CostKind") (.readLocal "kind") ::
     .temporary 2 .word (.readLocal "units") :: chargeGuardCode) bound.1 bound.2 out ↔ _
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : bound.1.temporaryNames.contains 1 = false) (.local kindRead))]
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : (targetDeclareTemporary bound.1 1 kind).temporaryNames.contains 2 = false)
    (.local unitsRead))]
  rfl

private theorem chargeGuard_captured_operands {World : Type} (interface : Interface)
    (frame : TargetFrame) (kind : TargetValue) (units : BitVec 64) (queried : TargetState World) :
    TargetAtomsEval interface
      (targetDeclareTemporary (chargeGuardCaptured frame kind units) 3 (.bool true)) queried
      [.temporary 1 (.named "CostKind"), .temporary 2 .word] [kind, .word units] := by
  constructor
  · exact .temporary (by simp [chargeGuardCaptured, targetDeclareTemporary])
      (by simp [chargeGuardCaptured, targetDeclareTemporary])
  · constructor
    · exact .temporary (by simp [chargeGuardCaptured, targetDeclareTemporary])
        (by simp [chargeGuardCaptured, targetDeclareTemporary])
    · exact .nil

/-- Captured ordinary arguments precede the active query. Returning false
skips the observed service even when the query has a nontrivial post-state. -/
private theorem chargeGuard_body_inactive_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (kind : TargetValue) (units : BitVec 64)
    (post : TargetState World)
    (query : ∀ raw after, calls (.external "cetta_native_cost_active") []
      (chargeGuardBound state storage kind units).2 raw after ↔
        raw = .bool false ∧ after = post)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    let bound := chargeGuardBound state storage kind units
    TargetRun interface heap calls .word root chargeGuardFunction.body bound.1 bound.2 out ↔
      out = chargeGuardOutcome bound.1 kind units post := by
  let bound := chargeGuardBound state storage kind units
  dsimp only
  rw [chargeGuard_capture_prefix_exact]
  have complete : ∀ candidate,
      (chargeGuardCaptured bound.1 kind units).temporaryNames.contains candidate = false →
        (chargeGuardCaptured bound.1 kind units).temporaries candidate = none :=
    target_declared_names_complete _ _ _
      (target_declared_names_complete _ _ _ (by intro _ _; rfl))
  exact target_inactive_call_guard_exact
    (by rfl : (chargeGuardCaptured bound.1 kind units).temporaryNames.contains 3 = false)
    complete query root out

private def chargeGuardActiveOutcome {World : Type} (frame : TargetFrame)
    (kind : TargetValue) (units : BitVec 64) (value : TargetValue)
    (post : TargetState World) : TargetBlockOutcome World :=
  ⟨.returned value,
    targetDeclareTemporary (chargeGuardCaptured frame kind units) 3 (.bool true), post⟩

/-- The enabled arm forwards the captured arguments and returns each actual
accounting result. The query's post-state precedes that service, whose whole
post-state survives the branch. -/
private theorem chargeGuard_body_active_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (kind : TargetValue) (units : BitVec 64)
    (queried : TargetState World)
    (query : ∀ raw after, calls (.external "cetta_native_cost_active") []
      (chargeGuardBound state storage kind units).2 raw after ↔
        raw = .bool true ∧ after = queried)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    let bound := chargeGuardBound state storage kind units
    TargetRun interface heap calls .word root chargeGuardFunction.body bound.1 bound.2 out ↔
      ∃ value post, calls (.external "cetta_native_cost_charge_observed")
        [kind, .word units] queried value post ∧
        out = chargeGuardActiveOutcome bound.1 kind units value post := by
  let bound := chargeGuardBound state storage kind units
  dsimp only
  rw [chargeGuard_capture_prefix_exact]
  have complete : ∀ candidate,
      (chargeGuardCaptured bound.1 kind units).temporaryNames.contains candidate = false →
        (chargeGuardCaptured bound.1 kind units).temporaries candidate = none :=
    target_declared_names_complete _ _ _
      (target_declared_names_complete _ _ _ (by intro _ _; rfl))
  exact target_active_call_guard_exact
    (by rfl : (chargeGuardCaptured bound.1 kind units).temporaryNames.contains 3 = false)
    (by rfl : (targetDeclareTemporary (chargeGuardCaptured bound.1 kind units)
      3 (.bool true)).temporaryNames.contains 4 = false)
    complete query (chargeGuard_captured_operands interface bound.1 kind units queried) root out

private theorem chargeGuard_teardown {World : Type} (state : TargetState World)
    (storage : Nat) (kind : TargetValue) (units : BitVec 64)
    (fresh : targetFreshFrame state.memory storage) :
    let bound := chargeGuardBound state storage kind units
    (targetLeaveScope (targetEmptyFrame storage)
      (chargeGuardOutcome bound.1 kind units bound.2).frame bound.2).2 = state := by
  let bound := chargeGuardBound state storage kind units
  have boundParameters : targetBindParameters chargeGuardHeader.parameters [kind, .word units]
      (targetEmptyFrame storage) state = some bound := by rfl
  obtain ⟨_, _, _, stateExact⟩ := target_bind_parameters_facts chargeGuardHeader.parameters
    [kind, .word units] (targetEmptyFrame storage) state bound.1 bound.2 boundParameters
  obtain ⟨_, _, released⟩ := target_bound_parameters_release chargeGuardHeader.parameters
    [kind, .word units] storage state bound.1 bound.2 fresh boundParameters
  change { bound.2 with memory := targetDropLocals bound.2.memory storage 0 2 } = state
  change targetDropLocals bound.2.memory storage 0 2 = state.memory at released
  rw [released, stateExact]

/-- A single actual false query realizes the wrapper and returns its full
post-state after releasing parameter cells. The observed service is absent
from the premises and from the executed branch. -/
theorem chargeGuard_inactive_function_of_call {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (kind : TargetValue) (units : BitVec 64) (state : TargetState World) (storage : Nat)
    (post : TargetState World) (fresh : targetFreshFrame state.memory storage)
    (query : calls (.external "cetta_native_cost_active") []
      (chargeGuardBound state storage kind units).2 (.bool false) post) :
    TargetFunctionBody interface heap calls chargeGuardFunction [kind, .word units] state
      ⟨.word 0, { post with memory := targetDropLocals post.memory storage 0 2 }⟩ := by
  let bound := chargeGuardBound state storage kind units
  have complete : ∀ candidate,
      (chargeGuardCaptured bound.1 kind units).temporaryNames.contains candidate = false →
        (chargeGuardCaptured bound.1 kind units).temporaries candidate = none :=
    target_declared_names_complete _ _ _
      (target_declared_names_complete _ _ _ (by intro _ _; rfl))
  have body : TargetRun interface heap calls .word chargeGuardFunction.body chargeGuardFunction.body
      bound.1 bound.2 (chargeGuardOutcome bound.1 kind units post) := by
    apply (chargeGuard_capture_prefix_exact interface heap calls state storage kind units _ _).mpr
    exact target_inactive_call_guard_of_call
      (by rfl : (chargeGuardCaptured bound.1 kind units).temporaryNames.contains 3 = false)
      complete query chargeGuardFunction.body
  have executed : TargetFunctionBody interface heap calls chargeGuardFunction [kind, .word units] state
      ⟨.word 0, (targetLeaveScope (targetEmptyFrame storage)
        (chargeGuardOutcome bound.1 kind units post).frame post).2⟩ :=
    .run fresh (by rfl) body rfl
  exact executed

/-- The actual admitted wrapper returns zero and preserves every caller
field when the active query is state-preserving on the caller's world.
Temporary invocation cells are released; the observed service is unrestricted. -/
theorem chargeGuard_inactive_function_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (kind : TargetValue) (units : BitVec 64) (state : TargetState World)
    (query : ∀ middle, middle.external = state.external → ∀ raw after,
      calls (.external "cetta_native_cost_active") [] middle raw after ↔
        raw = .bool false ∧ after = middle)
    (result : TargetRawResult World) :
    TargetFunctionBody interface heap calls chargeGuardFunction [kind, .word units] state result ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧ result = ⟨.word 0, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | @run storage frame bound out raw fresh parameters body returned =>
      have parameterPair : (frame, bound) = chargeGuardBound state storage kind units :=
        (Option.some.inj parameters).symm
      have frameEq : frame = (chargeGuardBound state storage kind units).1 :=
        congrArg Prod.fst parameterPair
      have stateEq : bound = (chargeGuardBound state storage kind units).2 :=
        congrArg Prod.snd parameterPair
      subst frame
      subst bound
      have executed := (chargeGuard_body_inactive_exact interface heap calls state storage
        kind units (chargeGuardBound state storage kind units).2
        (query _ rfl) chargeGuardFunction.body out).mp body
      have rawExact : raw = .word 0 := TargetFlow.returned.inj
        (returned.symm.trans (congrArg TargetBlockOutcome.flow executed))
      refine ⟨⟨storage, fresh⟩, ?_⟩
      rw [rawExact, executed]
      change TargetRawResult.mk (.word 0) (targetLeaveScope (targetEmptyFrame storage)
        (chargeGuardOutcome (chargeGuardBound state storage kind units).1 kind units
          (chargeGuardBound state storage kind units).2).frame
        (chargeGuardBound state storage kind units).2).2 = ⟨.word 0, state⟩
      rw [chargeGuard_teardown state storage kind units fresh]
  · rintro ⟨⟨storage, fresh⟩, rfl⟩
    let bound := chargeGuardBound state storage kind units
    have executed : TargetFunctionBody interface heap calls chargeGuardFunction
        [kind, .word units] state
        ⟨.word 0, (targetLeaveScope (targetEmptyFrame storage)
          (chargeGuardOutcome bound.1 kind units bound.2).frame bound.2).2⟩ :=
      .run fresh (by rfl)
        ((chargeGuard_body_inactive_exact interface heap calls state storage kind units bound.2
          (query _ rfl) chargeGuardFunction.body _).mpr rfl) rfl
    rw [chargeGuard_teardown state storage kind units fresh] at executed
    exact executed

/-- Finite caller storage realizes the disabled wrapper, rather than only
constraining a possibly empty relation. -/
theorem chargeGuard_inactive_function_realization {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (kind : TargetValue) (units : BitVec 64) (state : TargetState World)
    (finite : TargetFiniteStorage state.memory)
    (query : ∀ middle, middle.external = state.external → ∀ raw after,
      calls (.external "cetta_native_cost_active") [] middle raw after ↔
        raw = .bool false ∧ after = middle) :
    TargetFunctionBody interface heap calls chargeGuardFunction [kind, .word units]
      state ⟨.word 0, state⟩ :=
  (chargeGuard_inactive_function_exact interface heap calls kind units state query _).mpr
    ⟨target_finite_fresh finite, rfl⟩

/-- Two actual service responses suffice to realize the admitted wrapper.
Unlike a global service contract, these witnesses can name exact ordered
invocations. The observed response starts from the query's full post-state. -/
theorem chargeGuard_active_function_of_calls {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (kind : TargetValue) (units : BitVec 64) (state : TargetState World) (storage : Nat)
    (queried post : TargetState World) (value : TargetValue)
    (fresh : targetFreshFrame state.memory storage)
    (query : calls (.external "cetta_native_cost_active") []
      (chargeGuardBound state storage kind units).2 (.bool true) queried)
    (observed : calls (.external "cetta_native_cost_charge_observed")
      [kind, .word units] queried value post) :
    TargetFunctionBody interface heap calls chargeGuardFunction [kind, .word units] state
      ⟨value, { post with memory := targetDropLocals post.memory storage 0 2 }⟩ := by
  let bound := chargeGuardBound state storage kind units
  have complete : ∀ candidate,
      (chargeGuardCaptured bound.1 kind units).temporaryNames.contains candidate = false →
        (chargeGuardCaptured bound.1 kind units).temporaries candidate = none :=
    target_declared_names_complete _ _ _
      (target_declared_names_complete _ _ _ (by intro _ _; rfl))
  have body : TargetRun interface heap calls .word chargeGuardFunction.body chargeGuardFunction.body
      bound.1 bound.2 (chargeGuardActiveOutcome bound.1 kind units value post) := by
    apply (chargeGuard_capture_prefix_exact interface heap calls state storage kind units _ _).mpr
    exact target_active_call_guard_of_calls
      (by rfl : (chargeGuardCaptured bound.1 kind units).temporaryNames.contains 3 = false)
      (by rfl : (targetDeclareTemporary (chargeGuardCaptured bound.1 kind units)
        3 (.bool true)).temporaryNames.contains 4 = false)
      complete query (chargeGuard_captured_operands interface bound.1 kind units queried)
      observed chargeGuardFunction.body
  have executed : TargetFunctionBody interface heap calls chargeGuardFunction [kind, .word units] state
      ⟨value, (targetLeaveScope (targetEmptyFrame storage)
        (chargeGuardActiveOutcome bound.1 kind units value post).frame post).2⟩ :=
    .run fresh (by rfl) body rfl
  exact executed

/-- The enabled wrapper's two service occurrences, including their complete
intermediate states. Their external contracts are checked separately. -/
def chargeGuardActiveChildren {World : Type} (state : TargetState World) (storage : Nat)
    (kind : TargetValue) (units : BitVec 64) (queried post : TargetState World)
    (value : TargetValue) : List (TargetCallTree World) :=
  [.primitive "cetta_native_cost_active" [] (chargeGuardBound state storage kind units).2
      (.bool true) queried,
   .primitive "cetta_native_cost_charge_observed" [kind, .word units] queried value post]

/-- The disabled wrapper retains just its false query occurrence. -/
def chargeGuardInactiveChildren {World : Type} (state : TargetState World) (storage : Nat)
    (kind : TargetValue) (units : BitVec 64) (post : TargetState World) : List (TargetCallTree World) :=
  [.primitive "cetta_native_cost_active" [] (chargeGuardBound state storage kind units).2
      (.bool false) post]

/-- A disabled invocation consumes exactly its query child. No charge child
or observed-service hypothesis is needed to execute the actual body. -/
theorem chargeGuard_inactive_function_node {World : Type} (heap : TargetHeapSemantics World)
    (state : TargetState World) (storage : Nat) (kind : TargetValue) (units : BitVec 64)
    (post : TargetState World) (position : Nat) (fresh : targetFreshFrame state.memory storage) :
    targetFunctionNode chargeGuardProgram heap chargeGuardHeader.name [kind, .word units] state (.word 0)
      { post with memory := targetDropLocals post.memory storage 0 2 }
      (chargeGuardInactiveChildren state storage kind units post) position := by
  let children := chargeGuardInactiveChildren state storage kind units post
  let first : TargetStampedCall World :=
    ⟨.primitive "cetta_native_cost_active" [] (chargeGuardBound state storage kind units).2
      (.bool false) post, position + 1, position + 2⟩
  have member : first ∈ targetStampChildren children (position + 1) := List.mem_cons_self
  refine ⟨chargeGuardFunction, rfl, ?_⟩
  exact chargeGuard_inactive_function_of_call chargeGuardProgram.interface (targetHeapWithCursor heap)
    (targetLedgerCall children (position + 1)) kind units (targetWithCursor state (position + 1))
    storage (targetWithCursor post (position + 2)) fresh (target_ledger_call_of_member member)

/-- An actual false service response validates the disabled call tree without
any assumption on the unexecuted accounting service. -/
theorem chargeGuard_inactive_call_tree_valid {World : Type} (heap : TargetHeapSemantics World)
    (external : TargetExternalSemantics World) (state : TargetState World) (storage : Nat)
    (kind : TargetValue) (units : BitVec 64) (post : TargetState World)
    (position : Nat) (fresh : targetFreshFrame state.memory storage)
    (query : external.call "cetta_native_cost_active" []
      (chargeGuardBound state storage kind units).2 (.bool false) post) :
    targetValidCallTree chargeGuardProgram heap external
      (.function chargeGuardHeader.name [kind, .word units] state (.word 0)
        { post with memory := targetDropLocals post.memory storage 0 2 }
        (chargeGuardInactiveChildren state storage kind units post)) position := by
  rw [targetValidCallTree]
  constructor
  · exact chargeGuard_inactive_function_node heap state storage kind units post position fresh
  · simp only [chargeGuardInactiveChildren, targetValidChildren, targetValidCallTree]
    exact ⟨⟨⟨chargeGuardActive, rfl⟩, query⟩, trivial⟩

/-- The admitted C wrapper consumes the query and observed call in order.
This constructs the existing invocation certificate by executing its body;
the cursor is not an assumed annotation on the returned value. -/
theorem chargeGuard_active_function_node {World : Type} (heap : TargetHeapSemantics World)
    (state : TargetState World) (storage : Nat) (kind : TargetValue) (units : BitVec 64)
    (queried post : TargetState World) (value : TargetValue) (position : Nat)
    (fresh : targetFreshFrame state.memory storage) :
    targetFunctionNode chargeGuardProgram heap chargeGuardHeader.name [kind, .word units] state value
      { post with memory := targetDropLocals post.memory storage 0 2 }
      (chargeGuardActiveChildren state storage kind units queried post value) position := by
  let children := chargeGuardActiveChildren state storage kind units queried post value
  let first : TargetStampedCall World :=
    ⟨.primitive "cetta_native_cost_active" [] (chargeGuardBound state storage kind units).2
      (.bool true) queried, position + 1, position + 2⟩
  let second : TargetStampedCall World :=
    ⟨.primitive "cetta_native_cost_charge_observed" [kind, .word units] queried value post,
      position + 2, position + 3⟩
  have firstMember : first ∈ targetStampChildren children (position + 1) := List.mem_cons_self
  have secondMember : second ∈ targetStampChildren children (position + 1) :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have query := target_ledger_call_of_member firstMember
  have observed := target_ledger_call_of_member secondMember
  refine ⟨chargeGuardFunction, rfl, ?_⟩
  exact chargeGuard_active_function_of_calls chargeGuardProgram.interface (targetHeapWithCursor heap)
    (targetLedgerCall children (position + 1)) kind units (targetWithCursor state (position + 1))
    storage (targetWithCursor queried (position + 2)) (targetWithCursor post (position + 3)) value
    fresh query observed

/-- Actual admitted service responses validate the ordered invocation tree.
The hypotheses concern the two primitive leaves, not wrapper correctness. -/
theorem chargeGuard_active_call_tree_valid {World : Type} (heap : TargetHeapSemantics World)
    (external : TargetExternalSemantics World) (state : TargetState World) (storage : Nat)
    (kind : TargetValue) (units : BitVec 64) (queried post : TargetState World)
    (value : TargetValue) (position : Nat) (fresh : targetFreshFrame state.memory storage)
    (query : external.call "cetta_native_cost_active" []
      (chargeGuardBound state storage kind units).2 (.bool true) queried)
    (observed : external.call "cetta_native_cost_charge_observed" [kind, .word units]
      queried value post) :
    targetValidCallTree chargeGuardProgram heap external
      (.function chargeGuardHeader.name [kind, .word units] state value
        { post with memory := targetDropLocals post.memory storage 0 2 }
        (chargeGuardActiveChildren state storage kind units queried post value)) position := by
  rw [targetValidCallTree]
  constructor
  · exact chargeGuard_active_function_node heap state storage kind units queried post value position fresh
  · simp only [chargeGuardActiveChildren, targetValidChildren, targetValidCallTree]
    exact ⟨⟨⟨chargeGuardActive, rfl⟩, query⟩,
      ⟨⟨⟨chargeGuardObserved, rfl⟩, observed⟩, trivial⟩⟩

/-- An enabled invocation has exactly the observed service's result relation.
It supplies the original by-value arguments and releases its two parameter
cells afterwards. The query post-state is explicit, so recording its call
may advance an invocation cursor. External effects, faults, allocator observations and all
other storage remain in the service's actual post-state. The service itself
is not certified by this wrapper theorem. -/
theorem chargeGuard_active_function_post_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (kind : TargetValue) (units : BitVec 64) (state : TargetState World)
    (queryPost : TargetState World → TargetState World)
    (query : ∀ middle, middle.external = state.external → ∀ raw after,
      calls (.external "cetta_native_cost_active") [] middle raw after ↔
        raw = .bool true ∧ after = queryPost middle)
    (result : TargetRawResult World) :
    TargetFunctionBody interface heap calls chargeGuardFunction [kind, .word units] state result ↔
      ∃ storage value post, targetFreshFrame state.memory storage ∧
        calls (.external "cetta_native_cost_charge_observed") [kind, .word units]
          (queryPost (chargeGuardBound state storage kind units).2) value post ∧
        result = ⟨value, { post with memory := targetDropLocals post.memory storage 0 2 }⟩ := by
  constructor
  · intro ran
    cases ran with
    | @run storage frame bound out raw fresh parameters body returned =>
      have parameterPair : (frame, bound) = chargeGuardBound state storage kind units :=
        (Option.some.inj parameters).symm
      have frameEq : frame = (chargeGuardBound state storage kind units).1 :=
        congrArg Prod.fst parameterPair
      have stateEq : bound = (chargeGuardBound state storage kind units).2 :=
        congrArg Prod.snd parameterPair
      subst frame
      subst bound
      obtain ⟨value, post, called, executed⟩ :=
        (chargeGuard_body_active_exact interface heap calls state storage kind units
          (queryPost (chargeGuardBound state storage kind units).2) (query _ rfl)
          chargeGuardFunction.body out).mp body
      have rawExact : raw = value := TargetFlow.returned.inj
        (returned.symm.trans (congrArg TargetBlockOutcome.flow executed))
      refine ⟨storage, value, post, fresh, called, ?_⟩
      rw [rawExact, executed]
      rfl
  · rintro ⟨storage, value, post, fresh, called, rfl⟩
    let bound := chargeGuardBound state storage kind units
    have executed : TargetFunctionBody interface heap calls chargeGuardFunction
        [kind, .word units] state
        ⟨value, (targetLeaveScope (targetEmptyFrame storage)
          (chargeGuardActiveOutcome bound.1 kind units value post).frame post).2⟩ :=
      .run fresh (by rfl)
      ((chargeGuard_body_active_exact interface heap calls state storage kind units (queryPost bound.2)
        (query _ rfl) chargeGuardFunction.body _).mpr ⟨value, post, called, rfl⟩) rfl
    exact executed

/-- A state-preserving enabled query is the ordinary uninstrumented instance
of the complete query/service sequencing law. -/
theorem chargeGuard_active_function_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (kind : TargetValue) (units : BitVec 64) (state : TargetState World)
    (query : ∀ middle, middle.external = state.external → ∀ raw after,
      calls (.external "cetta_native_cost_active") [] middle raw after ↔
        raw = .bool true ∧ after = middle)
    (result : TargetRawResult World) :
    TargetFunctionBody interface heap calls chargeGuardFunction [kind, .word units] state result ↔
      ∃ storage value post, targetFreshFrame state.memory storage ∧
        calls (.external "cetta_native_cost_charge_observed") [kind, .word units]
          (chargeGuardBound state storage kind units).2 value post ∧
        result = ⟨value, { post with memory := targetDropLocals post.memory storage 0 2 }⟩ :=
  chargeGuard_active_function_post_exact interface heap calls kind units state id query result

/-- Finite caller storage and an actual service response produce an enabled
wrapper invocation. No totality is inferred from the service's signature. -/
theorem chargeGuard_active_function_realization {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (kind : TargetValue) (units : BitVec 64) (state : TargetState World)
    (finite : TargetFiniteStorage state.memory)
    (query : ∀ middle, middle.external = state.external → ∀ raw after,
      calls (.external "cetta_native_cost_active") [] middle raw after ↔
        raw = .bool true ∧ after = middle)
    (responds : ∀ middle, middle.external = state.external →
      ∃ value post, calls (.external "cetta_native_cost_charge_observed")
        [kind, .word units] middle value post) :
    ∃ result, TargetFunctionBody interface heap calls chargeGuardFunction
      [kind, .word units] state result := by
  obtain ⟨storage, fresh⟩ := target_finite_fresh finite
  obtain ⟨value, post, called⟩ := responds (chargeGuardBound state storage kind units).2 rfl
  exact ⟨_, (chargeGuard_active_function_exact interface heap calls kind units state query _).mpr
    ⟨storage, value, post, fresh, called, rfl⟩⟩

/-- An active query does not invent a successful accounting response when
the observed service is unavailable. -/
theorem chargeGuard_missing_active_service_refused {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (kind : TargetValue) (units : BitVec 64) (state : TargetState World)
    (query : ∀ middle, middle.external = state.external → ∀ raw after,
      calls (.external "cetta_native_cost_active") [] middle raw after ↔
        raw = .bool true ∧ after = middle)
    (missing : ∀ middle value post, ¬ calls (.external "cetta_native_cost_charge_observed")
      [kind, .word units] middle value post) (result : TargetRawResult World) :
    ¬ TargetFunctionBody interface heap calls chargeGuardFunction [kind, .word units] state result := by
  intro ran
  obtain ⟨_, _, _, _, called, _⟩ :=
    (chargeGuard_active_function_exact interface heap calls kind units state query result).mp ran
  exact missing _ _ _ called

namespace GuardControls

/-- Reversing the same two call records prevents the first query, even
when the supplied result word and final program state are unchanged. -/
theorem reordered_query_refused {World : Type} (state : TargetState World) (storage : Nat)
    (kind : TargetValue) (units : BitVec 64) (queried post : TargetState World)
    (value : TargetValue) (position : Nat) (after : TargetState (World × Nat)) :
    ¬ targetLedgerCall (chargeGuardActiveChildren state storage kind units queried post value).reverse
      (position + 1) (.external "cetta_native_cost_active") []
      (targetWithCursor (chargeGuardBound state storage kind units).2 (position + 1))
      (.bool true) after := by
  intro called
  change targetLedgerCall
    [.primitive "cetta_native_cost_charge_observed" [kind, .word units] queried value post,
     .primitive "cetta_native_cost_active" [] (chargeGuardBound state storage kind units).2
       (.bool true) queried] (position + 1) (.external "cetta_native_cost_active") []
    (targetWithCursor (chargeGuardBound state storage kind units).2 (position + 1))
    (.bool true) after at called
  rcases (target_ledger_call_cons_iff _ _ _ _ _ _ _ _).mp called with first | later
  · have mismatch := first.2.1
    simp [TargetCallTree.target] at mismatch
  · rcases (target_ledger_call_cons_iff _ _ _ _ _ _ _ _).mp later with second | absent
    · have cursor := second.1
      change position + 1 + 1 = position + 1 at cursor
      omega
    · exact empty_target_ledger_refuses_call _ _ _ _ _ _ absent

/-- Dropping the query record cannot be repaired by retaining the charge's
record alone. The query is an occurrence, not an inferred service result. -/
theorem omitted_query_refused {World : Type} (queried post : TargetState World)
    (kind : TargetValue) (units : BitVec 64) (value : TargetValue) (position : Nat)
    (before after : TargetState (World × Nat)) :
    ¬ targetLedgerCall [.primitive "cetta_native_cost_charge_observed"
        [kind, .word units] queried value post] position
      (.external "cetta_native_cost_active") [] before (.bool true) after := by
  intro called
  rcases (target_ledger_call_cons_iff _ _ _ _ _ _ _ _).mp called with first | absent
  · have mismatch := first.2.1
    simp [TargetCallTree.target] at mismatch
  · exact empty_target_ledger_refuses_call _ _ _ _ _ _ absent

/-- A concrete service pair makes invocation effects observable independently
of its zero return value. This is a control for wrapper execution, not a model
of the full native ledger implementation. -/
def countingServices (kind : TargetValue) (units : BitVec 64) : TargetCalls Nat :=
  fun target arguments before raw after =>
    (target = .external "cetta_native_cost_active" ∧ arguments = [] ∧
      raw = .bool true ∧ after = before) ∨
    (target = .external "cetta_native_cost_charge_observed" ∧
      arguments = [kind, .word units] ∧ raw = .word 0 ∧
      after = { before with external := before.external + 1 })

/-- The same concrete service control supplies primitive leaves to the
independent ordered-call validator. -/
def countingExternal (kind : TargetValue) (units : BitVec 64) : TargetExternalSemantics Nat :=
  ⟨fun name arguments before raw after =>
    countingServices kind units (.external name) arguments before raw after⟩

/-- Finite caller storage realizes the complete enabled program call with
two checked primitive children. Its zero result retains one service effect. -/
theorem active_program_service_realized (heap : TargetHeapSemantics Nat)
    (kind : TargetValue) (units : BitVec 64) (state : TargetState Nat)
    (finite : TargetFiniteStorage state.memory) :
    ∃ post, targetProgramCall chargeGuardProgram heap (countingExternal kind units)
      (.function chargeGuardHeader.name) [kind, .word units] state (.word 0) post ∧
      post.external = state.external + 1 := by
  obtain ⟨storage, fresh⟩ := target_finite_fresh finite
  let bound := (chargeGuardBound state storage kind units).2
  let observed := { bound with external := bound.external + 1 }
  let post := { observed with memory := targetDropLocals observed.memory storage 0 2 }
  refine ⟨post, ?_, rfl⟩
  refine ⟨.function chargeGuardHeader.name [kind, .word units] state (.word 0) post
      (chargeGuardActiveChildren state storage kind units bound observed (.word 0)),
    rfl, rfl, rfl, rfl, rfl, ?_⟩
  apply chargeGuard_active_call_tree_valid heap (countingExternal kind units)
    state storage kind units bound observed (.word 0) 0 fresh
  · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

private theorem counting_query (kind : TargetValue) (units : BitVec 64)
    (before : TargetState Nat) (raw : TargetValue) (after : TargetState Nat) :
    countingServices kind units (.external "cetta_native_cost_active") [] before raw after ↔
      raw = .bool true ∧ after = before := by
  simp [countingServices]

/-- Every execution of the admitted wrapper preserves this service's return
word and exactly one externally visible increment. -/
theorem active_keeps_service_effect (interface : Interface) (heap : TargetHeapSemantics Nat)
    (kind : TargetValue) (units : BitVec 64) (state : TargetState Nat)
    (result : TargetRawResult Nat)
    (ran : TargetFunctionBody interface heap (countingServices kind units)
      chargeGuardFunction [kind, .word units] state result) :
    result.value = .word 0 ∧ result.state.external = state.external + 1 := by
  obtain ⟨storage, value, post, _, called, same⟩ :=
    (chargeGuard_active_function_exact interface heap (countingServices kind units)
      kind units state (fun _ _ => counting_query kind units _) result).mp ran
  have effect : value = .word 0 ∧
      post = { (chargeGuardBound state storage kind units).2 with
        external := state.external + 1 } := by
    simpa [countingServices, chargeGuardBound, targetDeclareLocal] using called
  rcases effect with ⟨rfl, rfl⟩
  subst result
  exact ⟨rfl, rfl⟩

/-- The control is inhabited for every finite caller store. Its two temporary
parameter cells are released, while the independent service effect survives. -/
theorem active_service_realized (interface : Interface) (heap : TargetHeapSemantics Nat)
    (kind : TargetValue) (units : BitVec 64) (state : TargetState Nat)
    (finite : TargetFiniteStorage state.memory) :
    ∃ result, TargetFunctionBody interface heap (countingServices kind units)
      chargeGuardFunction [kind, .word units] state result ∧
      result.value = .word 0 ∧ result.state.external = state.external + 1 := by
  obtain ⟨result, ran⟩ := chargeGuard_active_function_realization interface heap
    (countingServices kind units) kind units state finite
    (fun _ _ => counting_query kind units _) (by
      intro middle _
      exact ⟨.word 0, { middle with external := middle.external + 1 },
        Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩)
  exact ⟨result, ran, active_keeps_service_effect interface heap kind units state result ran⟩

/-- Keeping only the returned word and resetting the post-state would erase
an actual accounting invocation. The admitted wrapper rejects that result. -/
theorem discarded_service_effect_rejected (interface : Interface)
    (heap : TargetHeapSemantics Nat) (kind : TargetValue) (units : BitVec 64)
    (state : TargetState Nat) :
    ¬ TargetFunctionBody interface heap (countingServices kind units)
      chargeGuardFunction [kind, .word units] state ⟨.word 0, state⟩ := by
  intro ran
  have impossible := (active_keeps_service_effect interface heap kind units state _ ran).2
  exact Nat.ne_of_lt (Nat.lt_succ_self state.external) impossible

end GuardControls

/-- A false query can still change its world. This execution of the actual
wrapper distinguishes a disabled branch from a state-preserving query. -/
theorem chargeGuard_false_query_can_change_world (interface : Interface)
    (heap : TargetHeapSemantics Bool) (state : TargetState Bool)
    (inactive : state.external = false) (storage : Nat) (kind : TargetValue) (units : BitVec 64) :
    let calls : TargetCalls Bool := fun target arguments before raw after =>
      target = .external "cetta_native_cost_active" ∧ arguments = [] ∧
        raw = .bool false ∧ after = { before with external := true }
    let bound := chargeGuardBound state storage kind units
    ∃ out, TargetRun interface heap calls .word chargeGuardFunction.body chargeGuardFunction.body
      bound.1 bound.2 out ∧ out.flow = .returned (.word 0) ∧ out.state.external ≠ state.external := by
  let bound := chargeGuardBound state storage kind units
  let post := { bound.2 with external := true }
  refine ⟨chargeGuardOutcome bound.1 kind units post, ?_, rfl, ?_⟩
  · apply (chargeGuard_body_inactive_exact interface heap _ state storage kind units post
      ?_ chargeGuardFunction.body _).mpr rfl
    intro raw after
    simp only [true_and]
    rfl
  · simp only [chargeGuardOutcome, post, inactive]
    decide


/-! ## Issued-return registry source

The complete deployed search body retains its guard, ordinal table position,
charge call, const pointer alias, selected return and exhausted return. Text
recognition is separate from operational lowering: the scalar profile does
not yet admit this loop or certify its physical pointer-to-array view.
-/

namespace IssuedReturnSource

private def text0 : List Char := "static size_t continuation_lease_index(const CettaContinuationStore *store,\n".toList
private def tokens0 : List NativeC.Token := [.identifier "static".toList, .identifier "size_t".toList, .identifier "continuation_lease_index".toList, .punctuation "(".toList, .identifier "const".toList, .identifier "CettaContinuationStore".toList, .punctuation "*".toList, .identifier "store".toList, .punctuation ",".toList]
private theorem scanned0 : text0.foldl NativeC.step NativeC.initial =
    NativeC.completed tokens0 := by decide +kernel

private def text1 : List Char := "                                      const CettaOwnedContinuation *owned) {\n".toList
private def tokens1 : List NativeC.Token := [.identifier "const".toList, .identifier "CettaOwnedContinuation".toList, .punctuation "*".toList, .identifier "owned".toList, .punctuation ")".toList, .punctuation "{".toList]
private theorem scanned1 : text1.foldl NativeC.step NativeC.initial =
    NativeC.completed tokens1 := by decide +kernel

private def text2 : List Char := "    if (!store || !owned || !owned->resume_store ||\n".toList
private def tokens2 : List NativeC.Token := [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "store".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "owned".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "owned".toList, .punctuation "->".toList, .identifier "resume_store".toList, .punctuation "||".toList]
private theorem scanned2 : text2.foldl NativeC.step NativeC.initial =
    NativeC.completed tokens2 := by decide +kernel

private def text3 : List Char := "        owned->resume_store != store->identity || !owned->resume_lease)\n".toList
private def tokens3 : List NativeC.Token := [.identifier "owned".toList, .punctuation "->".toList, .identifier "resume_store".toList, .punctuation "!=".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "identity".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "owned".toList, .punctuation "->".toList, .identifier "resume_lease".toList, .punctuation ")".toList]
private theorem scanned3 : text3.foldl NativeC.step NativeC.initial =
    NativeC.completed tokens3 := by decide +kernel

private def text4 : List Char := "        return SIZE_MAX;\n".toList
private def tokens4 : List NativeC.Token := [.identifier "return".toList, .identifier "SIZE_MAX".toList, .punctuation ";".toList]
private theorem scanned4 : text4.foldl NativeC.step NativeC.initial =
    NativeC.completed tokens4 := by decide +kernel

private def text5 : List Char := "    for (size_t i = 0u; i < store->lease_length; i++) {\n".toList
private def tokens5 : List NativeC.Token := [.identifier "for".toList, .punctuation "(".toList, .identifier "size_t".toList, .identifier "i".toList, .punctuation "=".toList, .number "0u".toList, .punctuation ";".toList, .identifier "i".toList, .punctuation "<".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "lease_length".toList, .punctuation ";".toList, .identifier "i".toList, .punctuation "++".toList, .punctuation ")".toList, .punctuation "{".toList]
private theorem scanned5 : text5.foldl NativeC.step NativeC.initial =
    NativeC.completed tokens5 := by decide +kernel

private def text6 : List Char := "        cetta_native_cost_charge(CETTA_COST_QUEUE_VISIT,1u);\n".toList
private def tokens6 : List NativeC.Token := [.identifier "cetta_native_cost_charge".toList, .punctuation "(".toList, .identifier "CETTA_COST_QUEUE_VISIT".toList, .punctuation ",".toList, .number "1u".toList, .punctuation ")".toList, .punctuation ";".toList]
private theorem scanned6 : text6.foldl NativeC.step NativeC.initial =
    NativeC.completed tokens6 := by decide +kernel

private def text7 : List Char := "        const CettaContinuationLease *lease = &store->leases[i];\n".toList
private def tokens7 : List NativeC.Token := [.identifier "const".toList, .identifier "CettaContinuationLease".toList, .punctuation "*".toList, .identifier "lease".toList, .punctuation "=".toList, .punctuation "&".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "leases".toList, .punctuation "[".toList, .identifier "i".toList, .punctuation "]".toList, .punctuation ";".toList]
private theorem scanned7 : text7.foldl NativeC.step NativeC.initial =
    NativeC.completed tokens7 := by decide +kernel

private def text8 : List Char := "        if (lease->occurrence == owned->occurrence_id && lease->lease == owned->resume_lease &&\n".toList
private def tokens8 : List NativeC.Token := [.identifier "if".toList, .punctuation "(".toList, .identifier "lease".toList, .punctuation "->".toList, .identifier "occurrence".toList, .punctuation "==".toList, .identifier "owned".toList, .punctuation "->".toList, .identifier "occurrence_id".toList, .punctuation "&&".toList, .identifier "lease".toList, .punctuation "->".toList, .identifier "lease".toList, .punctuation "==".toList, .identifier "owned".toList, .punctuation "->".toList, .identifier "resume_lease".toList, .punctuation "&&".toList]
private theorem scanned8 : text8.foldl NativeC.step NativeC.initial =
    NativeC.completed tokens8 := by decide +kernel

private def text9 : List Char := "            lease->payload == owned->payload && lease->provider == owned->provider)\n".toList
private def tokens9 : List NativeC.Token := [.identifier "lease".toList, .punctuation "->".toList, .identifier "payload".toList, .punctuation "==".toList, .identifier "owned".toList, .punctuation "->".toList, .identifier "payload".toList, .punctuation "&&".toList, .identifier "lease".toList, .punctuation "->".toList, .identifier "provider".toList, .punctuation "==".toList, .identifier "owned".toList, .punctuation "->".toList, .identifier "provider".toList, .punctuation ")".toList]
private theorem scanned9 : text9.foldl NativeC.step NativeC.initial =
    NativeC.completed tokens9 := by decide +kernel

private def text10 : List Char := "            return i;\n".toList
private def tokens10 : List NativeC.Token := [.identifier "return".toList, .identifier "i".toList, .punctuation ";".toList]
private theorem scanned10 : text10.foldl NativeC.step NativeC.initial =
    NativeC.completed tokens10 := by decide +kernel

private def text11 : List Char := "    }\n".toList
private def tokens11 : List NativeC.Token := [.punctuation "}".toList]
private theorem scanned11 : text11.foldl NativeC.step NativeC.initial =
    NativeC.completed tokens11 := by decide +kernel

private def text12 : List Char := "    return SIZE_MAX;\n".toList
private def tokens12 : List NativeC.Token := [.identifier "return".toList, .identifier "SIZE_MAX".toList, .punctuation ";".toList]
private theorem scanned12 : text12.foldl NativeC.step NativeC.initial =
    NativeC.completed tokens12 := by decide +kernel

private def text13 : List Char := "}".toList
private def tokens13 : List NativeC.Token := [.punctuation "}".toList]
private theorem scanned13 : text13.foldl NativeC.step NativeC.initial =
    NativeC.completed tokens13 := by decide +kernel

private def pieces : List (List Char × List NativeC.Token) :=
  [(text0, tokens0), (text1, tokens1), (text2, tokens2), (text3, tokens3), (text4, tokens4), (text5, tokens5), (text6, tokens6), (text7, tokens7), (text8, tokens8), (text9, tokens9), (text10, tokens10), (text11, tokens11), (text12, tokens12), (text13, tokens13)]

def source : List Char := pieces.flatMap Prod.fst
private def tokens : List NativeC.Token := pieces.flatMap Prod.snd

private theorem scanned : List.Forall (fun piece =>
    piece.1.foldl NativeC.step NativeC.initial = NativeC.completed piece.2) pieces :=
  ⟨scanned0, ⟨scanned1, ⟨scanned2, ⟨scanned3, ⟨scanned4, ⟨scanned5, ⟨scanned6, ⟨scanned7, ⟨scanned8, ⟨scanned9, ⟨scanned10, ⟨scanned11, ⟨scanned12, scanned13⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

private theorem lexed : NativeC.lex source = .ok tokens :=
  NativeC.lex_of_completed source tokens (NativeC.completed_pieces pieces scanned)

def types : NativeC.TypeNames :=
  ["size_t".toList, "CettaContinuationStore".toList,
   "CettaOwnedContinuation".toList, "CettaContinuationLease".toList]

private def member (name field : String) : NativeC.CExpr :=
  .field (.identifier name.toList) field.toList true

private def guard : NativeC.CExpr :=
  .binary .or
    (.binary .or
      (.binary .or
        (.binary .or (.unary .not (.identifier "store".toList))
          (.unary .not (.identifier "owned".toList)))
        (.unary .not (member "owned" "resume_store")))
      (.binary .ne (member "owned" "resume_store") (member "store" "identity")))
    (.unary .not (member "owned" "resume_lease"))

private def rowMatches : NativeC.CExpr :=
  .binary .and
    (.binary .and
      (.binary .and
        (.binary .eq (member "lease" "occurrence") (member "owned" "occurrence_id"))
        (.binary .eq (member "lease" "lease") (member "owned" "resume_lease")))
      (.binary .eq (member "lease" "payload") (member "owned" "payload")))
    (.binary .eq (member "lease" "provider") (member "owned" "provider"))

def body : List NativeC.CStatement :=
  [.branch guard [.return (some (.identifier "SIZE_MAX".toList))] [],
   .forLoop ⟨"size_t".toList, 0⟩ ['i'] (.unsignedInteger 0)
     (.binary .lt (.identifier ['i']) (member "store" "lease_length"))
     (.postIncrement (.identifier ['i']))
     [.effect (.call "cetta_native_cost_charge".toList
       [.identifier "CETTA_COST_QUEUE_VISIT".toList, .unsignedInteger 1]),
      .declarePointeeConst ⟨"CettaContinuationLease".toList, 1⟩ "lease".toList
        (.unary .address (.index (member "store" "leases") (.identifier ['i']))),
      .branch rowMatches [.return (some (.identifier ['i']))] []],
   .return (some (.identifier "SIZE_MAX".toList))]

def parsed : NativeC.CQualifiedFunction :=
  ⟨⟨"size_t".toList, 0⟩, "continuation_lease_index".toList,
   [⟨⟨⟨"CettaContinuationStore".toList, 1⟩, "store".toList⟩, true⟩,
    ⟨⟨⟨"CettaOwnedContinuation".toList, 1⟩, "owned".toList⟩, true⟩], body⟩

private theorem token_count : tokens.length = 123 := by decide +kernel

private theorem parsed_exact : NativeC.qualifiedFunction?
    (2 * tokens.length + 4) types (NativeC.ordinaryFunctionTokens tokens) =
      some (parsed, []) := by
  rw [token_count]
  rfl

/-- Complete source consumption keeps both qualified parameters and all
branches of the actual scan; it is not a compiled-C execution theorem. -/
theorem source_recognized : NativeC.qualifiedFunctionText? types source = some parsed :=
  NativeC.function_text_using_of_parts (NativeC.qualifiedParameter? types) types source
    tokens parsed lexed parsed_exact

end IssuedReturnSource

end Mettapedia.Languages.MeTTa.CeTTaNativeCost
