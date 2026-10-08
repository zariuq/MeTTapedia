import Mettapedia.Algorithms.WellFoundedServices.DependencyAnalysis
import Mettapedia.GSLT.LanguageDef.NativeControlCursor
import Mettapedia.GSLT.LanguageDef.NativeOpsCDeclarator
import Mettapedia.GSLT.LanguageDef.NativeOpsCBodyTextAgreement
import Mettapedia.GSLT.LanguageDef.NativeOpsCPostIndex
import Mettapedia.Machines.Cursor.OwnedLifecycle
import Mettapedia.Machines.Cursor.RelationalAmortized
import Mettapedia.Machines.NativeCostLedger
import Mettapedia.Machines.LinkedScopeStack
import Mettapedia.GSLT.LanguageDef.NativeOpsCNormalization
import Mettapedia.GSLT.LanguageDef.NativeOpsCFunctionComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsScalarLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsInstructionComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsFiniteStorage
import Mettapedia.GSLT.LanguageDef.NativeOpsTargetParameterFacts
import Mettapedia.GSLT.LanguageDef.NativeOpsReferenceFieldLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsCLexSegments
import Mettapedia.GSLT.LanguageDef.NativeOpsCLocalBlock
import Mettapedia.GSLT.Core.RouteTrace
import Mettapedia.Machines.CMemory.ReadExpressions
import Mettapedia.Machines.CMemory.EffectStatements

/-!
# CeTTa cost-counter, receipt, completion and readiness source

The body is consumed by the common C lexer and complete statement parser.
The ordinary-parameter reader lowers it to the shared operational IR; its
execution is compared with the independent natural-number cost specification.

The boundary is explicit: unsigned 64-bit arithmetic, immutable by-value
parameters, the admitted `UINT64_MAX` value, and a defined live Boolean
pointer destination. This is not a theorem about an ISO C compiler, the
physical allocator, concurrent pointer access or the whole cost ledger.
Source identity and the rest of the ledger remain separate obligations.
The Task runner additionally retains its whole source body, independently
authored operation tree and complete scoped flow. By-value record copies,
assertion macro profiles and both cleanup guards use the common memory
services; their physical providers and argument-order agreement remain
separate realization obligations. The complete task tree also instantiates
the common polynomial resumption through the primitive-tree isomorphism. Its
direct stateful interpretation preserves fault avoidance and whole-state runs.
The receipt wrapper additionally uses two explicitly declared services.
Its inactive path retains the whole query post-state and releases its
invocation cells. Caller noninterference requires a state-preserving query;
no contract for the unexecuted observed service is used.
-/

set_option autoImplicit false
set_option Elab.async false

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


/-! ## Scoped accounting service instance

The actual admitted inline wrapper is executed with the shared bounded
scope specification as its external accounting service. Its ordered call
tree retains the service's complete post-state and releases invocation cells.
The scope walk, identity atomic, allocator, C memory representation and
compiled implementation of that service remain separate correspondence
obligations; this instance does not promote them to verified primitives.
-/

namespace ScopedServices

open Mettapedia.Machines.NativeCostLedger

abbrev World := Recording.ScopeState 64

/-- The native-events-v1 enumeration, in the deployed C declaration order.
This profile binding is separate from the carrier's abstract cost algebra. -/
def kindWord : Kind → BitVec 64
  | .quantum => 0 | .candidateRow => 1 | .indexVisit => 2 | .matchAttempt => 3
  | .matchNode => 4 | .heapLookup => 5 | .heapIndexVisit => 6 | .heapUpdate => 7
  | .receiptAppend => 8 | .bindingClone => 9 | .queueInsert => 10 | .queueTake => 11
  | .queueVisit => 12 | .queueMove => 13 | .capture => 14 | .restore => 15
  | .frameAllocate => 16 | .frameRetire => 17 | .publish => 18
  | .coefficientAppend => 19 | .coefficientMultiply => 20 | .costRead => 21
  | .analysisStep => 22 | .workerDispatch => 23 | .workerJoin => 24
  | .commitCheck => 25 | .equationActivation => 26 | .storageProbe => 27
  | .coefficientHandle => 28

theorem kindWord_valid (kind : Kind) : (kindWord kind).toNat < 29 := by
  cases kind <;> decide

theorem kindWord_injective : Function.Injective kindWord := by
  decide

def chargeResult (kind : Kind) (units : BitVec 64) (state : TargetState World) :
    TargetValue × TargetState World :=
  let result := Recording.observeScopes (2 ^ 64 - 1) (2 ^ 64 - 1) state.external kind units
  (.word (BitVec.ofNat 64 result.1), { state with external := result.2 })

/-- The query observes the captured active chain without changing it. The
accounting leaf invokes the independently specified shared scope machine;
it does not discard its counters, retained histories or identity frontier. -/
def calls (kind : Kind) (units : BitVec 64) : TargetCalls World :=
  fun target arguments before raw after =>
    (target = .external "cetta_native_cost_active" ∧ arguments = [] ∧
      raw = .bool (decide (before.external.scopes ≠ [])) ∧ after = before) ∨
    (target = .external "cetta_native_cost_charge_observed" ∧
      arguments = [.word (kindWord kind), .word units] ∧
      (raw, after) = chargeResult kind units before)

def external (kind : Kind) (units : BitVec 64) : TargetExternalSemantics World :=
  ⟨fun name arguments before raw after => calls kind units (.external name) arguments before raw after⟩

private theorem query (kind : Kind) (units : BitVec 64)
    (before : TargetState World) (raw : TargetValue) (after : TargetState World) :
    calls kind units (.external "cetta_native_cost_active") [] before raw after ↔
      raw = .bool (decide (before.external.scopes ≠ [])) ∧ after = before := by
  simp [calls]

/-- A disabled captured scope instantiates the admitted source wrapper
without an observed-service call or identity issuance. Every caller field
is preserved after the two temporary argument cells are released. -/
theorem inactive_source_realized (heap : TargetHeapSemantics World)
    (kind : Kind) (units : BitVec 64) (state : TargetState World)
    (finite : TargetFiniteStorage state.memory) (inactive : state.external.scopes = []) :
    TargetFunctionBody chargeGuardProgram.interface heap (calls kind units) chargeGuardFunction
      [.word (kindWord kind), .word units] state ⟨.word 0, state⟩ := by
  apply chargeGuard_inactive_function_realization _ _ _ _ _ _ finite
  intro middle same raw after
  rw [query, same]
  simp only [inactive, ne_eq, not_true_eq_false, decide_false]

/-- The disabled source instance has one actual query leaf. The missing
accounting leaf is not simulated by emitting and later erasing an event. -/
theorem inactive_program_realized (heap : TargetHeapSemantics World)
    (kind : Kind) (units : BitVec 64) (state : TargetState World)
    (finite : TargetFiniteStorage state.memory) (inactive : state.external.scopes = []) :
    targetProgramCall chargeGuardProgram heap (external kind units)
      (.function chargeGuardHeader.name) [.word (kindWord kind), .word units] state (.word 0) state := by
  obtain ⟨storage, fresh⟩ := target_finite_fresh finite
  let encoded : TargetValue := .word (kindWord kind)
  let bound := (chargeGuardBound state storage encoded units).2
  have teardown : { bound with memory := targetDropLocals bound.memory storage 0 2 } = state :=
    chargeGuard_teardown state storage encoded units fresh
  suffices realized : targetProgramCall chargeGuardProgram heap (external kind units)
      (.function chargeGuardHeader.name) [encoded, .word units] state (.word 0)
      { bound with memory := targetDropLocals bound.memory storage 0 2 } by
    simpa only [teardown] using realized
  refine ⟨.function chargeGuardHeader.name [encoded, .word units] state (.word 0)
      { bound with memory := targetDropLocals bound.memory storage 0 2 }
      (chargeGuardInactiveChildren state storage encoded units bound),
    rfl, rfl, rfl, rfl, rfl, ?_⟩
  apply chargeGuard_inactive_call_tree_valid heap (external kind units)
    state storage encoded units bound 0 fresh
  exact Or.inl ⟨rfl, rfl, by simp [chargeGuardBound, targetDeclareLocal, inactive], rfl⟩

/-- The enabled call has two actual checked primitive leaves. The native
scope specification supplies the physical-event word and whole retained
post-context; both are kept by the parsed and lowered wrapper. -/
theorem active_program_realized (heap : TargetHeapSemantics World)
    (kind : Kind) (units : BitVec 64) (state : TargetState World)
    (finite : TargetFiniteStorage state.memory) (active : state.external.scopes ≠ []) :
    let result := Recording.observeScopes (2 ^ 64 - 1) (2 ^ 64 - 1) state.external kind units
    ∃ post, targetProgramCall chargeGuardProgram heap (external kind units)
      (.function chargeGuardHeader.name) [.word (kindWord kind), .word units] state
      (.word (BitVec.ofNat 64 result.1)) post ∧
      post = { state with external := result.2 } := by
  obtain ⟨storage, fresh⟩ := target_finite_fresh finite
  let encoded : TargetValue := .word (kindWord kind)
  let bound := (chargeGuardBound state storage encoded units).2
  let result := Recording.observeScopes (2 ^ 64 - 1) (2 ^ 64 - 1) state.external kind units
  let value : TargetValue := .word (BitVec.ofNat 64 result.1)
  let observed := { bound with external := result.2 }
  let post := { observed with memory := targetDropLocals observed.memory storage 0 2 }
  have teardown : post = { state with external := result.2 } :=
    congrArg (fun packet : TargetState World => { packet with external := result.2 })
      (chargeGuard_teardown state storage encoded units fresh)
  refine ⟨post, ?_, teardown⟩
  refine ⟨.function chargeGuardHeader.name [encoded, .word units] state value post
      (chargeGuardActiveChildren state storage encoded units bound observed value),
    rfl, rfl, rfl, rfl, rfl, ?_⟩
  apply chargeGuard_active_call_tree_valid heap (external kind units)
    state storage encoded units bound observed value 0 fresh
  · exact Or.inl ⟨rfl, rfl, by simp [chargeGuardBound, targetDeclareLocal, active], rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl⟩

/-- The source invocation's joined instance obeys the independent
mathematical saturation law at every containing destination. Its primitive
scope/retention services still require separate source realization. -/
theorem active_program_work (heap : TargetHeapSemantics World)
    (kind : Kind) (units : BitVec 64) (state : TargetState World)
    (finite : TargetFiniteStorage state.memory) (active : state.external.scopes ≠ [])
    (nonzero : units ≠ 0) (location : Nat) :
    ∃ post, targetProgramCall chargeGuardProgram heap (external kind units)
      (.function chargeGuardHeader.name) [.word (kindWord kind), .word units] state
      (.word (BitVec.ofNat 64
        (Recording.observeScopes (2 ^ 64 - 1) (2 ^ 64 - 1) state.external kind units).1)) post ∧
      (post.external.store location).work.toNat =
        boundedTotal (2 ^ 64 - 1) ((state.external.store location).work.toNat +
          if some location ∈ state.external.scopes.map Prod.fst then units.toNat else 0) := by
  obtain ⟨post, ran, same⟩ := active_program_realized heap kind units state finite active
  refine ⟨post, ran, ?_⟩
  rw [same]
  exact Recording.observeScopes_work _ _ _ _ _ active nonzero location

/-- Every enabled execution retains the shared service's entire context,
not merely one realizable invocation. Returning only the event word cannot
license resetting the identity frontier, counters or retained histories. -/
theorem active_source_keeps_context (interface : Interface) (heap : TargetHeapSemantics World)
    (kind : Kind) (units : BitVec 64) (state : TargetState World)
    (active : state.external.scopes ≠ []) (result : TargetRawResult World)
    (ran : TargetFunctionBody interface heap (calls kind units) chargeGuardFunction
      [.word (kindWord kind), .word units] state result) :
    let charged := Recording.observeScopes (2 ^ 64 - 1) (2 ^ 64 - 1) state.external kind units
    result.value = .word (BitVec.ofNat 64 charged.1) ∧ result.state.external = charged.2 := by
  obtain ⟨storage, value, post, _, called, same⟩ :=
    (chargeGuard_active_function_exact interface heap (calls kind units)
      (.word (kindWord kind)) units state (by
        intro middle equivalent raw after
        have actual := query kind units middle raw after
        have middleActive : middle.external.scopes ≠ [] := by rw [equivalent]; exact active
        have enabled : decide (middle.external.scopes ≠ []) = true := decide_eq_true middleActive
        simpa only [enabled] using actual) result).mp ran
  let charged := Recording.observeScopes (2 ^ 64 - 1) (2 ^ 64 - 1) state.external kind units
  have effect : value = .word (BitVec.ofNat 64 charged.1) ∧
      post = { (chargeGuardBound state storage (.word (kindWord kind)) units).2 with
        external := charged.2 } := by
    simpa [calls, chargeResult, charged, chargeGuardBound, targetDeclareLocal] using called
  rcases effect with ⟨rfl, rfl⟩
  subst result
  exact ⟨rfl, rfl⟩

end ScopedServices

namespace CapturedRun

open Mettapedia.Machines.LinkedScopeStack

/-- Carrier values are kept whole. Their physical representation, borrowed
addresses and source currency need separate native service comparisons. -/
structure Views (Need Branch Weights Receipt : Type) where
  need : Need
  branch : Branch
  weights : Weights
  receipt : Receipt
  logical : Option Nat
  deriving DecidableEq

structure Context (Need Branch Weights Receipt : Type) where
  views : Views Need Branch Weights Receipt
  driver : Option Nat
  first : Option Nat
  needOwner : Option Nat
  episodeOwner : Option Nat
  branchOwner : Option Nat
  regionPool : Option Nat

inductive Channel where
  | registry | cost
  deriving DecidableEq

structure Config (Need Branch Weights Receipt : Type) where
  capture : Option (Views Need Branch Weights Receipt)
  driver : Nat
  storage : Option Nat
  registryFrame : Nat
  registrySource : Option Nat
  costFrame : Option (Nat × Nat)

/-- Intrusive metadata remains written when a frame becomes inactive.
The payload retains the complete supplied service/control state. -/
structure Store (Payload : Type) where
  registrySources : Nat → Option Nat
  costFrames : Nat → Option (Nat × Nat)
  payload : Payload

variable {Need Branch Weights Receipt Payload : Type}

abbrev State := Activation.State Channel (fun _ => Nat)
  (Context Need Branch Weights Receipt) (Store Payload)
abbrev Reference := Activation.Reference Channel (fun _ => Nat)
  (Context Need Branch Weights Receipt) (Store Payload)

local notation "RunState" => State (Need := Need) (Branch := Branch)
  (Weights := Weights) (Receipt := Receipt) (Payload := Payload)
local notation "RunReference" => Reference (Need := Need) (Branch := Branch)
  (Weights := Weights) (Receipt := Receipt) (Payload := Payload)

/-- Modeled field contract of the native run guard. An initialized capture
replaces every view, including empty values; an uninitialized computation
inherits the ambient views. Owned storage replaces both allocation owners
and clears the borrowed branch owner and pool. -/
def install (config : Config Need Branch Weights Receipt)
    (caller : Context Need Branch Weights Receipt) : Context Need Branch Weights Receipt :=
  { views := config.capture.getD caller.views
    driver := some config.driver
    first := none
    needOwner := config.storage.or caller.needOwner
    episodeOwner := config.storage.or caller.episodeOwner
    branchOwner := if config.storage.isSome then none else caller.branchOwner
    regionPool := if config.storage.isSome then none else caller.regionPool }

def selected (config : Config Need Branch Weights Receipt) : Channel → Option Nat
  | .registry => some config.registryFrame
  | .cost => config.costFrame.map Prod.fst

def prepareStore (config : Config Need Branch Weights Receipt) (store : Store Payload) :
    Store Payload :=
  { store with
    registrySources := fun frame => if frame = config.registryFrame then
      config.registrySource else store.registrySources frame
    costFrames := fun frame => match config.costFrame with
      | none => store.costFrames frame
      | some (active, ledger) => if frame = active then some (ledger, 0)
          else store.costFrames frame }

def prepare (config : Config Need Branch Weights Receipt)
    (caller : RunState) : RunState :=
  { caller with store := prepareStore config caller.store }

def prepareReference (config : Config Need Branch Weights Receipt)
    (caller : RunReference) : RunReference :=
  { caller with store := prepareStore config caller.store }

theorem prepare_related (config : Config Need Branch Weights Receipt)
    {caller : RunState} {reference : RunReference}
    (related : Activation.Related caller reference) :
    Activation.Related (prepare config caller) (prepareReference config reference) :=
  ⟨related.context, related.scopes, related.externalDepth,
    congrArg (prepareStore config) related.store⟩

theorem captured_views_exact (config : Config Need Branch Weights Receipt)
    (caller : Context Need Branch Weights Receipt) (capture : Views Need Branch Weights Receipt)
    (initialized : config.capture = some capture) :
    (install config caller).views = capture := by simp [install, initialized]

theorem uninitialized_views_inherit (config : Config Need Branch Weights Receipt)
    (caller : Context Need Branch Weights Receipt) (uninitialized : config.capture = none) :
    (install config caller).views = caller.views := by simp [install, uninitialized]

theorem owned_owner_routing (config : Config Need Branch Weights Receipt)
    (caller : Context Need Branch Weights Receipt) (owner : Nat)
    (owned : config.storage = some owner) :
    (install config caller).needOwner = some owner ∧
      (install config caller).episodeOwner = some owner ∧
      (install config caller).branchOwner = none ∧
      (install config caller).regionPool = none := by simp [install, owned]

theorem borrowed_owner_routing (config : Config Need Branch Weights Receipt)
    (caller : Context Need Branch Weights Receipt) (borrowed : config.storage = none) :
    (install config caller).needOwner = caller.needOwner ∧
      (install config caller).episodeOwner = caller.episodeOwner ∧
      (install config caller).branchOwner = caller.branchOwner ∧
      (install config caller).regionPool = caller.regionPool := by simp [install, borrowed]

/-- This instantiates the linked-stack/list entry theorem with the native
guard's two independently selected channels and whole captured context. It
does not claim that the C guard source has been formally compiled. -/
theorem enter_model_correspondence (config : Config Need Branch Weights Receipt)
    {caller : RunState} {reference : RunReference}
    (related : Activation.Related caller reference)
    (fresh : ∀ channel identity, selected config channel = some identity →
      identity ∉ reference.active channel) :
    Activation.Related
      (Activation.enter (selected config) (install config caller.context) (prepare config caller))
      (Activation.enterReference (selected config) (install config reference.context)
        (prepareReference config reference)) := by
  rw [related.context]
  exact Activation.enter_related _ _ (prepare_related config related) fresh

def run {Answer : Type} (config : Config Need Branch Weights Receipt)
    (body : RunState → Answer × RunState) (caller : RunState) : Answer × RunState :=
  Activation.run (selected config) (install config caller.context) body (prepare config caller)

def runReference {Answer : Type} (config : Config Need Branch Weights Receipt)
    (body : RunReference → Answer × RunReference)
    (caller : RunReference) : Answer × RunReference :=
  Activation.runReference (selected config) (install config caller.context) body
    (prepareReference config caller)

theorem run_restores_context {Answer : Type} (config : Config Need Branch Weights Receipt)
    (body : RunState → Answer × RunState) (caller : RunState) :
    (run config body caller).2.context = caller.context := rfl

theorem run_keeps_poststore {Answer : Type} (config : Config Need Branch Weights Receipt)
    (body : RunState → Answer × RunState) (caller : RunState) :
    (run config body caller).2.store =
      (body (Activation.enter (selected config) (install config caller.context)
        (prepare config caller))).2.store := rfl

/-- A separately supplied body comparison composes with the modeled field
installation. Balanced selected channels, live links and bounded native depth
remain premises for a native guard interpretation. Service poststates are
retained rather than replaced by the original caller store. -/
theorem run_model_correspondence {Answer : Type} (config : Config Need Branch Weights Receipt)
    (body : RunState → Answer × RunState)
    (referenceBody : RunReference → Answer × RunReference)
    {caller : RunState} {reference : RunReference} (related : Activation.Related caller reference)
    (fresh : ∀ channel identity, selected config channel = some identity →
      identity ∉ reference.active channel)
    (bodyComparison : ∀ state reference, Activation.Related state reference →
      (body state).1 = (referenceBody reference).1 ∧
        Activation.Related (body state).2 (referenceBody reference).2)
    (balanced : ∀ channel identity, selected config channel = some identity →
      (referenceBody (Activation.enterReference (selected config)
        (install config reference.context) (prepareReference config reference))).2.active channel =
          identity :: reference.active channel) :
    (run config body caller).1 = (runReference config referenceBody reference).1 ∧
      Activation.Related (run config body caller).2 (runReference config referenceBody reference).2 := by
  unfold run runReference
  rw [related.context]
  exact Activation.run_correspondence _ _ body referenceBody
    (prepare_related config related) fresh bodyComparison balanced

/-- A concrete family of observer bodies reads every captured carrier and
retains the supplied service update. The reference reads its separate list
state; it is not defined by invoking the implementation body. -/
def observe (update : Views Need Branch Weights Receipt → Payload → Payload)
    (state : RunState) : Views Need Branch Weights Receipt × RunState :=
  (state.context.views,
    { state with store := { state.store with
      payload := update state.context.views state.store.payload } })

def observeReference (update : Views Need Branch Weights Receipt → Payload → Payload)
    (state : RunReference) : Views Need Branch Weights Receipt × RunReference :=
  (state.context.views,
    { state with store := { state.store with
      payload := update state.context.views state.store.payload } })

theorem observe_comparison (update : Views Need Branch Weights Receipt → Payload → Payload)
    {state : RunState} {reference : RunReference} (related : Activation.Related state reference) :
    (observe update state).1 = (observeReference update reference).1 ∧
      Activation.Related (observe update state).2 (observeReference update reference).2 := by
  refine ⟨congrArg Context.views related.context,
    related.context, related.scopes, related.externalDepth, ?_⟩
  change { state.store with payload := update state.context.views state.store.payload } =
    { reference.store with payload := update reference.context.views reference.store.payload }
  rw [related.context, related.store]

/-- All captured views and the complete supplied service update survive the
activation boundary, under the independent linked/list representation. -/
theorem observing_run_correspondence (config : Config Need Branch Weights Receipt)
    (update : Views Need Branch Weights Receipt → Payload → Payload)
    {caller : RunState} {reference : RunReference} (related : Activation.Related caller reference)
    (fresh : ∀ channel identity, selected config channel = some identity →
      identity ∉ reference.active channel) :
    (run config (observe update) caller).1 =
        (runReference config (observeReference update) reference).1 ∧
      Activation.Related (run config (observe update) caller).2
        (runReference config (observeReference update) reference).2 := by
  apply run_model_correspondence config (observe update) (observeReference update)
    related fresh (fun _ _ => observe_comparison update)
  intro channel identity choice
  change (selected config channel).toList ++ reference.active channel =
    identity :: reference.active channel
  simp [choice]

/-- The physical collection barrier uses an unsigned 32-bit word. Its
natural-depth reading is exact only before wrapping; the leave service also
requires a nonzero word. The readiness initializer is a separate service. -/
def enterDepth (depth : BitVec 32) : BitVec 32 := depth + 1
def leaveDepth (depth : BitVec 32) : BitVec 32 := depth - 1

theorem enter_depth_exact (depth : BitVec 32) (within : depth.toNat + 1 < 2 ^ 32) :
    (enterDepth depth).toNat = depth.toNat + 1 := by
  simpa [enterDepth] using (BitVec.toNat_add_of_lt (x := depth) (y := 1) within)

theorem entered_depth_positive (depth : BitVec 32) (within : depth.toNat + 1 < 2 ^ 32) :
    0 < (enterDepth depth).toNat := by rw [enter_depth_exact depth within]; omega

theorem leave_depth_exact (depth : BitVec 32) (active : 0 < depth.toNat) :
    (leaveDepth depth).toNat = depth.toNat - 1 := by
  have ordered : (1 : BitVec 32) ≤ depth := by
    change (1 : BitVec 32).toNat ≤ depth.toNat
    exact Nat.succ_le_of_lt active
  simpa [leaveDepth] using BitVec.toNat_sub_of_le ordered

theorem wrapped_depth_is_outside_natural_activation :
    enterDepth (BitVec.allOnes 32) = 0 ∧
      (enterDepth (BitVec.allOnes 32)).toNat ≠ (BitVec.allOnes 32).toNat + 1 := by decide

namespace Controls

abbrev NeedView := Option (Nat × List Nat)
abbrev TestViews := Views NeedView (List Nat) (List Nat) (List Nat)
abbrev TestContext := Context NeedView (List Nat) (List Nat) (List Nat)
abbrev TestState := State (Need := NeedView) (Branch := List Nat) (Weights := List Nat)
  (Receipt := List Nat) (Payload := List TestViews)

def ambient : TestContext :=
  ⟨⟨some (7, [2, 2]), [4], [3, 3], [11], some 90⟩,
    some 80, some 81, some 82, some 83, some 84, some 85⟩
def absent : TestViews := ⟨none, [], [], [], some 30⟩
def validEmpty : TestViews := ⟨some (9, []), [], [], [], some 31⟩
def initial : TestState :=
  ⟨ambient, fun _ => Mettapedia.Machines.LinkedScopeStack.Controls.empty, 4,
    ⟨fun _ => none, fun _ => none, []⟩⟩
def configured (capture : TestViews) : Config NeedView (List Nat) (List Nat) (List Nat) :=
  ⟨some capture, 40, none, 1, some 50, some (2, 70)⟩
def retain (view : TestViews) (history : List TestViews) : List TestViews := history ++ [view]

theorem absent_and_valid_empty_remain_distinct :
    (run (configured absent) (observe retain) initial).1.need = none ∧
      (run (configured validEmpty) (observe retain) initial).1.need = some (9, []) ∧
      (run (configured absent) (observe retain) initial).2.store.payload = [absent] ∧
      (run (configured validEmpty) (observe retain) initial).2.store.payload = [validEmpty] := by
  decide

theorem borrowed_views_do_not_retain_ambient_weights :
    let result := run (configured validEmpty) (observe retain) initial
    result.1.weights = [] ∧ result.1.logical = some 31 ∧
      result.2.context.views.weights = [3, 3] ∧
      result.2.context.needOwner = some 82 ∧
      result.2.context.branchOwner = some 84 ∧ result.2.externalDepth = 4 := by decide

theorem inactive_metadata_and_service_history_survive :
    let result := run (configured validEmpty) (observe retain) initial
    result.2.store.registrySources 1 = some 50 ∧
      result.2.store.costFrames 2 = some (70, 0) ∧
      (result.2.scopes .registry).parent 1 = none ∧
      result.2.store.payload = [validEmpty] := by decide

/-- Treating an initialized empty capture as missing reintroduces the
caller's weights and session into the resumed computation. -/
theorem omitted_capture_exposes_ambient_world :
    let wrong := { configured validEmpty with capture := none }
    (run wrong (observe retain) initial).1.need = ambient.views.need ∧
      (run wrong (observe retain) initial).1.weights = [3, 3] ∧
      (run wrong (observe retain) initial).1.need ≠
        (run (configured validEmpty) (observe retain) initial).1.need := by decide

end Controls

end CapturedRun


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

/-! The complete release source retains both refusal branches, the
authenticated index call, pre-decremented last-row exchange, clearing of both
lease fields and the retirement charge. Recognition supplies no execution
authority for its pointer aliases or mutation. -/

namespace ReleaseLease

open NativeC

private def text0 : List Char := "bool cetta_continuation_hub_release_lease(CettaContinuationHub *hub,\n".toList
private def tokens0 : List Token := [.identifier "bool".toList, .identifier "cetta_continuation_hub_release_lease".toList, .punctuation "(".toList, .identifier "CettaContinuationHub".toList, .punctuation "*".toList, .identifier "hub".toList, .punctuation ",".toList]
private theorem scanned0 : text0.foldl step initial = completed tokens0 := by decide +kernel

private def text1 : List Char := "        CettaOwnedContinuation *owned) {\n".toList
private def tokens1 : List Token := [.identifier "CettaOwnedContinuation".toList, .punctuation "*".toList, .identifier "owned".toList, .punctuation ")".toList, .punctuation "{".toList]
private theorem scanned1 : text1.foldl step initial = completed tokens1 := by decide +kernel

private def text2 : List Char := "    if (!hub || !hub->initialized) return false;\n".toList
private def tokens2 : List Token := [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "hub".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "hub".toList, .punctuation "->".toList, .identifier "initialized".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "false".toList, .punctuation ";".toList]
private theorem scanned2 : text2.foldl step initial = completed tokens2 := by decide +kernel

private def text3 : List Char := "    CettaContinuationStore *store = &hub->store;\n".toList
private def tokens3 : List Token := [.identifier "CettaContinuationStore".toList, .punctuation "*".toList, .identifier "store".toList, .punctuation "=".toList, .punctuation "&".toList, .identifier "hub".toList, .punctuation "->".toList, .identifier "store".toList, .punctuation ";".toList]
private theorem scanned3 : text3.foldl step initial = completed tokens3 := by decide +kernel

private def text4 : List Char := "    size_t index = continuation_lease_index(store,owned);\n".toList
private def tokens4 : List Token := [.identifier "size_t".toList, .identifier "index".toList, .punctuation "=".toList, .identifier "continuation_lease_index".toList, .punctuation "(".toList, .identifier "store".toList, .punctuation ",".toList, .identifier "owned".toList, .punctuation ")".toList, .punctuation ";".toList]
private theorem scanned4 : text4.foldl step initial = completed tokens4 := by decide +kernel

private def text5 : List Char := "    if (index == SIZE_MAX) return false;\n".toList
private def tokens5 : List Token := [.identifier "if".toList, .punctuation "(".toList, .identifier "index".toList, .punctuation "==".toList, .identifier "SIZE_MAX".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "false".toList, .punctuation ";".toList]
private theorem scanned5 : text5.foldl step initial = completed tokens5 := by decide +kernel

private def text6 : List Char := "    store->leases[index] = store->leases[--store->lease_length];\n".toList
private def tokens6 : List Token := [.identifier "store".toList, .punctuation "->".toList, .identifier "leases".toList, .punctuation "[".toList, .identifier "index".toList, .punctuation "]".toList, .punctuation "=".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "leases".toList, .punctuation "[".toList, .punctuation "--".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "lease_length".toList, .punctuation "]".toList, .punctuation ";".toList]
private theorem scanned6 : text6.foldl step initial = completed tokens6 := by decide +kernel

private def text7 : List Char := "    owned->resume_store = 0u;\n".toList
private def tokens7 : List Token := [.identifier "owned".toList, .punctuation "->".toList, .identifier "resume_store".toList, .punctuation "=".toList, .number "0u".toList, .punctuation ";".toList]
private theorem scanned7 : text7.foldl step initial = completed tokens7 := by decide +kernel

private def text8 : List Char := "    owned->resume_lease = 0u;\n".toList
private def tokens8 : List Token := [.identifier "owned".toList, .punctuation "->".toList, .identifier "resume_lease".toList, .punctuation "=".toList, .number "0u".toList, .punctuation ";".toList]
private theorem scanned8 : text8.foldl step initial = completed tokens8 := by decide +kernel

private def text9 : List Char := "    cetta_native_cost_charge(CETTA_COST_FRAME_RETIRE,1u);\n".toList
private def tokens9 : List Token := [.identifier "cetta_native_cost_charge".toList, .punctuation "(".toList, .identifier "CETTA_COST_FRAME_RETIRE".toList, .punctuation ",".toList, .number "1u".toList, .punctuation ")".toList, .punctuation ";".toList]
private theorem scanned9 : text9.foldl step initial = completed tokens9 := by decide +kernel

private def text10 : List Char := "    return true;\n".toList
private def tokens10 : List Token := [.identifier "return".toList, .identifier "true".toList, .punctuation ";".toList]
private theorem scanned10 : text10.foldl step initial = completed tokens10 := by decide +kernel

private def text11 : List Char := "}".toList
private def tokens11 : List Token := [.punctuation "}".toList]
private theorem scanned11 : text11.foldl step initial = completed tokens11 := by decide +kernel

private def pieces : List (List Char × List Token) := [(text0, tokens0), (text1, tokens1), (text2, tokens2), (text3, tokens3), (text4, tokens4), (text5, tokens5), (text6, tokens6), (text7, tokens7), (text8, tokens8), (text9, tokens9), (text10, tokens10), (text11, tokens11)]
def source : List Char := pieces.flatMap Prod.fst
private def tokens : List Token := pieces.flatMap Prod.snd

private theorem scanned : List.Forall (fun piece =>
    piece.1.foldl step initial = completed piece.2) pieces :=
  ⟨scanned0, ⟨scanned1, ⟨scanned2, ⟨scanned3, ⟨scanned4, ⟨scanned5, ⟨scanned6, ⟨scanned7, ⟨scanned8, ⟨scanned9, ⟨scanned10, scanned11⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

private theorem lexed : lex source = .ok tokens :=
  lex_of_completed source tokens (completed_pieces pieces scanned)

def types : TypeNames :=
  ["bool".toList, "size_t".toList, "CettaContinuationHub".toList,
   "CettaContinuationStore".toList, "CettaOwnedContinuation".toList]

private def registry (index : CExpr) : CExpr :=
  .index (member "store" "leases") index

def body : List CStatement :=
  [.branch (.binary .or (.unary .not (.identifier "hub".toList))
      (.unary .not (member "hub" "initialized"))) [.return (some (.bool false))] [],
   .declare ⟨"CettaContinuationStore".toList, 1⟩ "store".toList
     (.unary .address (member "hub" "store")),
   .declare ⟨"size_t".toList, 0⟩ "index".toList
     (.call "continuation_lease_index".toList
       [.identifier "store".toList, .identifier "owned".toList]),
   .branch (.binary .eq (.identifier "index".toList) (.identifier "SIZE_MAX".toList))
     [.return (some (.bool false))] [],
   .assign (registry (.identifier "index".toList))
     (registry (.unary .decrement (member "store" "lease_length"))),
   .assign (member "owned" "resume_store") (.unsignedInteger 0),
   .assign (member "owned" "resume_lease") (.unsignedInteger 0),
   .effect (.call "cetta_native_cost_charge".toList
     [.identifier "CETTA_COST_FRAME_RETIRE".toList, .unsignedInteger 1]),
   .return (some (.bool true))]

def parsed : CQualifiedFunction :=
  ⟨⟨"bool".toList, 0⟩, "cetta_continuation_hub_release_lease".toList,
   [⟨⟨⟨"CettaContinuationHub".toList, 1⟩, "hub".toList⟩, false⟩,
    ⟨⟨⟨"CettaOwnedContinuation".toList, 1⟩, "owned".toList⟩, false⟩], body⟩

private theorem token_count : tokens.length = 93 := by decide +kernel

private theorem parsed_exact : qualifiedFunction?
    (2 * tokens.length + 4) types (ordinaryFunctionTokens tokens) = some (parsed, []) := by
  rw [token_count]
  rfl

theorem source_recognized : qualifiedFunctionText? types source = some parsed :=
  function_text_using_of_parts (qualifiedParameter? types) types source tokens parsed lexed parsed_exact

namespace Exchange

open NativeC.PostIndex.LastExchange
open Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn
open Mettapedia.Algebra.OccurrenceIdentity

def exchangeSite : ExchangeSyntax :=
  ⟨"store".toList, "leases".toList, "lease_length".toList, "index".toList⟩

theorem body_exchange_exact : body[4]? = some exchangeSite.statement := rfl

theorem body_exchange_recognized :
    body[4]?.bind exchangeSyntax? = some exchangeSite := by
  rw [body_exchange_exact]
  exact recognizes_authored_exchange exchangeSite

variable {Value : Type} {width : Nat}

theorem body_exchange_execution (resolve : ExchangeSyntax →
    Option (List Value × BitVec width × Nat))
    (slots : List Value) (count : BitVec width) (index : Nat)
    (resolved : resolve exchangeSite = some (slots, count, index)) :
    body[4]?.bind (executeExchange resolve) = exchangeLast slots count index := by
  rw [body_exchange_exact]
  exact recognized_exchange_execution resolve exchangeSite slots count index resolved

variable {Address Provider : Type} [DecidableEq Address] [DecidableEq Provider]

/-- The word-counted backing-array edit implements the independently specified
issued return. Retired/spare backing cells are retained. Lookup authorization,
array extent and unsigned-word width are explicit; this does not supply a
physical allocator, alias/layout certificate, or the whole helper semantics. -/
theorem issued_return_of_exchange (registry : Registry Address Provider)
    (handle : Handle Address Provider) (slots : List (Row Address Provider))
    (count : BitVec width) (index : Nat) (positiveWidth : 0 < width)
    (sized : count.toNat ≤ slots.length)
    (represented : registry.rows = slots.take count.toNat)
    (accepted : (lookup registry handle).1 = some index) :
    ∃ next after,
      exchangeLast slots count index = some (next, after) ∧
      releaseIssued registry handle =
        (some ({ registry with rows := after.take next.toNat },
          { handle with store := 0, row.token := 0 }), index + 1) ∧
      next.toNat + 1 = count.toNat ∧ after.length = slots.length ∧
      (handle.row :: after.take next.toNat).Perm registry.rows := by
  obtain ⟨atIndex, visits⟩ := lookup_selected registry handle index accepted
  have liveLength : registry.rows.length = count.toNat := by
    rw [represented]
    exact List.length_take_of_le sized
  have inside : index < count.toNat := by
    by_contra outside
    have absent : registry.rows[index]? = none :=
      List.getElem?_eq_none_iff.mpr (by omega)
    rw [absent] at atIndex
    cases atIndex
  obtain ⟨selected, remaining, next, after, executed, extraction, extent, livePrefix, backing⟩ :=
    exchange_refines_live_prefix slots count index positiveWidth sized inside
  have picked := extractByLast_selected index (slots.take count.toNat)
  rw [extraction] at picked
  simp only [Option.map_some] at picked
  rw [← represented, atIndex] at picked
  have same : selected = handle.row := Option.some.inj picked
  rw [same, ← represented] at extraction
  have released : releaseIssued registry handle =
      (some ({ registry with rows := remaining },
        { handle with store := 0, row.token := 0 }), index + 1) := by
    simp only [releaseIssued, accepted, extraction, visits, bind, Option.bind_some]
  refine ⟨next, after, executed, ?_, extent, backing, ?_⟩
  · rw [livePrefix]
    exact released
  · rw [livePrefix]
    exact extractByLast_permutation index registry.rows handle.row remaining extraction


end Exchange

end ReleaseLease

/-! Complete registration syntax retains capacity refusal, the selected
occurrence scan, inclusive token exhaustion, ordered row construction and the
capture charge. The array publication bridge preserves full handles and spare
cells; allocator calls, pointer layout and whole-helper execution remain
separate obligations. -/

namespace TakeForResume

open NativeC


private def text0 : List Char := "bool cetta_continuation_hub_take_for_resume(CettaContinuationHub *hub, size_t index,\n".toList
private def tokens0 : List Token := [.identifier "bool".toList, .identifier "cetta_continuation_hub_take_for_resume".toList, .punctuation "(".toList, .identifier "CettaContinuationHub".toList, .punctuation "*".toList, .identifier "hub".toList, .punctuation ",".toList, .identifier "size_t".toList, .identifier "index".toList, .punctuation ",".toList]
private theorem scanned0 : text0.foldl step initial = completed tokens0 := by decide +kernel

private def text1 : List Char := "        CettaOwnedContinuation *owned) {\n".toList
private def tokens1 : List Token := [.identifier "CettaOwnedContinuation".toList, .punctuation "*".toList, .identifier "owned".toList, .punctuation ")".toList, .punctuation "{".toList]
private theorem scanned1 : text1.foldl step initial = completed tokens1 := by decide +kernel

private def text2 : List Char := "    if (!hub || !hub->initialized || !owned || owned->payload ||\n".toList
private def tokens2 : List Token := [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "hub".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "hub".toList, .punctuation "->".toList, .identifier "initialized".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "owned".toList, .punctuation "||".toList, .identifier "owned".toList, .punctuation "->".toList, .identifier "payload".toList, .punctuation "||".toList]
private theorem scanned2 : text2.foldl step initial = completed tokens2 := by decide +kernel

private def text3 : List Char := "        !hub->store.identity || !hub->store.next_lease ||\n".toList
private def tokens3 : List Token := [.punctuation "!".toList, .identifier "hub".toList, .punctuation "->".toList, .identifier "store".toList, .punctuation ".".toList, .identifier "identity".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "hub".toList, .punctuation "->".toList, .identifier "store".toList, .punctuation ".".toList, .identifier "next_lease".toList, .punctuation "||".toList]
private theorem scanned3 : text3.foldl step initial = completed tokens3 := by decide +kernel

private def text4 : List Char := "        index >= cetta_continuation_store_length(&hub->store)) return false;\n".toList
private def tokens4 : List Token := [.identifier "index".toList, .punctuation ">=".toList, .identifier "cetta_continuation_store_length".toList, .punctuation "(".toList, .punctuation "&".toList, .identifier "hub".toList, .punctuation "->".toList, .identifier "store".toList, .punctuation ")".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "false".toList, .punctuation ";".toList]
private theorem scanned4 : text4.foldl step initial = completed tokens4 := by decide +kernel

private def text5 : List Char := "    CettaContinuationStore *store = &hub->store;\n".toList
private def tokens5 : List Token := [.identifier "CettaContinuationStore".toList, .punctuation "*".toList, .identifier "store".toList, .punctuation "=".toList, .punctuation "&".toList, .identifier "hub".toList, .punctuation "->".toList, .identifier "store".toList, .punctuation ";".toList]
private theorem scanned5 : text5.foldl step initial = completed tokens5 := by decide +kernel

private def text6 : List Char := "    const CettaOwnedContinuation *candidate = cetta_continuation_store_at(store,index);\n".toList
private def tokens6 : List Token := [.identifier "const".toList, .identifier "CettaOwnedContinuation".toList, .punctuation "*".toList, .identifier "candidate".toList, .punctuation "=".toList, .identifier "cetta_continuation_store_at".toList, .punctuation "(".toList, .identifier "store".toList, .punctuation ",".toList, .identifier "index".toList, .punctuation ")".toList, .punctuation ";".toList]
private theorem scanned6 : text6.foldl step initial = completed tokens6 := by decide +kernel

private def text7 : List Char := "    if (!candidate || candidate->resume_lease) return false;\n".toList
private def tokens7 : List Token := [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "candidate".toList, .punctuation "||".toList, .identifier "candidate".toList, .punctuation "->".toList, .identifier "resume_lease".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "false".toList, .punctuation ";".toList]
private theorem scanned7 : text7.foldl step initial = completed tokens7 := by decide +kernel

private def text8 : List Char := "    for (size_t i = 0u; i < store->lease_length; i++) {\n".toList
private def tokens8 : List Token := [.identifier "for".toList, .punctuation "(".toList, .identifier "size_t".toList, .identifier "i".toList, .punctuation "=".toList, .number "0u".toList, .punctuation ";".toList, .identifier "i".toList, .punctuation "<".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "lease_length".toList, .punctuation ";".toList, .identifier "i".toList, .punctuation "++".toList, .punctuation ")".toList, .punctuation "{".toList]
private theorem scanned8 : text8.foldl step initial = completed tokens8 := by decide +kernel

private def text9 : List Char := "        cetta_native_cost_charge(CETTA_COST_QUEUE_VISIT,1u);\n".toList
private def tokens9 : List Token := [.identifier "cetta_native_cost_charge".toList, .punctuation "(".toList, .identifier "CETTA_COST_QUEUE_VISIT".toList, .punctuation ",".toList, .number "1u".toList, .punctuation ")".toList, .punctuation ";".toList]
private theorem scanned9 : text9.foldl step initial = completed tokens9 := by decide +kernel

private def text10 : List Char := "        if (store->leases[i].occurrence == candidate->occurrence_id) return false;\n".toList
private def tokens10 : List Token := [.identifier "if".toList, .punctuation "(".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "leases".toList, .punctuation "[".toList, .identifier "i".toList, .punctuation "]".toList, .punctuation ".".toList, .identifier "occurrence".toList, .punctuation "==".toList, .identifier "candidate".toList, .punctuation "->".toList, .identifier "occurrence_id".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "false".toList, .punctuation ";".toList]
private theorem scanned10 : text10.foldl step initial = completed tokens10 := by decide +kernel

private def text11 : List Char := "    }\n".toList
private def tokens11 : List Token := [.punctuation "}".toList]
private theorem scanned11 : text11.foldl step initial = completed tokens11 := by decide +kernel

private def text12 : List Char := "    if (store->lease_length == store->lease_capacity) {\n".toList
private def tokens12 : List Token := [.identifier "if".toList, .punctuation "(".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "lease_length".toList, .punctuation "==".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "lease_capacity".toList, .punctuation ")".toList, .punctuation "{".toList]
private theorem scanned12 : text12.foldl step initial = completed tokens12 := by decide +kernel

private def text13 : List Char := "        size_t capacity = store->lease_capacity ? store->lease_capacity * 2u : 4u;\n".toList
private def tokens13 : List Token := [.identifier "size_t".toList, .identifier "capacity".toList, .punctuation "=".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "lease_capacity".toList, .punctuation "?".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "lease_capacity".toList, .punctuation "*".toList, .number "2u".toList, .punctuation ":".toList, .number "4u".toList, .punctuation ";".toList]
private theorem scanned13 : text13.foldl step initial = completed tokens13 := by decide +kernel

private def text14 : List Char := "        if (capacity < store->lease_capacity || capacity > SIZE_MAX / sizeof(*store->leases)) return false;\n".toList
private def tokens14 : List Token := [.identifier "if".toList, .punctuation "(".toList, .identifier "capacity".toList, .punctuation "<".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "lease_capacity".toList, .punctuation "||".toList, .identifier "capacity".toList, .punctuation ">".toList, .identifier "SIZE_MAX".toList, .punctuation "/".toList, .identifier "sizeof".toList, .punctuation "(".toList, .punctuation "*".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "leases".toList, .punctuation ")".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "false".toList, .punctuation ";".toList]
private theorem scanned14 : text14.foldl step initial = completed tokens14 := by decide +kernel

private def text15 : List Char := "        void *leases = realloc(store->leases,capacity*sizeof(*store->leases));\n".toList
private def tokens15 : List Token := [.identifier "void".toList, .punctuation "*".toList, .identifier "leases".toList, .punctuation "=".toList, .identifier "realloc".toList, .punctuation "(".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "leases".toList, .punctuation ",".toList, .identifier "capacity".toList, .punctuation "*".toList, .identifier "sizeof".toList, .punctuation "(".toList, .punctuation "*".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "leases".toList, .punctuation ")".toList, .punctuation ")".toList, .punctuation ";".toList]
private theorem scanned15 : text15.foldl step initial = completed tokens15 := by decide +kernel

private def text16 : List Char := "        if (!leases) return false;\n".toList
private def tokens16 : List Token := [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "leases".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "false".toList, .punctuation ";".toList]
private theorem scanned16 : text16.foldl step initial = completed tokens16 := by decide +kernel

private def text17 : List Char := "        store->leases = leases;\n".toList
private def tokens17 : List Token := [.identifier "store".toList, .punctuation "->".toList, .identifier "leases".toList, .punctuation "=".toList, .identifier "leases".toList, .punctuation ";".toList]
private theorem scanned17 : text17.foldl step initial = completed tokens17 := by decide +kernel

private def text18 : List Char := "        store->lease_capacity = capacity;\n".toList
private def tokens18 : List Token := [.identifier "store".toList, .punctuation "->".toList, .identifier "lease_capacity".toList, .punctuation "=".toList, .identifier "capacity".toList, .punctuation ";".toList]
private theorem scanned18 : text18.foldl step initial = completed tokens18 := by decide +kernel

private def text19 : List Char := "        cetta_native_cost_charge(CETTA_COST_FRAME_ALLOCATE,1u);\n".toList
private def tokens19 : List Token := [.identifier "cetta_native_cost_charge".toList, .punctuation "(".toList, .identifier "CETTA_COST_FRAME_ALLOCATE".toList, .punctuation ",".toList, .number "1u".toList, .punctuation ")".toList, .punctuation ";".toList]
private theorem scanned19 : text19.foldl step initial = completed tokens19 := by decide +kernel

private def text20 : List Char := "    }\n".toList
private def tokens20 : List Token := [.punctuation "}".toList]
private theorem scanned20 : text20.foldl step initial = completed tokens20 := by decide +kernel

private def text21 : List Char := "    if (!cetta_continuation_store_take(store,index,owned)) return false;\n".toList
private def tokens21 : List Token := [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "cetta_continuation_store_take".toList, .punctuation "(".toList, .identifier "store".toList, .punctuation ",".toList, .identifier "index".toList, .punctuation ",".toList, .identifier "owned".toList, .punctuation ")".toList, .punctuation ")".toList, .identifier "return".toList, .identifier "false".toList, .punctuation ";".toList]
private theorem scanned21 : text21.foldl step initial = completed tokens21 := by decide +kernel

private def text22 : List Char := "    owned->resume_store = store->identity;\n".toList
private def tokens22 : List Token := [.identifier "owned".toList, .punctuation "->".toList, .identifier "resume_store".toList, .punctuation "=".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "identity".toList, .punctuation ";".toList]
private theorem scanned22 : text22.foldl step initial = completed tokens22 := by decide +kernel

private def text23 : List Char := "    owned->resume_lease = store->next_lease;\n".toList
private def tokens23 : List Token := [.identifier "owned".toList, .punctuation "->".toList, .identifier "resume_lease".toList, .punctuation "=".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "next_lease".toList, .punctuation ";".toList]
private theorem scanned23 : text23.foldl step initial = completed tokens23 := by decide +kernel

private def text24 : List Char := "    store->next_lease = store->next_lease == UINT64_MAX ? 0u : store->next_lease+1u;\n".toList
private def tokens24 : List Token := [.identifier "store".toList, .punctuation "->".toList, .identifier "next_lease".toList, .punctuation "=".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "next_lease".toList, .punctuation "==".toList, .identifier "UINT64_MAX".toList, .punctuation "?".toList, .number "0u".toList, .punctuation ":".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "next_lease".toList, .punctuation "+".toList, .number "1u".toList, .punctuation ";".toList]
private theorem scanned24 : text24.foldl step initial = completed tokens24 := by decide +kernel

private def text25 : List Char := "    store->leases[store->lease_length++] = (CettaContinuationLease){\n".toList
private def tokens25 : List Token := [.identifier "store".toList, .punctuation "->".toList, .identifier "leases".toList, .punctuation "[".toList, .identifier "store".toList, .punctuation "->".toList, .identifier "lease_length".toList, .punctuation "++".toList, .punctuation "]".toList, .punctuation "=".toList, .punctuation "(".toList, .identifier "CettaContinuationLease".toList, .punctuation ")".toList, .punctuation "{".toList]
private theorem scanned25 : text25.foldl step initial = completed tokens25 := by decide +kernel

private def text26 : List Char := "        owned->occurrence_id,owned->resume_lease,owned->payload,owned->provider};\n".toList
private def tokens26 : List Token := [.identifier "owned".toList, .punctuation "->".toList, .identifier "occurrence_id".toList, .punctuation ",".toList, .identifier "owned".toList, .punctuation "->".toList, .identifier "resume_lease".toList, .punctuation ",".toList, .identifier "owned".toList, .punctuation "->".toList, .identifier "payload".toList, .punctuation ",".toList, .identifier "owned".toList, .punctuation "->".toList, .identifier "provider".toList, .punctuation "}".toList, .punctuation ";".toList]
private theorem scanned26 : text26.foldl step initial = completed tokens26 := by decide +kernel

private def text27 : List Char := "    cetta_native_cost_charge(CETTA_COST_CAPTURE,1u);\n".toList
private def tokens27 : List Token := [.identifier "cetta_native_cost_charge".toList, .punctuation "(".toList, .identifier "CETTA_COST_CAPTURE".toList, .punctuation ",".toList, .number "1u".toList, .punctuation ")".toList, .punctuation ";".toList]
private theorem scanned27 : text27.foldl step initial = completed tokens27 := by decide +kernel

private def text28 : List Char := "    return true;\n".toList
private def tokens28 : List Token := [.identifier "return".toList, .identifier "true".toList, .punctuation ";".toList]
private theorem scanned28 : text28.foldl step initial = completed tokens28 := by decide +kernel

private def text29 : List Char := "}".toList
private def tokens29 : List Token := [.punctuation "}".toList]
private theorem scanned29 : text29.foldl step initial = completed tokens29 := by decide +kernel

private def pieces : List (List Char × List Token) := [(text0, tokens0), (text1, tokens1), (text2, tokens2), (text3, tokens3), (text4, tokens4), (text5, tokens5), (text6, tokens6), (text7, tokens7), (text8, tokens8), (text9, tokens9), (text10, tokens10), (text11, tokens11), (text12, tokens12), (text13, tokens13), (text14, tokens14), (text15, tokens15), (text16, tokens16), (text17, tokens17), (text18, tokens18), (text19, tokens19), (text20, tokens20), (text21, tokens21), (text22, tokens22), (text23, tokens23), (text24, tokens24), (text25, tokens25), (text26, tokens26), (text27, tokens27), (text28, tokens28), (text29, tokens29)]
def source : List Char := pieces.flatMap Prod.fst
private def tokens : List Token := pieces.flatMap Prod.snd

private theorem scanned : List.Forall (fun piece =>
    piece.1.foldl step initial = completed piece.2) pieces :=
  ⟨scanned0, ⟨scanned1, ⟨scanned2, ⟨scanned3, ⟨scanned4, ⟨scanned5, ⟨scanned6, ⟨scanned7, ⟨scanned8, ⟨scanned9, ⟨scanned10, ⟨scanned11, ⟨scanned12, ⟨scanned13, ⟨scanned14, ⟨scanned15, ⟨scanned16, ⟨scanned17, ⟨scanned18, ⟨scanned19, ⟨scanned20, ⟨scanned21, ⟨scanned22, ⟨scanned23, ⟨scanned24, ⟨scanned25, ⟨scanned26, ⟨scanned27, ⟨scanned28, scanned29⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

private theorem lexed : lex source = .ok tokens :=
  lex_of_completed source tokens (completed_pieces pieces scanned)

def types : TypeNames :=
  ["bool".toList, "size_t".toList, "void".toList, "CettaContinuationHub".toList,
   "CettaContinuationStore".toList, "CettaOwnedContinuation".toList,
   "CettaContinuationLease".toList]

private def hubStore (field : String) : CExpr :=
  .field (member "hub" "store") field.toList false

private def any (first : CExpr) (others : List CExpr) : CExpr :=
  others.foldl (.binary .or) first

private def no : List CStatement := [.return (some (.bool false))]

private def charge (kind : String) : CStatement :=
  .effect (.call "cetta_native_cost_charge".toList
    [.identifier kind.toList, .unsignedInteger 1])

private def fullGuard : CExpr := any (.unary .not (.identifier "hub".toList))
  [.unary .not (member "hub" "initialized"),
   .unary .not (.identifier "owned".toList), member "owned" "payload",
   .unary .not (hubStore "identity"), .unary .not (hubStore "next_lease"),
   .binary .ge (.identifier "index".toList)
     (.call "cetta_continuation_store_length".toList
       [.unary .address (member "hub" "store")])]

def leaseRhs : CExpr := .aggregate ⟨"CettaContinuationLease".toList, 0⟩
  [member "owned" "occurrence_id", member "owned" "resume_lease",
   member "owned" "payload", member "owned" "provider"]

def body : List CStatement :=
  [.branch fullGuard no [],
   .declare ⟨"CettaContinuationStore".toList, 1⟩ "store".toList
     (.unary .address (member "hub" "store")),
   .declarePointeeConst ⟨"CettaOwnedContinuation".toList, 1⟩ "candidate".toList
     (.call "cetta_continuation_store_at".toList
       [.identifier "store".toList, .identifier "index".toList]),
   .branch (.binary .or (.unary .not (.identifier "candidate".toList))
     (member "candidate" "resume_lease")) no [],
   .forLoop ⟨"size_t".toList, 0⟩ ['i'] (.unsignedInteger 0)
     (.binary .lt (.identifier ['i']) (member "store" "lease_length"))
     (.postIncrement (.identifier ['i']))
     [charge "CETTA_COST_QUEUE_VISIT",
      .branch (.binary .eq
        (.field (.index (member "store" "leases") (.identifier ['i'])) "occurrence".toList false)
        (member "candidate" "occurrence_id")) no []],
   .branch (.binary .eq (member "store" "lease_length") (member "store" "lease_capacity"))
     [.declare ⟨"size_t".toList, 0⟩ "capacity".toList
        (.conditional (member "store" "lease_capacity")
          (.binary .mul (member "store" "lease_capacity") (.unsignedInteger 2))
          (.unsignedInteger 4)),
      .branch (.binary .or
        (.binary .lt (.identifier "capacity".toList) (member "store" "lease_capacity"))
        (.binary .gt (.identifier "capacity".toList)
          (.binary .div (.identifier "SIZE_MAX".toList)
            (.sizeOfExpr (.unary .dereference (member "store" "leases")))))) no [],
      .declare ⟨"void".toList, 1⟩ "leases".toList
        (.call "realloc".toList [member "store" "leases",
          .binary .mul (.identifier "capacity".toList)
            (.sizeOfExpr (.unary .dereference (member "store" "leases")))]),
      .branch (.unary .not (.identifier "leases".toList)) no [],
      .assign (member "store" "leases") (.identifier "leases".toList),
      .assign (member "store" "lease_capacity") (.identifier "capacity".toList),
      charge "CETTA_COST_FRAME_ALLOCATE"] [],
   .branch (.unary .not (.call "cetta_continuation_store_take".toList
     [.identifier "store".toList, .identifier "index".toList,
      .identifier "owned".toList])) no [],
   .assign (member "owned" "resume_store") (member "store" "identity"),
   .assign (member "owned" "resume_lease") (member "store" "next_lease"),
   .assign (member "store" "next_lease")
     (.conditional (.binary .eq (member "store" "next_lease")
        (.identifier "UINT64_MAX".toList)) (.unsignedInteger 0)
        (.binary .add (member "store" "next_lease") (.unsignedInteger 1))),
   .assign (.index (member "store" "leases")
     (.postIncrement (member "store" "lease_length"))) leaseRhs,
   charge "CETTA_COST_CAPTURE",
   .return (some (.bool true))]

def parsed : CQualifiedFunction :=
  ⟨⟨"bool".toList, 0⟩, "cetta_continuation_hub_take_for_resume".toList,
   [⟨⟨⟨"CettaContinuationHub".toList, 1⟩, "hub".toList⟩, false⟩,
    ⟨⟨⟨"size_t".toList, 0⟩, "index".toList⟩, false⟩,
    ⟨⟨⟨"CettaOwnedContinuation".toList, 1⟩, "owned".toList⟩, false⟩], body⟩

private theorem token_count : tokens.length = 324 := by decide +kernel

private theorem parsed_exact : qualifiedFunction?
    (2 * tokens.length + 4) types (ordinaryFunctionTokens tokens) = some (parsed, []) := by
  rw [token_count]
  rfl

/-- Source recognition retains every refusal, capacity branch, charge and mutation.
It does not execute allocator calls or certify compiled pointer accesses. -/
theorem source_recognized : qualifiedFunctionText? types source = some parsed :=
  function_text_using_of_parts (qualifiedParameter? types) types source tokens parsed lexed parsed_exact


namespace Append

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.ScalarRead
open Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn
open NativeC.PostIndex
open NativeC.PostIndex.WordStore

variable {Ptr : Type} [DecidableEq Ptr]

variable {Address Provider : Type} {width : Nat}


/-- Issuance keeps the independent ownership specification and all backing
slots. Only store identity and the newly reserved token are changed. -/
theorem issued_registration_of_store (registry : Registry Address Provider)
    (selected : Handle Address Provider) (token : Nat)
    (slots : List (Row Address Provider)) (count : BitVec width)
    (sized : slots.length < 2 ^ width) (room : count.toNat < slots.length)
    (represented : registry.rows = slots.take count.toNat) :
    ∃ next after,
      WordStore.store slots count { selected.row with token := token } = some (next, after) ∧
      (registerIssued registry selected token).1.rows = after.take next.toNat ∧
      (registerIssued registry selected token).2.store = registry.identity ∧
      (registerIssued registry selected token).2.parent = selected.parent ∧
      (registerIssued registry selected token).2.row = { selected.row with token := token } ∧
      next.toNat = count.toNat + 1 ∧ after.length = slots.length ∧
      after.take count.toNat = slots.take count.toNat := by
  refine ⟨count + 1, slots.set count.toNat { selected.row with token := token },
    if_pos room, ?_, rfl, rfl, rfl, WordStore.increment_is_exact slots count sized room,
    List.length_set, List.take_set_of_le (Nat.le_refl _)⟩
  rw [active_prefix_append slots count _ sized room]
  simp only [registerIssued, represented]


/-- Four typed operand reads preserve the constructor's declared order.
Pointer layout and the live field-reader contract remain external. -/
def leaseRow? (environment : Environment Ptr) (fields : FieldReader Ptr) :
    CExpr → Option (Row (Option Ptr) (Option Ptr))
  | .aggregate type [occurrence, token, payload, provider] =>
      if type = ⟨"CettaContinuationLease".toList, 0⟩ then
        match expression environment fields occurrence, expression environment fields token,
            expression environment fields payload, expression environment fields provider with
        | some (.unsigned64 occurrence), some (.unsigned64 token),
            some (.identity payload), some (.identity provider) =>
            some ⟨occurrence.toNat, token.toNat, payload, provider⟩
        | _, _, _, _ => none
      else none
  | _ => none

def site : AppendSyntax :=
  ⟨"store".toList, "leases".toList, "lease_length".toList⟩

theorem actual_append_statement : body[10]? =
    some (site.statement leaseRhs) := rfl

theorem actual_append_recognized :
    body[10]?.bind appendSyntax? =
      some (site, leaseRhs) := by
  rw [actual_append_statement]
  simp only [Option.bind_some]
  exact recognizes_authored_append _ _

theorem actual_row_read (environment : Environment Ptr) (fields : FieldReader Ptr)
    (owner : Ptr) (occurrence token : UInt64) (payload provider : Option Ptr)
    (ownerRead : environment "owned".toList = some (.identity (some owner)))
    (occurrenceRead : fields owner "occurrence_id".toList = some (.unsigned64 occurrence))
    (tokenRead : fields owner "resume_lease".toList = some (.unsigned64 token))
    (payloadRead : fields owner "payload".toList = some (.identity payload))
    (providerRead : fields owner "provider".toList = some (.identity provider)) :
    leaseRow? environment fields leaseRhs =
      some ⟨occurrence.toNat, token.toNat, payload, provider⟩ := by
  change (match
    expression environment fields (.field (.identifier "owned".toList) "occurrence_id".toList true),
    expression environment fields (.field (.identifier "owned".toList) "resume_lease".toList true),
    expression environment fields (.field (.identifier "owned".toList) "payload".toList true),
    expression environment fields (.field (.identifier "owned".toList) "provider".toList true) with
    | some (.unsigned64 o), some (.unsigned64 t), some (.identity p), some (.identity r) =>
      some (⟨o.toNat, t.toNat, p, r⟩ : Row (Option Ptr) (Option Ptr))
    | _, _, _, _ => none) = _
  rw [pointer_field_read environment fields _ _ owner _ ownerRead occurrenceRead,
    pointer_field_read environment fields _ _ owner _ ownerRead tokenRead,
    pointer_field_read environment fields _ _ owner _ ownerRead payloadRead,
    pointer_field_read environment fields _ _ owner _ ownerRead providerRead]

def resolve (environment : Environment Ptr) (fields : FieldReader Ptr)
    (slots : List (Row (Option Ptr) (Option Ptr))) (count : UInt64)
    (actual : AppendSyntax) (rhs : CExpr) :
    Option (List (Row (Option Ptr) (Option Ptr)) × BitVec 64 × Row (Option Ptr) (Option Ptr)) :=
  if actual = site then (leaseRow? environment fields rhs).map
    (fun row => (slots, count.toBitVec, row)) else none

theorem actual_append_execution (environment : Environment Ptr) (fields : FieldReader Ptr)
    (slots : List (Row (Option Ptr) (Option Ptr))) (count : UInt64)
    (owner : Ptr) (occurrence token : UInt64) (payload provider : Option Ptr)
    (ownerRead : environment "owned".toList = some (.identity (some owner)))
    (occurrenceRead : fields owner "occurrence_id".toList = some (.unsigned64 occurrence))
    (tokenRead : fields owner "resume_lease".toList = some (.unsigned64 token))
    (payloadRead : fields owner "payload".toList = some (.identity payload))
    (providerRead : fields owner "provider".toList = some (.identity provider)) :
    body[10]?.bind (executeAppend (resolve environment fields slots count)) =
      WordStore.store slots count.toBitVec ⟨occurrence.toNat, token.toNat, payload, provider⟩ := by
  rw [actual_append_statement]
  simp only [Option.bind_some]
  apply recognized_append_execution
  unfold resolve
  rw [if_pos rfl,
    actual_row_read environment fields owner occurrence token payload provider
      ownerRead occurrenceRead tokenRead payloadRead providerRead]
  rfl

theorem actual_append_issues (environment : Environment Ptr) (fields : FieldReader Ptr)
    (registry : Registry (Option Ptr) (Option Ptr))
    (selected : Handle (Option Ptr) (Option Ptr))
    (slots : List (Row (Option Ptr) (Option Ptr))) (count : UInt64)
    (owner : Ptr) (occurrence token : UInt64) (payload provider : Option Ptr)
    (ownerRead : environment "owned".toList = some (.identity (some owner)))
    (occurrenceRead : fields owner "occurrence_id".toList = some (.unsigned64 occurrence))
    (tokenRead : fields owner "resume_lease".toList = some (.unsigned64 token))
    (payloadRead : fields owner "payload".toList = some (.identity payload))
    (providerRead : fields owner "provider".toList = some (.identity provider))
    (representedOccurrence : selected.row.occurrence = occurrence.toNat)
    (representedPayload : selected.row.payload = payload)
    (representedProvider : selected.row.provider = provider)
    (sized : slots.length < 2 ^ 64) (room : count.toNat < slots.length)
    (representedRows : registry.rows = slots.take count.toNat) :
    ∃ next after,
      body[10]?.bind (executeAppend (resolve environment fields slots count)) =
        some (next, after) ∧
      (registerIssued registry selected token.toNat).1.rows = after.take next.toNat ∧
      (registerIssued registry selected token.toNat).2.store = registry.identity ∧
      (registerIssued registry selected token.toNat).2.parent = selected.parent ∧
      (registerIssued registry selected token.toNat).2.row =
        { selected.row with token := token.toNat } ∧
      next.toNat = count.toNat + 1 ∧ after.length = slots.length ∧
      after.take count.toNat = slots.take count.toNat := by
  have sameRow : { selected.row with token := token.toNat } =
      (⟨occurrence.toNat, token.toNat, payload, provider⟩ : Row (Option Ptr) (Option Ptr)) := by
    cases selected with
    | mk oldStore parent row =>
      cases row with
      | mk o t p v =>
        change o = occurrence.toNat at representedOccurrence
        change p = payload at representedPayload
        change v = provider at representedProvider
        subst o
        subst p
        subst v
        rfl
  have scalarRoom : count.toBitVec.toNat < slots.length := by simpa using room
  have scalarRows : registry.rows = slots.take count.toBitVec.toNat := by
    simpa using representedRows
  obtain ⟨next, after, stored, rows, identity, parent, issued, increment, extent, retainedPrefix⟩ :=
    issued_registration_of_store registry selected token.toNat slots count.toBitVec
      sized scalarRoom scalarRows
  refine ⟨next, after, ?_, rows, identity, parent, issued, ?_, extent, ?_⟩
  · rw [actual_append_execution environment fields slots count owner occurrence token
      payload provider ownerRead occurrenceRead tokenRead payloadRead providerRead,
      ← sameRow]
    exact stored
  · simpa using increment
  · simpa using retainedPrefix

namespace Controls

def environment : Environment Nat := fun name =>
  if name = "owned".toList then some (.identity (some 7)) else none

def fields : FieldReader Nat := fun owner name =>
  if owner = 7 then
    if name = "occurrence_id".toList then some (.unsigned64 4294967296)
    else if name = "resume_lease".toList then some (.unsigned64 18446744073709551615)
    else if name = "payload".toList then some (.identity (some 11))
    else if name = "provider".toList then some (.identity (some 13)) else none
  else none

theorem full_word_and_two_identities_survive :
    leaseRow? environment fields leaseRhs =
      some ⟨4294967296, 18446744073709551615, some 11, some 13⟩ := by decide +kernel

theorem missing_field_is_not_zero_filled :
    leaseRow? environment (fun _ _ => none) leaseRhs = none :=
  by decide +kernel

theorem narrow_read_is_not_silently_widened :
    leaseRow? environment (fun _ _ => some (.unsigned 7))
      leaseRhs = none := by decide +kernel

end Controls


end Append

end TakeForResume

end IssuedReturnSource

/-! Accepted work renews only an earlier cancellation. This source comparison
uses a logical enum-field view with explicit borrowed storage. It does not
establish physical struct layout, enum ABI, whole-controller orchestration or
compiled-code refinement. -/
namespace AcceptedProgress

/-- The word is the logical encoding of an enum value. This interface is a
field view; it does not declare the physical C struct or its ABI layout. -/
def representation : NativeC.Representation :=
  ⟨"ResumeCompletion", ⟨[⟨"Control", [⟨"completion", .word⟩]⟩], [], [], []⟩, []⟩

def header : Header :=
  ⟨"prime_native_control_accepted_progress", [⟨"control", .ref (.named "Control")⟩], .unit⟩

def macros : NativeC.PrimitiveBindings :=
  [("CETTA_EVAL_INCOMPLETE_CANCELLED".toList, .word 2),
   ("CETTA_EVAL_COMPLETE".toList, .word 0)]

def source : List Char :=
  "static void prime_native_control_accepted_progress(PrimeNativeControl *control) {\n    if (control->completion == CETTA_EVAL_INCOMPLETE_CANCELLED)\n        control->completion = CETTA_EVAL_COMPLETE;\n}\n".toList

/-- Authored independently of the C reader. The load and conditional store
remain distinct operations on an existing live completion field. -/
def code : List Instruction :=
  [.temporary 2 (.ref .word)
      (.fieldAddress (.temporary 1 (.ref (.named "Control"))) "Control" 0),
   .temporary 3 .word (.indirectRead (.temporary 2 (.ref .word))),
   .temporary 4 .bool (.binary (.compare .eq) (.temporary 3 .word) (.word 2)),
   .branch (.value (.temporary 4 .bool))
     [.temporary 5 (.ref .word)
        (.fieldAddress (.temporary 1 (.ref (.named "Control"))) "Control" 0),
      .write (.temporary 5 (.ref .word)) (.word 0)] []]

def function : NativeIR.Function :=
  ⟨header, [.temporary 1 (.ref (.named "Control")) (.readLocal "control")] ++ code ++
      [.return .unit], 5⟩

private def sourceTokens : List NativeC.Token :=
  [.identifier "static".toList, .identifier "void".toList,
   .identifier "prime_native_control_accepted_progress".toList,
   .punctuation ['('], .identifier "PrimeNativeControl".toList,
   .punctuation ['*'], .identifier "control".toList, .punctuation [')'],
   .punctuation ['{'], .identifier "if".toList, .punctuation ['('],
   .identifier "control".toList, .punctuation ['-', '>'],
   .identifier "completion".toList, .punctuation ['=', '='],
   .identifier "CETTA_EVAL_INCOMPLETE_CANCELLED".toList, .punctuation [')'],
   .identifier "control".toList, .punctuation ['-', '>'],
   .identifier "completion".toList, .punctuation ['='],
   .identifier "CETTA_EVAL_COMPLETE".toList, .punctuation [';'],
   .punctuation ['}']]

private theorem source_lexed : NativeC.lex source = .ok sourceTokens := by
  decide +kernel

private def sourceParsed : NativeC.CQualifiedFunction :=
  ⟨⟨"void".toList, 0⟩, "prime_native_control_accepted_progress".toList,
   [⟨⟨⟨"PrimeNativeControl".toList, 1⟩, "control".toList⟩, false⟩],
   [.branch
     (.binary .eq (.field (.identifier "control".toList) "completion".toList true)
       (.identifier "CETTA_EVAL_INCOMPLETE_CANCELLED".toList))
     [.assign (.field (.identifier "control".toList) "completion".toList true)
       (.identifier "CETTA_EVAL_COMPLETE".toList)] []]⟩

private theorem source_parsed : NativeC.qualifiedFunction? (2 * sourceTokens.length + 4)
    ["void".toList, "PrimeNativeControl".toList]
    (NativeC.ordinaryFunctionTokens sourceTokens) = some (sourceParsed, []) := by
  rfl

theorem source_admitted : NativeC.qualifiedParameterStoreFunctionText?
    representation ["void".toList, "PrimeNativeControl".toList] header
    [("PrimeNativeControl".toList, "Control")] [false] macros source = some function := by
  rw [NativeC.qualified_parameter_store_text_of_parts representation
    ["void".toList, "PrimeNativeControl".toList] header
    [("PrimeNativeControl".toList, "Control")] [false] macros source sourceTokens
    sourceParsed source_lexed source_parsed]
  rw [show source.length + 1 = 200 from by decide +kernel]
  rfl

def constSource : List Char :=
  "static void prime_native_control_accepted_progress(const PrimeNativeControl *control) {\n    if (control->completion == CETTA_EVAL_INCOMPLETE_CANCELLED)\n        control->completion = CETTA_EVAL_COMPLETE;\n}\n".toList

theorem const_destination_refused : NativeC.qualifiedParameterStoreFunctionText?
    representation ["void".toList, "PrimeNativeControl".toList] header
    [("PrimeNativeControl".toList, "Control")] [true] macros constSource = none := by
  decide +kernel

private def bound {World : Type} (state : TargetState World) (storage : Nat)
    (address : Address) : TargetFrame × TargetState World :=
  targetDeclareLocal (targetEmptyFrame storage) state "control"
    (.ref (.named "Control")) (.reference (some address))

private def captured (frame : TargetFrame) (address : Address) : TargetFrame :=
  targetDeclareTemporary frame 1 (.reference (some address))

private def returnedFrame (frame : TargetFrame) (address : Address) (value : BitVec 64) :
    TargetFrame :=
  fieldEqualFrame (captured frame address) address 0 2 value 2

private theorem memory_parameters (memory : TargetMemory) (storage : Nat)
    (address : Address) (value : BitVec 64) (different : address.storage ≠ storage) :
    conditionalWordFieldMemory
        (targetParameterMemory memory storage 0 [.reference (some address)])
        (sourceFieldAddress address 0) value 2 0 =
      (conditionalWordFieldMemory memory (sourceFieldAddress address 0) value 2 0).map
        (fun post => targetParameterMemory post storage 0 [.reference (some address)]) := by
  unfold conditionalWordFieldMemory
  by_cases selected : (value == 2) = true
  · simp only [selected, if_true]
    exact targetWrite_parameter_memory_other_storage memory storage 0 _ _ _ different
  · simp only [Bool.eq_false_iff.mpr selected, Bool.false_eq_true, if_false, Option.map_some]

private theorem memory_fresh {memory after : TargetMemory} {storage : Nat}
    (fresh : targetFreshFrame memory storage) (address : Address) (value : BitVec 64)
    (different : storage ≠ address.storage)
    (changed : conditionalWordFieldMemory memory (sourceFieldAddress address 0) value 2 0 =
      some after) : targetFreshFrame after storage := by
  unfold conditionalWordFieldMemory at changed
  by_cases selected : (value == 2) = true
  · simp only [selected, if_true] at changed
    exact targetFreshFrame_after_write (address := sourceFieldAddress address 0) fresh different changed
  · simp only [Bool.eq_false_iff.mpr selected, Bool.false_eq_true, if_false] at changed
    cases Option.some.inj changed
    exact fresh

private theorem body_exact {World : Type}
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (storage : Nat) (address : Address) (value : BitVec 64)
    (fresh : targetFreshFrame state.memory storage)
    (loaded : targetRead state.memory (sourceFieldAddress address 0) = some (.word value))
    (memory : TargetMemory)
    (changed : conditionalWordFieldMemory state.memory (sourceFieldAddress address 0) value 2 0 =
      some memory) (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun representation.interface heap calls .unit root function.body
      (bound state storage address).1 (bound state storage address).2 out ↔
      out = ⟨.returned .unit, returnedFrame (bound state storage address).1 address value,
        { state with memory := targetParameterMemory memory storage 0 [.reference (some address)] }⟩ := by
  let entry := bound state storage address
  have localRead : targetLocalValue entry.1 entry.2 "control" = some (.reference (some address)) :=
    target_singleton_parameter_readback state storage
      ⟨"control", .ref (.named "Control")⟩ (.reference (some address))
  change TargetRun _ _ _ _ root
    (.temporary 1 (.ref (.named "Control")) (.readLocal "control") :: (code ++ [.return .unit]))
    entry.1 entry.2 out ↔ _
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (by rfl : entry.1.temporaryNames.contains 1 = false) (.local localRead))]
  have baseRead : TargetAtomEval representation.interface (captured entry.1 address) entry.2
      (.temporary 1 (.ref (.named "Control"))) (.reference (some address)) :=
    declared_temporary_atom representation.interface entry.1 entry.2 1 _ _
  have names : TemporaryNamesBound (captured entry.1 address) 1 := by
    intro identity present
    have same : identity = 1 := by
      simpa [entry, captured, bound, targetDeclareLocal, targetEmptyFrame, targetDeclareTemporary,
        List.contains_iff_mem] using present
    omega
  have hscope : TemporariesScoped (captured entry.1 address) :=
    target_declared_names_complete _ _ _ (by intro _ _; rfl)
  have separate : address.storage ≠ storage :=
    (targetFreshFrame_storage_ne_read (address := sourceFieldAddress address 0) fresh loaded).symm
  have boundRead : targetRead entry.2.memory (sourceFieldAddress address 0) = some (.word value) :=
    (targetRead_parameter_memory_other_storage state.memory storage 0
      [.reference (some address)] (sourceFieldAddress address 0) separate).trans loaded
  have boundChanged : conditionalWordFieldMemory entry.2.memory
      (sourceFieldAddress address 0) value 2 0 =
        some (targetParameterMemory memory storage 0 [.reference (some address)]) := by
    change conditionalWordFieldMemory
      (targetParameterMemory state.memory storage 0 [.reference (some address)])
      (sourceFieldAddress address 0) value 2 0 = _
    rw [memory_parameters state.memory storage address value separate, changed]
    rfl
  have exactCode (ending : TargetBlockOutcome World) :
      TargetRun representation.interface heap calls .unit root code
        (captured entry.1 address) entry.2 ending ↔
      ending = ⟨.normal, returnedFrame entry.1 address value,
        { entry.2 with memory := targetParameterMemory memory storage 0 [.reference (some address)] }⟩ := by
    change TargetRun _ _ _ _ _
      (conditionalWordFieldCode (.temporary 1 (.ref (.named "Control"))) "Control" 0 2 2 0) _ _ _ ↔ _
    rw [conditional_word_field_code_exact baseRead (by change 1 ≤ 1; exact Nat.le_refl _) names (by decide)
      hscope value 2 0 boundRead "Control" root]
    constructor
    · rintro ⟨after, updated, same⟩
      cases Option.some.inj (boundChanged.symm.trans updated)
      exact same
    · intro same
      exact ⟨_, boundChanged, same⟩
  change TargetRun representation.interface heap calls .unit root
    (code ++ [.return .unit]) (captured entry.1 address) entry.2 out ↔ _
  rw [target_normal_prefix_then_exact (by simp [code, jumpFreeCode, jumpFreeInstruction] : jumpFreeCode code = true) exactCode]
  exact target_return_then_exact .unit root [] out

/-- The exact admitted helper returns unit and retains the entire caller
state apart from its conditional completion-field write. Invocation storage
is fresh, and caller field liveness establishes the required separation. -/
theorem invocation_exact {World : Type}
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (address : Address) (value : BitVec 64)
    (loaded : targetRead state.memory (sourceFieldAddress address 0) = some (.word value))
    (result : TargetRawResult World) :
    TargetFunctionBody representation.interface heap calls function [.reference (some address)]
      state result ↔ (∃ storage, targetFreshFrame state.memory storage) ∧
      ∃ memory, conditionalWordFieldMemory state.memory (sourceFieldAddress address 0) value 2 0 =
        some memory ∧ result = ⟨.unit, { state with memory := memory }⟩ := by
  have total : ∃ memory, conditionalWordFieldMemory state.memory
      (sourceFieldAddress address 0) value 2 0 = some memory := by
    unfold conditionalWordFieldMemory
    by_cases selected : (value == 2) = true
    · simp only [selected, if_true]
      exact targetWrite_defined_of_read loaded (.word 0)
    · simp only [Bool.eq_false_iff.mpr selected, Bool.false_eq_true, if_false]
      exact ⟨state.memory, rfl⟩
  constructor
  · intro ran
    cases ran with
    | @run storage frame entry out raw fresh parameters body returned =>
      have pair : (frame, entry) = bound state storage address := (Option.some.inj parameters).symm
      have frameEq : frame = (bound state storage address).1 := congrArg Prod.fst pair
      have stateEq : entry = (bound state storage address).2 := congrArg Prod.snd pair
      subst frame
      subst entry
      obtain ⟨memory, changed⟩ := total
      have exactBody := (body_exact heap calls state storage address value fresh loaded memory changed
        function.body out).mp body
      have rawEq : raw = .unit := TargetFlow.returned.inj
        (returned.symm.trans (congrArg TargetBlockOutcome.flow exactBody))
      have separate : storage ≠ address.storage := targetFreshFrame_storage_ne_read (address := sourceFieldAddress address 0) fresh loaded
      have released := target_parameter_memory_release memory storage [.reference (some address)]
        (memory_fresh fresh address value separate changed)
      have teardown : (targetLeaveScope (targetEmptyFrame storage)
          (returnedFrame (bound state storage address).1 address value)
          { state with memory := targetParameterMemory memory storage 0 [.reference (some address)] }).2 =
        { state with memory := memory } :=
        target_invocation_teardown state storage 1 _ _ _ rfl rfl released
      refine ⟨⟨storage, fresh⟩, memory, changed, ?_⟩
      rw [rawEq, exactBody]
      exact congrArg (TargetRawResult.mk .unit) teardown
  · rintro ⟨⟨storage, fresh⟩, memory, changed, rfl⟩
    let out : TargetBlockOutcome World :=
      ⟨.returned .unit, returnedFrame (bound state storage address).1 address value,
        { state with memory := targetParameterMemory memory storage 0 [.reference (some address)] }⟩
    have body := (body_exact heap calls state storage address value fresh loaded memory changed
      function.body out).mpr rfl
    have executed : TargetFunctionBody representation.interface heap calls function
        [.reference (some address)] state
        ⟨.unit, (targetLeaveScope (targetEmptyFrame storage) out.frame out.state).2⟩ :=
      .run fresh (by rfl) body rfl
    have separate : storage ≠ address.storage := targetFreshFrame_storage_ne_read (address := sourceFieldAddress address 0) fresh loaded
    have released := target_parameter_memory_release memory storage [.reference (some address)]
      (memory_fresh fresh address value separate changed)
    have teardown : (targetLeaveScope (targetEmptyFrame storage) out.frame out.state).2 =
        { state with memory := memory } :=
      target_invocation_teardown state storage 1 _ _ _ rfl rfl released
    rw [teardown] at executed
    exact executed

/-- The independent completion-value specification. The admitted helper
implements this update through its defined live field. -/
def renewed (completion : BitVec 64) : BitVec 64 :=
  if completion = 2 then 0 else completion

theorem cancelled_renewed : renewed 2 = 0 := by decide

theorem other_reason_retained (completion : BitVec 64) (other : completion ≠ 2) :
    renewed completion = completion := by
  unfold renewed
  rw [if_neg other]

/-- The conditional write agrees with the independent completion-value
specification and retains allocation ownership. -/
theorem memory_observation {memory after : TargetMemory} (address : Address)
    (value : BitVec 64)
    (loaded : targetRead memory (sourceFieldAddress address 0) = some (.word value))
    (changed : conditionalWordFieldMemory memory (sourceFieldAddress address 0) value 2 0 =
      some after) :
    targetRead after (sourceFieldAddress address 0) = some (.word (renewed value)) ∧
      after.owned = memory.owned := by
  by_cases cancelled : value = 2
  · subst value
    simp only [conditionalWordFieldMemory, beq_self_eq_true, if_true] at changed
    simpa only [renewed, ↓reduceIte] using targetRead_after_write changed
  · have different : (value == 2) = false := beq_eq_false_iff_ne.mpr cancelled
    simp only [conditionalWordFieldMemory, different, Bool.false_eq_true, if_false] at changed
    cases Option.some.inj changed
    exact ⟨by simpa only [renewed, if_neg cancelled] using loaded, rfl⟩

/-- A defined invocation changes only its live completion field. The caller's
external world includes any supplied residual, account or scope observation. -/
theorem invocation_observation {World : Type}
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (address : Address) (value : BitVec 64)
    (loaded : targetRead state.memory (sourceFieldAddress address 0) = some (.word value))
    (result : TargetRawResult World)
    (ran : TargetFunctionBody representation.interface heap calls function
      [.reference (some address)] state result) :
    result.value = .unit ∧ result.state.external = state.external ∧
      result.state.fault = state.fault ∧
      result.state.allocatorStats = state.allocatorStats ∧
      result.state.memory.owned = state.memory.owned ∧
      targetRead result.state.memory (sourceFieldAddress address 0) = some (.word (renewed value)) := by
  obtain ⟨_, memory, changed, rfl⟩ := (invocation_exact heap calls state address value loaded result).mp ran
  obtain ⟨read, owned⟩ := memory_observation address value loaded changed
  exact ⟨rfl, rfl, rfl, rfl, owned, read⟩

namespace Controls

private def address : Address := ⟨11, 0, []⟩

private def state (tag : BitVec 64) : TargetState Nat :=
  ⟨⟨fun storage element =>
    if storage = 11 ∧ element = 0 then some (.record "Control"
      [.word tag, .word 99, .reference (some address)]) else none,
    fun _ => none⟩, none, true, false, 37, AllocatorStats.targetEmpty⟩

private def noServices : TargetCalls Nat := fun _ _ _ _ _ => False

private theorem fresh (tag : BitVec 64) : targetFreshFrame (state tag).memory 12 := by
  constructor
  · rfl
  · intro position
    simp [state]

private theorem loaded (tag : BitVec 64) :
    targetRead (state tag).memory (sourceFieldAddress address 0) = some (.word tag) := by
  rfl

private theorem changed (tag : BitVec 64) :
    conditionalWordFieldMemory (state tag).memory (sourceFieldAddress address 0) tag 2 0 =
      some (state (renewed tag)).memory := by
  by_cases cancelled : tag = 2
  · subst tag
    simp only [renewed, conditionalWordFieldMemory, beq_self_eq_true, ↓reduceIte]
    change some (targetStoreCell (state 2).memory 11 0
      (.record "Control" [.word 0, .word 99, .reference (some address)])) = some (state 0).memory
    apply congrArg some
    have cells : (targetStoreCell (state 2).memory 11 0
        (.record "Control" [.word 0, .word 99, .reference (some address)])).cells =
        (state 0).memory.cells := by
      funext candidate position
      by_cases here : candidate = 11 <;> by_cases first : position = 0 <;>
        simp [targetStoreCell, state, here, first]
    exact congrArg (fun contents => TargetMemory.mk contents (state 0).memory.owned) cells
  · have different : (tag == 2) = false := beq_eq_false_iff_ne.mpr cancelled
    simp only [renewed, if_neg cancelled, conditionalWordFieldMemory, different,
      Bool.false_eq_true, if_false]

/-- Each actual completion tag executes through the admitted helper body;
no external service is available to make an omitted operation pass. -/
theorem all_completion_tags_execute (heap : TargetHeapSemantics Nat) (tag : Fin 7) :
    TargetFunctionBody representation.interface heap noServices function
      [.reference (some address)] (state (BitVec.ofNat 64 tag.val))
      ⟨.unit, state (renewed (BitVec.ofNat 64 tag.val))⟩ := by
  apply (invocation_exact heap noServices (state (BitVec.ofNat 64 tag.val)) address _
    (loaded _) _).mpr
  exact ⟨⟨12, fresh _⟩, _, changed _, rfl⟩

theorem cancelled_state_executes (heap : TargetHeapSemantics Nat) :
    TargetFunctionBody representation.interface heap noServices function
      [.reference (some address)] (state 2) ⟨.unit, state 0⟩ :=
  all_completion_tags_execute heap ⟨2, by decide⟩

theorem other_fields_and_alias_retained :
    targetRead (state (renewed 2)).memory (sourceFieldAddress address 1) = some (.word 99) ∧
      targetRead (state (renewed 2)).memory (sourceFieldAddress address 2) =
        some (.reference (some address)) ∧
      targetRead (state (renewed 2)).memory (sourceFieldAddress address 0) = some (.word 0) := by
  exact ⟨rfl, rfl, rfl⟩

theorem omitted_renewal_refused (heap : TargetHeapSemantics Nat) :
    ¬ TargetFunctionBody representation.interface heap noServices function
      [.reference (some address)] (state 2) ⟨.unit, state 2⟩ := by
  intro ran
  have read := (invocation_observation heap noServices (state 2) address 2 (loaded 2) _ ran).2.2.2.2.2
  have words : (2 : BitVec 64) = 0 := TargetValue.word.inj (Option.some.inj read)
  have numbers := congrArg BitVec.toNat words
  contradiction

theorem erasing_other_failure_refused (heap : TargetHeapSemantics Nat) :
    ¬ TargetFunctionBody representation.interface heap noServices function
      [.reference (some address)] (state 3) ⟨.unit, state 0⟩ := by
  intro ran
  have read := (invocation_observation heap noServices (state 3) address 3 (loaded 3) _ ran).2.2.2.2.2
  have words : (0 : BitVec 64) = 3 := TargetValue.word.inj (Option.some.inj read)
  have numbers := congrArg BitVec.toNat words
  contradiction

theorem resetting_external_world_refused (heap : TargetHeapSemantics Nat) :
    ¬ TargetFunctionBody representation.interface heap noServices function
      [.reference (some address)] (state 2) ⟨.unit, { state 0 with external := 0 }⟩ := by
  intro ran
  have same := (invocation_observation heap noServices (state 2) address 2 (loaded 2) _ ran).2.1
  contradiction

end Controls


end AcceptedProgress

/-! Readiness of the actual const-frame helper is compared with a separate
local-progress contract. Unsigned cursors retain their 64-bit width; case groups
retain the one authored body and its fall-through labels. This is a typed,
immutable header-reading fragment, separate from queue ownership, graph scans,
physical storage and the complete native controller relation. -/
namespace FrameReadiness
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

private def text0 : List Char := "static bool prime_native_control_frame_ready(const PrimeEvalStackFrame *frame) {\n".toList
private def tokens0 : List Token := [.identifier "static".toList, .identifier "bool".toList, .identifier "prime_native_control_frame_ready".toList, .punctuation "(".toList, .identifier "const".toList, .identifier "PrimeEvalStackFrame".toList, .punctuation "*".toList, .identifier "frame".toList, .punctuation ")".toList, .punctuation "{".toList]
private theorem scanned0 : text0.foldl step initial = completed tokens0 := by decide +kernel

private def text1 : List Char := "    if (!frame || frame->control_closed || frame->weight_ownership_parked)\n".toList
private def tokens1 : List Token := [.identifier "if".toList, .punctuation "(".toList, .punctuation "!".toList, .identifier "frame".toList, .punctuation "||".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "control_closed".toList, .punctuation "||".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "weight_ownership_parked".toList, .punctuation ")".toList]
private theorem scanned1 : text1.foldl step initial = completed tokens1 := by decide +kernel

private def text2 : List Char := "        return false;\n".toList
private def tokens2 : List Token := [.identifier "return".toList, .identifier "false".toList, .punctuation ";".toList]
private theorem scanned2 : text2.foldl step initial = completed tokens2 := by decide +kernel

private def text3 : List Char := "    if (frame->kind == PRIME_EVAL_STACK_FRAME_WEIGHT_ADMIT && frame->weight_index)\n".toList
private def tokens3 : List Token := [.identifier "if".toList, .punctuation "(".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "kind".toList, .punctuation "==".toList, .identifier "PRIME_EVAL_STACK_FRAME_WEIGHT_ADMIT".toList, .punctuation "&&".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "weight_index".toList, .punctuation ")".toList]
private theorem scanned3 : text3.foldl step initial = completed tokens3 := by decide +kernel

private def text4 : List Char := "        return false;\n".toList
private def tokens4 : List Token := [.identifier "return".toList, .identifier "false".toList, .punctuation ";".toList]
private theorem scanned4 : text4.foldl step initial = completed tokens4 := by decide +kernel

private def text5 : List Char := "    if (frame->kind == PRIME_EVAL_STACK_FRAME_CONTROL_NESTED && frame->control_nested_parked)\n".toList
private def tokens5 : List Token := [.identifier "if".toList, .punctuation "(".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "kind".toList, .punctuation "==".toList, .identifier "PRIME_EVAL_STACK_FRAME_CONTROL_NESTED".toList, .punctuation "&&".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "control_nested_parked".toList, .punctuation ")".toList]
private theorem scanned5 : text5.foldl step initial = completed tokens5 := by decide +kernel

private def text6 : List Char := "        return false;\n".toList
private def tokens6 : List Token := [.identifier "return".toList, .identifier "false".toList, .punctuation ";".toList]
private theorem scanned6 : text6.foldl step initial = completed tokens6 := by decide +kernel

private def text7 : List Char := "    if (frame->kind == PRIME_EVAL_STACK_FRAME_MATCH_ROWS)\n".toList
private def tokens7 : List Token := [.identifier "if".toList, .punctuation "(".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "kind".toList, .punctuation "==".toList, .identifier "PRIME_EVAL_STACK_FRAME_MATCH_ROWS".toList, .punctuation ")".toList]
private theorem scanned7 : text7.foldl step initial = completed tokens7 := by decide +kernel

private def text8 : List Char := "        return frame->match_rows && !frame->match_rows->blocked;\n".toList
private def tokens8 : List Token := [.identifier "return".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "match_rows".toList, .punctuation "&&".toList, .punctuation "!".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "match_rows".toList, .punctuation "->".toList, .identifier "blocked".toList, .punctuation ";".toList]
private theorem scanned8 : text8.foldl step initial = completed tokens8 := by decide +kernel

private def text9 : List Char := "    if (frame->kind == PRIME_EVAL_STACK_FRAME_ALTERNATIVES)\n".toList
private def tokens9 : List Token := [.identifier "if".toList, .punctuation "(".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "kind".toList, .punctuation "==".toList, .identifier "PRIME_EVAL_STACK_FRAME_ALTERNATIVES".toList, .punctuation ")".toList]
private theorem scanned9 : text9.foldl step initial = completed tokens9 := by decide +kernel

private def text10 : List Char := "        return true;\n".toList
private def tokens10 : List Token := [.identifier "return".toList, .identifier "true".toList, .punctuation ";".toList]
private theorem scanned10 : text10.foldl step initial = completed tokens10 := by decide +kernel

private def text11 : List Char := "    if (frame->control_pending == 0u)\n".toList
private def tokens11 : List Token := [.identifier "if".toList, .punctuation "(".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "control_pending".toList, .punctuation "==".toList, .number "0u".toList, .punctuation ")".toList]
private theorem scanned11 : text11.foldl step initial = completed tokens11 := by decide +kernel

private def text12 : List Char := "        return true;\n".toList
private def tokens12 : List Token := [.identifier "return".toList, .identifier "true".toList, .punctuation ";".toList]
private theorem scanned12 : text12.foldl step initial = completed tokens12 := by decide +kernel

private def text13 : List Char := "    switch (frame->kind) {\n".toList
private def tokens13 : List Token := [.identifier "switch".toList, .punctuation "(".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "kind".toList, .punctuation ")".toList, .punctuation "{".toList]
private theorem scanned13 : text13.foldl step initial = completed tokens13 := by decide +kernel

private def text14 : List Char := "    case PRIME_EVAL_STACK_FRAME_EQUATION_SEARCH:\n".toList
private def tokens14 : List Token := [.identifier "case".toList, .identifier "PRIME_EVAL_STACK_FRAME_EQUATION_SEARCH".toList, .punctuation ":".toList]
private theorem scanned14 : text14.foldl step initial = completed tokens14 := by decide +kernel

private def text15 : List Char := "        return frame->equation_search &&\n".toList
private def tokens15 : List Token := [.identifier "return".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "equation_search".toList, .punctuation "&&".toList]
private theorem scanned15 : text15.foldl step initial = completed tokens15 := by decide +kernel

private def text16 : List Char := "            (frame->equation_search->state == PRIME_NEED_EQUATION_SEARCH_BUILD_PUBLICATION ||\n".toList
private def tokens16 : List Token := [.punctuation "(".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "equation_search".toList, .punctuation "->".toList, .identifier "state".toList, .punctuation "==".toList, .identifier "PRIME_NEED_EQUATION_SEARCH_BUILD_PUBLICATION".toList, .punctuation "||".toList]
private theorem scanned16 : text16.foldl step initial = completed tokens16 := by decide +kernel

private def text17 : List Char := "             (frame->control_force_stream &&\n".toList
private def tokens17 : List Token := [.punctuation "(".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "control_force_stream".toList, .punctuation "&&".toList]
private theorem scanned17 : text17.foldl step initial = completed tokens17 := by decide +kernel

private def text18 : List Char := "              frame->equation_search->state == PRIME_NEED_EQUATION_SEARCH_WAIT_FORCE &&\n".toList
private def tokens18 : List Token := [.identifier "frame".toList, .punctuation "->".toList, .identifier "equation_search".toList, .punctuation "->".toList, .identifier "state".toList, .punctuation "==".toList, .identifier "PRIME_NEED_EQUATION_SEARCH_WAIT_FORCE".toList, .punctuation "&&".toList]
private theorem scanned18 : text18.foldl step initial = completed tokens18 := by decide +kernel

private def text19 : List Char := "              frame->index < frame->child.len));\n".toList
private def tokens19 : List Token := [.identifier "frame".toList, .punctuation "->".toList, .identifier "index".toList, .punctuation "<".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "child".toList, .punctuation ".".toList, .identifier "len".toList, .punctuation ")".toList, .punctuation ")".toList, .punctuation ";".toList]
private theorem scanned19 : text19.foldl step initial = completed tokens19 := by decide +kernel

private def text20 : List Char := "    case PRIME_EVAL_STACK_FRAME_FORCE:\n".toList
private def tokens20 : List Token := [.identifier "case".toList, .identifier "PRIME_EVAL_STACK_FRAME_FORCE".toList, .punctuation ":".toList]
private theorem scanned20 : text20.foldl step initial = completed tokens20 := by decide +kernel

private def text21 : List Char := "    case PRIME_EVAL_STACK_FRAME_WEIGHT_EXACT_RATIONAL:\n".toList
private def tokens21 : List Token := [.identifier "case".toList, .identifier "PRIME_EVAL_STACK_FRAME_WEIGHT_EXACT_RATIONAL".toList, .punctuation ":".toList]
private theorem scanned21 : text21.foldl step initial = completed tokens21 := by decide +kernel

private def text22 : List Char := "    case PRIME_EVAL_STACK_FRAME_WEIGHT_WHERE:\n".toList
private def tokens22 : List Token := [.identifier "case".toList, .identifier "PRIME_EVAL_STACK_FRAME_WEIGHT_WHERE".toList, .punctuation ":".toList]
private theorem scanned22 : text22.foldl step initial = completed tokens22 := by decide +kernel

private def text23 : List Char := "    case PRIME_EVAL_STACK_FRAME_WEIGHT_ADMIT:\n".toList
private def tokens23 : List Token := [.identifier "case".toList, .identifier "PRIME_EVAL_STACK_FRAME_WEIGHT_ADMIT".toList, .punctuation ":".toList]
private theorem scanned23 : text23.foldl step initial = completed tokens23 := by decide +kernel

private def text24 : List Char := "    case PRIME_EVAL_STACK_FRAME_WEIGHT_ALGEBRA:\n".toList
private def tokens24 : List Token := [.identifier "case".toList, .identifier "PRIME_EVAL_STACK_FRAME_WEIGHT_ALGEBRA".toList, .punctuation ":".toList]
private theorem scanned24 : text24.foldl step initial = completed tokens24 := by decide +kernel

private def text25 : List Char := "    case PRIME_EVAL_STACK_FRAME_WEIGHT_READ:\n".toList
private def tokens25 : List Token := [.identifier "case".toList, .identifier "PRIME_EVAL_STACK_FRAME_WEIGHT_READ".toList, .punctuation ":".toList]
private theorem scanned25 : text25.foldl step initial = completed tokens25 := by decide +kernel

private def text26 : List Char := "    case PRIME_EVAL_STACK_FRAME_WEIGHT_FOLD:\n".toList
private def tokens26 : List Token := [.identifier "case".toList, .identifier "PRIME_EVAL_STACK_FRAME_WEIGHT_FOLD".toList, .punctuation ":".toList]
private theorem scanned26 : text26.foldl step initial = completed tokens26 := by decide +kernel

private def text27 : List Char := "    case PRIME_EVAL_STACK_FRAME_DIALECT_SOURCE:\n".toList
private def tokens27 : List Token := [.identifier "case".toList, .identifier "PRIME_EVAL_STACK_FRAME_DIALECT_SOURCE".toList, .punctuation ":".toList]
private theorem scanned27 : text27.foldl step initial = completed tokens27 := by decide +kernel

private def text28 : List Char := "        return frame->index < frame->child.len;\n".toList
private def tokens28 : List Token := [.identifier "return".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "index".toList, .punctuation "<".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "child".toList, .punctuation ".".toList, .identifier "len".toList, .punctuation ";".toList]
private theorem scanned28 : text28.foldl step initial = completed tokens28 := by decide +kernel

private def text29 : List Char := "    case PRIME_EVAL_STACK_FRAME_BIND_FINISH:\n".toList
private def tokens29 : List Token := [.identifier "case".toList, .identifier "PRIME_EVAL_STACK_FRAME_BIND_FINISH".toList, .punctuation ":".toList]
private theorem scanned29 : text29.foldl step initial = completed tokens29 := by decide +kernel

private def text30 : List Char := "        return frame->stream_forwarded < frame->child.len;\n".toList
private def tokens30 : List Token := [.identifier "return".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "stream_forwarded".toList, .punctuation "<".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "child".toList, .punctuation ".".toList, .identifier "len".toList, .punctuation ";".toList]
private theorem scanned30 : text30.foldl step initial = completed tokens30 := by decide +kernel

private def text31 : List Char := "    case PRIME_EVAL_STACK_FRAME_NORMALIZE_ATOM:\n".toList
private def tokens31 : List Token := [.identifier "case".toList, .identifier "PRIME_EVAL_STACK_FRAME_NORMALIZE_ATOM".toList, .punctuation ":".toList]
private theorem scanned31 : text31.foldl step initial = completed tokens31 := by decide +kernel

private def text32 : List Char := "    case PRIME_EVAL_STACK_FRAME_NORMALIZE_CHILDREN:\n".toList
private def tokens32 : List Token := [.identifier "case".toList, .identifier "PRIME_EVAL_STACK_FRAME_NORMALIZE_CHILDREN".toList, .punctuation ":".toList]
private theorem scanned32 : text32.foldl step initial = completed tokens32 := by decide +kernel

private def text33 : List Char := "        return frame->state == PRIME_EVAL_STACK_FRAME_WAIT_CALL &&\n".toList
private def tokens33 : List Token := [.identifier "return".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "state".toList, .punctuation "==".toList, .identifier "PRIME_EVAL_STACK_FRAME_WAIT_CALL".toList, .punctuation "&&".toList]
private theorem scanned33 : text33.foldl step initial = completed tokens33 := by decide +kernel

private def text34 : List Char := "            frame->index < frame->child.len;\n".toList
private def tokens34 : List Token := [.identifier "frame".toList, .punctuation "->".toList, .identifier "index".toList, .punctuation "<".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "child".toList, .punctuation ".".toList, .identifier "len".toList, .punctuation ";".toList]
private theorem scanned34 : text34.foldl step initial = completed tokens34 := by decide +kernel

private def text35 : List Char := "    case PRIME_EVAL_STACK_FRAME_LET:\n".toList
private def tokens35 : List Token := [.identifier "case".toList, .identifier "PRIME_EVAL_STACK_FRAME_LET".toList, .punctuation ":".toList]
private theorem scanned35 : text35.foldl step initial = completed tokens35 := by decide +kernel

private def text36 : List Char := "    case PRIME_EVAL_STACK_FRAME_STRICT:\n".toList
private def tokens36 : List Token := [.identifier "case".toList, .identifier "PRIME_EVAL_STACK_FRAME_STRICT".toList, .punctuation ":".toList]
private theorem scanned36 : text36.foldl step initial = completed tokens36 := by decide +kernel

private def text37 : List Char := "        return (frame->state == PRIME_EVAL_STACK_FRAME_DEMAND ||\n".toList
private def tokens37 : List Token := [.identifier "return".toList, .punctuation "(".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "state".toList, .punctuation "==".toList, .identifier "PRIME_EVAL_STACK_FRAME_DEMAND".toList, .punctuation "||".toList]
private theorem scanned37 : text37.foldl step initial = completed tokens37 := by decide +kernel

private def text38 : List Char := "                frame->state == PRIME_EVAL_STACK_FRAME_WAIT_BRANCH ||\n".toList
private def tokens38 : List Token := [.identifier "frame".toList, .punctuation "->".toList, .identifier "state".toList, .punctuation "==".toList, .identifier "PRIME_EVAL_STACK_FRAME_WAIT_BRANCH".toList, .punctuation "||".toList]
private theorem scanned38 : text38.foldl step initial = completed tokens38 := by decide +kernel

private def text39 : List Char := "                frame->state == PRIME_EVAL_STACK_FRAME_ITERATE) &&\n".toList
private def tokens39 : List Token := [.identifier "frame".toList, .punctuation "->".toList, .identifier "state".toList, .punctuation "==".toList, .identifier "PRIME_EVAL_STACK_FRAME_ITERATE".toList, .punctuation ")".toList, .punctuation "&&".toList]
private theorem scanned39 : text39.foldl step initial = completed tokens39 := by decide +kernel

private def text40 : List Char := "            frame->index < frame->child.len;\n".toList
private def tokens40 : List Token := [.identifier "frame".toList, .punctuation "->".toList, .identifier "index".toList, .punctuation "<".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "child".toList, .punctuation ".".toList, .identifier "len".toList, .punctuation ";".toList]
private theorem scanned40 : text40.foldl step initial = completed tokens40 := by decide +kernel

private def text41 : List Char := "    default:\n".toList
private def tokens41 : List Token := [.identifier "default".toList, .punctuation ":".toList]
private theorem scanned41 : text41.foldl step initial = completed tokens41 := by decide +kernel

private def text42 : List Char := "        return false;\n".toList
private def tokens42 : List Token := [.identifier "return".toList, .identifier "false".toList, .punctuation ";".toList]
private theorem scanned42 : text42.foldl step initial = completed tokens42 := by decide +kernel

private def text43 : List Char := "    }\n".toList
private def tokens43 : List Token := [.punctuation "}".toList]
private theorem scanned43 : text43.foldl step initial = completed tokens43 := by decide +kernel

private def text44 : List Char := "}\n".toList
private def tokens44 : List Token := [.punctuation "}".toList]
private theorem scanned44 : text44.foldl step initial = completed tokens44 := by decide +kernel

private def pieces : List (List Char × List Token) := [(text0, tokens0), (text1, tokens1), (text2, tokens2), (text3, tokens3), (text4, tokens4), (text5, tokens5), (text6, tokens6), (text7, tokens7), (text8, tokens8), (text9, tokens9), (text10, tokens10), (text11, tokens11), (text12, tokens12), (text13, tokens13), (text14, tokens14), (text15, tokens15), (text16, tokens16), (text17, tokens17), (text18, tokens18), (text19, tokens19), (text20, tokens20), (text21, tokens21), (text22, tokens22), (text23, tokens23), (text24, tokens24), (text25, tokens25), (text26, tokens26), (text27, tokens27), (text28, tokens28), (text29, tokens29), (text30, tokens30), (text31, tokens31), (text32, tokens32), (text33, tokens33), (text34, tokens34), (text35, tokens35), (text36, tokens36), (text37, tokens37), (text38, tokens38), (text39, tokens39), (text40, tokens40), (text41, tokens41), (text42, tokens42), (text43, tokens43), (text44, tokens44)]
def source : List Char := pieces.flatMap Prod.fst
private def tokens : List Token := pieces.flatMap Prod.snd

private theorem scanned : List.Forall (fun piece =>
    piece.1.foldl step initial = completed piece.2) pieces := by
  exact ⟨scanned0, ⟨scanned1, ⟨scanned2, ⟨scanned3, ⟨scanned4, ⟨scanned5, ⟨scanned6, ⟨scanned7, ⟨scanned8, ⟨scanned9, ⟨scanned10, ⟨scanned11, ⟨scanned12, ⟨scanned13, ⟨scanned14, ⟨scanned15, ⟨scanned16, ⟨scanned17, ⟨scanned18, ⟨scanned19, ⟨scanned20, ⟨scanned21, ⟨scanned22, ⟨scanned23, ⟨scanned24, ⟨scanned25, ⟨scanned26, ⟨scanned27, ⟨scanned28, ⟨scanned29, ⟨scanned30, ⟨scanned31, ⟨scanned32, ⟨scanned33, ⟨scanned34, ⟨scanned35, ⟨scanned36, ⟨scanned37, ⟨scanned38, ⟨scanned39, ⟨scanned40, ⟨scanned41, ⟨scanned42, ⟨scanned43, scanned44⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

private theorem lexed : lex source = .ok tokens :=
  lex_of_completed source tokens (completed_pieces pieces scanned)

def types : TypeNames := ["bool".toList, "PrimeEvalStackFrame".toList]

private def f : CExpr := .identifier "frame".toList
private def field (name : String) : CExpr := .field f name.toList true
private def tag (name : String) : CExpr := .identifier ("PRIME_EVAL_STACK_FRAME_" ++ name).toList
private def kind (name : String) : CExpr := .binary .eq (field "kind") (tag name)
private def phase (name : String) : CExpr := .binary .eq (field "state") (tag name)
private def length : CExpr := .field (field "child") "len".toList false
private def unread : CExpr := .binary .lt (field "index") length
private def reply (value : CExpr) : List CStatement := [.return (some value)]

private def equation : CExpr :=
  .binary .and (field "equation_search")
    (.binary .or
      (.binary .eq (.field (field "equation_search") "state".toList true)
        (.identifier "PRIME_NEED_EQUATION_SEARCH_BUILD_PUBLICATION".toList))
      (.binary .and (.binary .and (field "control_force_stream")
        (.binary .eq (.field (field "equation_search") "state".toList true)
          (.identifier "PRIME_NEED_EQUATION_SEARCH_WAIT_FORCE".toList))) unread))

private def arms : List (CExpr × List CStatement) := [
    (tag "EQUATION_SEARCH", reply equation),
    (tag "FORCE", []),
    (tag "WEIGHT_EXACT_RATIONAL", []),
    (tag "WEIGHT_WHERE", []),
    (tag "WEIGHT_ADMIT", []),
    (tag "WEIGHT_ALGEBRA", []),
    (tag "WEIGHT_READ", []),
    (tag "WEIGHT_FOLD", []),
    (tag "DIALECT_SOURCE", reply unread),
    (tag "BIND_FINISH", reply (.binary .lt (field "stream_forwarded") length)),
    (tag "NORMALIZE_ATOM", []),
    (tag "NORMALIZE_CHILDREN", reply (.binary .and (phase "WAIT_CALL") unread)),
    (tag "LET", []),
    (tag "STRICT", reply (.binary .and
      (.binary .or (.binary .or (phase "DEMAND") (phase "WAIT_BRANCH")) (phase "ITERATE")) unread))]

def body : List CStatement := [
  .branch (.binary .or (.binary .or (.unary .not f) (field "control_closed"))
    (field "weight_ownership_parked")) (reply (.bool false)) [],
  .branch (.binary .and (kind "WEIGHT_ADMIT") (field "weight_index")) (reply (.bool false)) [],
  .branch (.binary .and (kind "CONTROL_NESTED") (field "control_nested_parked"))
    (reply (.bool false)) [],
  .branch (kind "MATCH_ROWS") (reply (.binary .and (field "match_rows")
    (.unary .not (.field (field "match_rows") "blocked".toList true)))) [],
  .branch (kind "ALTERNATIVES") (reply (.bool true)) [],
  .branch (.binary .eq (field "control_pending") (.unsignedInteger 0)) (reply (.bool true)) [],
  .switch (field "kind") arms (reply (.bool false))]

def parsed : CQualifiedFunction :=
  ⟨⟨"bool".toList, 0⟩, "prime_native_control_frame_ready".toList,
    [⟨⟨⟨"PrimeEvalStackFrame".toList, 1⟩, "frame".toList⟩, true⟩], body⟩

private theorem token_count : tokens.length = 263 := by decide +kernel

private theorem parsed_exact : qualifiedFunction?
    (2 * tokens.length + 4) types (ordinaryFunctionTokens tokens) = some (parsed, []) := by
  rw [token_count]
  rfl

theorem source_recognized : qualifiedFunctionText? types source = some parsed :=
  function_text_using_of_parts (qualifiedParameter? types) types source tokens parsed lexed parsed_exact


namespace ReadView
open ScalarRead

inductive Role where
  | bindFinish
  | strict
  | conditional
  | letBody
  | equationSearch
  | force
  | normalizeAtom
  | normalizeChildren
  | streamResume
  | score
  | goal
  | cost
  | nested
  | exactRational
  | whereWeight
  | admit
  | algebra
  | read
  | fold
  | dialect
  | matchRows
  | alternatives
  deriving DecidableEq, Repr

def Role.code : Role → UInt32
  | .bindFinish => 0
  | .strict => 1
  | .conditional => 2
  | .letBody => 3
  | .equationSearch => 4
  | .force => 5
  | .normalizeAtom => 6
  | .normalizeChildren => 7
  | .streamResume => 8
  | .score => 9
  | .goal => 10
  | .cost => 11
  | .nested => 12
  | .exactRational => 13
  | .whereWeight => 14
  | .admit => 15
  | .algebra => 16
  | .read => 17
  | .fold => 18
  | .dialect => 19
  | .matchRows => 20
  | .alternatives => 21

structure Frame where
  role : Role
  phase : UInt32
  closed : Bool
  ownershipParked : Bool
  weightIndex : UInt64
  nestedParked : Bool
  pending : UInt64
  cursor : UInt64
  forwarded : UInt64
  childLength : UInt64
  rowsBlocked : Option Bool
  equationPhase : Option UInt32
  forceStream : Bool

def waiting (frame : Frame) : Bool :=
  let unread := decide (frame.cursor < frame.childLength)
  match frame.role with
  | .equationSearch => frame.equationPhase.any fun phase =>
      phase == 2 || (frame.forceStream && phase == 1 && unread)
  | .force | .exactRational | .whereWeight | .admit | .algebra | .read | .fold | .dialect => unread
  | .bindFinish => decide (frame.forwarded < frame.childLength)
  | .normalizeAtom | .normalizeChildren => frame.phase == 1 && unread
  | .letBody | .strict => (frame.phase == 0 || frame.phase == 2 || frame.phase == 3) && unread
  | _ => false

/-- Readiness is permission to make local progress. A row consumer's missing
or blocked cursor stays unavailable even when it has no producer obligations. -/
def ready : Option Frame → Bool
  | none => false
  | some frame =>
      if frame.closed || frame.ownershipParked then false
      else if frame.role == .admit && frame.weightIndex != 0 then false
      else if frame.role == .nested && frame.nestedParked then false
      else match frame.role with
        | .matchRows => frame.rowsBlocked.any (! ·)
        | .alternatives => true
        | _ => frame.pending == 0 || waiting frame

inductive Address where
  | frame | rows | equation
  deriving DecidableEq, Repr

def macroValue (name : Name) : Option (Value Address) :=
  if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'B', 'I', 'N', 'D', '_', 'F', 'I', 'N', 'I', 'S', 'H'] then some (.unsigned 0)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'S', 'T', 'R', 'I', 'C', 'T'] then some (.unsigned 1)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'I', 'F'] then some (.unsigned 2)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'L', 'E', 'T'] then some (.unsigned 3)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'E', 'Q', 'U', 'A', 'T', 'I', 'O', 'N', '_', 'S', 'E', 'A', 'R', 'C', 'H'] then some (.unsigned 4)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'F', 'O', 'R', 'C', 'E'] then some (.unsigned 5)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'N', 'O', 'R', 'M', 'A', 'L', 'I', 'Z', 'E', '_', 'A', 'T', 'O', 'M'] then some (.unsigned 6)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'N', 'O', 'R', 'M', 'A', 'L', 'I', 'Z', 'E', '_', 'C', 'H', 'I', 'L', 'D', 'R', 'E', 'N'] then some (.unsigned 7)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'S', 'T', 'R', 'E', 'A', 'M', '_', 'R', 'E', 'S', 'U', 'M', 'E'] then some (.unsigned 8)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'C', 'O', 'N', 'T', 'R', 'O', 'L', '_', 'S', 'C', 'O', 'R', 'E'] then some (.unsigned 9)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'C', 'O', 'N', 'T', 'R', 'O', 'L', '_', 'G', 'O', 'A', 'L'] then some (.unsigned 10)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'C', 'O', 'N', 'T', 'R', 'O', 'L', '_', 'C', 'O', 'S', 'T'] then some (.unsigned 11)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'C', 'O', 'N', 'T', 'R', 'O', 'L', '_', 'N', 'E', 'S', 'T', 'E', 'D'] then some (.unsigned 12)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'W', 'E', 'I', 'G', 'H', 'T', '_', 'E', 'X', 'A', 'C', 'T', '_', 'R', 'A', 'T', 'I', 'O', 'N', 'A', 'L'] then some (.unsigned 13)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'W', 'E', 'I', 'G', 'H', 'T', '_', 'W', 'H', 'E', 'R', 'E'] then some (.unsigned 14)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'W', 'E', 'I', 'G', 'H', 'T', '_', 'A', 'D', 'M', 'I', 'T'] then some (.unsigned 15)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'W', 'E', 'I', 'G', 'H', 'T', '_', 'A', 'L', 'G', 'E', 'B', 'R', 'A'] then some (.unsigned 16)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'W', 'E', 'I', 'G', 'H', 'T', '_', 'R', 'E', 'A', 'D'] then some (.unsigned 17)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'W', 'E', 'I', 'G', 'H', 'T', '_', 'F', 'O', 'L', 'D'] then some (.unsigned 18)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'D', 'I', 'A', 'L', 'E', 'C', 'T', '_', 'S', 'O', 'U', 'R', 'C', 'E'] then some (.unsigned 19)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'M', 'A', 'T', 'C', 'H', '_', 'R', 'O', 'W', 'S'] then some (.unsigned 20)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'A', 'L', 'T', 'E', 'R', 'N', 'A', 'T', 'I', 'V', 'E', 'S'] then some (.unsigned 21)

  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'D', 'E', 'M', 'A', 'N', 'D'] then some (.unsigned 0)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'W', 'A', 'I', 'T', '_', 'C', 'A', 'L', 'L'] then some (.unsigned 1)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'W', 'A', 'I', 'T', '_', 'B', 'R', 'A', 'N', 'C', 'H'] then some (.unsigned 2)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'I', 'T', 'E', 'R', 'A', 'T', 'E'] then some (.unsigned 3)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'N', 'E', 'E', 'D', '_', 'E', 'Q', 'U', 'A', 'T', 'I', 'O', 'N', '_', 'S', 'E', 'A', 'R', 'C', 'H', '_', 'B', 'U', 'I', 'L', 'D', '_', 'P', 'U', 'B', 'L', 'I', 'C', 'A', 'T', 'I', 'O', 'N'] then some (.unsigned 2)
  else if name = ['P', 'R', 'I', 'M', 'E', '_', 'N', 'E', 'E', 'D', '_', 'E', 'Q', 'U', 'A', 'T', 'I', 'O', 'N', '_', 'S', 'E', 'A', 'R', 'C', 'H', '_', 'W', 'A', 'I', 'T', '_', 'F', 'O', 'R', 'C', 'E'] then some (.unsigned 1)
  else none

def environment (view : Option Frame) : Environment Address := fun name =>
  if name = ['f', 'r', 'a', 'm', 'e'] then some (.identity (view.map fun _ => .frame))
  else macroValue name

def fields (view : Option Frame) : FieldReader Address := fun address name => do
  let frame ← view
  match address with
  | .frame =>
      if name = ['k', 'i', 'n', 'd'] then some (.unsigned frame.role.code)
      else if name = ['s', 't', 'a', 't', 'e'] then some (.unsigned frame.phase)
      else if name = ['c', 'o', 'n', 't', 'r', 'o', 'l', '_', 'c', 'l', 'o', 's', 'e', 'd'] then some (.boolean frame.closed)
      else if name = ['w', 'e', 'i', 'g', 'h', 't', '_', 'o', 'w', 'n', 'e', 'r', 's', 'h', 'i', 'p', '_', 'p', 'a', 'r', 'k', 'e', 'd'] then some (.boolean frame.ownershipParked)
      else if name = ['w', 'e', 'i', 'g', 'h', 't', '_', 'i', 'n', 'd', 'e', 'x'] then some (.unsigned64 frame.weightIndex)
      else if name = ['c', 'o', 'n', 't', 'r', 'o', 'l', '_', 'n', 'e', 's', 't', 'e', 'd', '_', 'p', 'a', 'r', 'k', 'e', 'd'] then some (.boolean frame.nestedParked)
      else if name = ['m', 'a', 't', 'c', 'h', '_', 'r', 'o', 'w', 's'] then some (.identity (frame.rowsBlocked.map fun _ => .rows))
      else if name = ['e', 'q', 'u', 'a', 't', 'i', 'o', 'n', '_', 's', 'e', 'a', 'r', 'c', 'h'] then some (.identity (frame.equationPhase.map fun _ => .equation))
      else if name = ['c', 'o', 'n', 't', 'r', 'o', 'l', '_', 'p', 'e', 'n', 'd', 'i', 'n', 'g'] then some (.unsigned64 frame.pending)
      else if name = ['c', 'o', 'n', 't', 'r', 'o', 'l', '_', 'f', 'o', 'r', 'c', 'e', '_', 's', 't', 'r', 'e', 'a', 'm'] then some (.boolean frame.forceStream)
      else if name = ['i', 'n', 'd', 'e', 'x'] then some (.unsigned64 frame.cursor)
      else if name = ['s', 't', 'r', 'e', 'a', 'm', '_', 'f', 'o', 'r', 'w', 'a', 'r', 'd', 'e', 'd'] then some (.unsigned64 frame.forwarded)
      else if name = ['c', 'h', 'i', 'l', 'd'] then some (.wordRecord [(['l', 'e', 'n'], frame.childLength)])
      else none
  | .rows => if name = ['b', 'l', 'o', 'c', 'k', 'e', 'd'] then frame.rowsBlocked.map Value.boolean else none
  | .equation => if name = ['s', 't', 'a', 't', 'e'] then frame.equationPhase.map Value.unsigned else none

def returned (view : Option Frame) (answer : Bool) : LocalBlock.Result Address :=
  .finished (some (.returned (environment view) (some (.boolean answer))))

theorem null_frame_returns_false :
    LocalBlock.execute (fields none) 32 (environment none) body = returned none false := rfl


@[simp] private theorem environment_frame (view : Option Frame) :
    environment view ['f', 'r', 'a', 'm', 'e'] = some (.identity (view.map fun _ => .frame)) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_BIND_FINISH (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'B', 'I', 'N', 'D', '_', 'F', 'I', 'N', 'I', 'S', 'H'] = some (.unsigned 0) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_STRICT (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'S', 'T', 'R', 'I', 'C', 'T'] = some (.unsigned 1) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_IF (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'I', 'F'] = some (.unsigned 2) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_LET (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'L', 'E', 'T'] = some (.unsigned 3) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_EQUATION_SEARCH (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'E', 'Q', 'U', 'A', 'T', 'I', 'O', 'N', '_', 'S', 'E', 'A', 'R', 'C', 'H'] = some (.unsigned 4) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_FORCE (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'F', 'O', 'R', 'C', 'E'] = some (.unsigned 5) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_NORMALIZE_ATOM (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'N', 'O', 'R', 'M', 'A', 'L', 'I', 'Z', 'E', '_', 'A', 'T', 'O', 'M'] = some (.unsigned 6) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_NORMALIZE_CHILDREN (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'N', 'O', 'R', 'M', 'A', 'L', 'I', 'Z', 'E', '_', 'C', 'H', 'I', 'L', 'D', 'R', 'E', 'N'] = some (.unsigned 7) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_STREAM_RESUME (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'S', 'T', 'R', 'E', 'A', 'M', '_', 'R', 'E', 'S', 'U', 'M', 'E'] = some (.unsigned 8) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_CONTROL_SCORE (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'C', 'O', 'N', 'T', 'R', 'O', 'L', '_', 'S', 'C', 'O', 'R', 'E'] = some (.unsigned 9) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_CONTROL_GOAL (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'C', 'O', 'N', 'T', 'R', 'O', 'L', '_', 'G', 'O', 'A', 'L'] = some (.unsigned 10) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_CONTROL_COST (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'C', 'O', 'N', 'T', 'R', 'O', 'L', '_', 'C', 'O', 'S', 'T'] = some (.unsigned 11) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_CONTROL_NESTED (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'C', 'O', 'N', 'T', 'R', 'O', 'L', '_', 'N', 'E', 'S', 'T', 'E', 'D'] = some (.unsigned 12) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_WEIGHT_EXACT_RATIONAL (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'W', 'E', 'I', 'G', 'H', 'T', '_', 'E', 'X', 'A', 'C', 'T', '_', 'R', 'A', 'T', 'I', 'O', 'N', 'A', 'L'] = some (.unsigned 13) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_WEIGHT_WHERE (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'W', 'E', 'I', 'G', 'H', 'T', '_', 'W', 'H', 'E', 'R', 'E'] = some (.unsigned 14) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_WEIGHT_ADMIT (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'W', 'E', 'I', 'G', 'H', 'T', '_', 'A', 'D', 'M', 'I', 'T'] = some (.unsigned 15) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_WEIGHT_ALGEBRA (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'W', 'E', 'I', 'G', 'H', 'T', '_', 'A', 'L', 'G', 'E', 'B', 'R', 'A'] = some (.unsigned 16) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_WEIGHT_READ (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'W', 'E', 'I', 'G', 'H', 'T', '_', 'R', 'E', 'A', 'D'] = some (.unsigned 17) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_WEIGHT_FOLD (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'W', 'E', 'I', 'G', 'H', 'T', '_', 'F', 'O', 'L', 'D'] = some (.unsigned 18) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_DIALECT_SOURCE (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'D', 'I', 'A', 'L', 'E', 'C', 'T', '_', 'S', 'O', 'U', 'R', 'C', 'E'] = some (.unsigned 19) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_MATCH_ROWS (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'M', 'A', 'T', 'C', 'H', '_', 'R', 'O', 'W', 'S'] = some (.unsigned 20) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_ALTERNATIVES (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'A', 'L', 'T', 'E', 'R', 'N', 'A', 'T', 'I', 'V', 'E', 'S'] = some (.unsigned 21) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_DEMAND (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'D', 'E', 'M', 'A', 'N', 'D'] = some (.unsigned 0) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_WAIT_CALL (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'W', 'A', 'I', 'T', '_', 'C', 'A', 'L', 'L'] = some (.unsigned 1) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_WAIT_BRANCH (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'W', 'A', 'I', 'T', '_', 'B', 'R', 'A', 'N', 'C', 'H'] = some (.unsigned 2) := rfl

@[simp] private theorem environment_PRIME_EVAL_STACK_FRAME_ITERATE (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'E', 'V', 'A', 'L', '_', 'S', 'T', 'A', 'C', 'K', '_', 'F', 'R', 'A', 'M', 'E', '_', 'I', 'T', 'E', 'R', 'A', 'T', 'E'] = some (.unsigned 3) := rfl

@[simp] private theorem environment_PRIME_NEED_EQUATION_SEARCH_BUILD_PUBLICATION (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'N', 'E', 'E', 'D', '_', 'E', 'Q', 'U', 'A', 'T', 'I', 'O', 'N', '_', 'S', 'E', 'A', 'R', 'C', 'H', '_', 'B', 'U', 'I', 'L', 'D', '_', 'P', 'U', 'B', 'L', 'I', 'C', 'A', 'T', 'I', 'O', 'N'] = some (.unsigned 2) := rfl

@[simp] private theorem environment_PRIME_NEED_EQUATION_SEARCH_WAIT_FORCE (view : Option Frame) :
    environment view ['P', 'R', 'I', 'M', 'E', '_', 'N', 'E', 'E', 'D', '_', 'E', 'Q', 'U', 'A', 'T', 'I', 'O', 'N', '_', 'S', 'E', 'A', 'R', 'C', 'H', '_', 'W', 'A', 'I', 'T', '_', 'F', 'O', 'R', 'C', 'E'] = some (.unsigned 1) := rfl

@[simp] private theorem fields_kind (frame : Frame) :
    fields (some frame) .frame ['k', 'i', 'n', 'd'] = some (.unsigned frame.role.code) := rfl

@[simp] private theorem fields_state (frame : Frame) :
    fields (some frame) .frame ['s', 't', 'a', 't', 'e'] = some (.unsigned frame.phase) := rfl

@[simp] private theorem fields_control_closed (frame : Frame) :
    fields (some frame) .frame ['c', 'o', 'n', 't', 'r', 'o', 'l', '_', 'c', 'l', 'o', 's', 'e', 'd'] = some (.boolean frame.closed) := rfl

@[simp] private theorem fields_weight_ownership_parked (frame : Frame) :
    fields (some frame) .frame ['w', 'e', 'i', 'g', 'h', 't', '_', 'o', 'w', 'n', 'e', 'r', 's', 'h', 'i', 'p', '_', 'p', 'a', 'r', 'k', 'e', 'd'] = some (.boolean frame.ownershipParked) := rfl

@[simp] private theorem fields_weight_index (frame : Frame) :
    fields (some frame) .frame ['w', 'e', 'i', 'g', 'h', 't', '_', 'i', 'n', 'd', 'e', 'x'] = some (.unsigned64 frame.weightIndex) := rfl

@[simp] private theorem fields_control_nested_parked (frame : Frame) :
    fields (some frame) .frame ['c', 'o', 'n', 't', 'r', 'o', 'l', '_', 'n', 'e', 's', 't', 'e', 'd', '_', 'p', 'a', 'r', 'k', 'e', 'd'] = some (.boolean frame.nestedParked) := rfl

@[simp] private theorem fields_match_rows (frame : Frame) :
    fields (some frame) .frame ['m', 'a', 't', 'c', 'h', '_', 'r', 'o', 'w', 's'] = some (.identity (frame.rowsBlocked.map fun _ => .rows)) := rfl

@[simp] private theorem fields_equation_search (frame : Frame) :
    fields (some frame) .frame ['e', 'q', 'u', 'a', 't', 'i', 'o', 'n', '_', 's', 'e', 'a', 'r', 'c', 'h'] = some (.identity (frame.equationPhase.map fun _ => .equation)) := rfl

@[simp] private theorem fields_control_pending (frame : Frame) :
    fields (some frame) .frame ['c', 'o', 'n', 't', 'r', 'o', 'l', '_', 'p', 'e', 'n', 'd', 'i', 'n', 'g'] = some (.unsigned64 frame.pending) := rfl

@[simp] private theorem fields_control_force_stream (frame : Frame) :
    fields (some frame) .frame ['c', 'o', 'n', 't', 'r', 'o', 'l', '_', 'f', 'o', 'r', 'c', 'e', '_', 's', 't', 'r', 'e', 'a', 'm'] = some (.boolean frame.forceStream) := rfl

@[simp] private theorem fields_index (frame : Frame) :
    fields (some frame) .frame ['i', 'n', 'd', 'e', 'x'] = some (.unsigned64 frame.cursor) := rfl

@[simp] private theorem fields_stream_forwarded (frame : Frame) :
    fields (some frame) .frame ['s', 't', 'r', 'e', 'a', 'm', '_', 'f', 'o', 'r', 'w', 'a', 'r', 'd', 'e', 'd'] = some (.unsigned64 frame.forwarded) := rfl

@[simp] private theorem fields_child (frame : Frame) :
    fields (some frame) .frame ['c', 'h', 'i', 'l', 'd'] = some (.wordRecord [(['l', 'e', 'n'], frame.childLength)]) := rfl

@[simp] private theorem fields_rows (frame : Frame) :
    fields (some frame) .rows ['b', 'l', 'o', 'c', 'k', 'e', 'd'] = frame.rowsBlocked.map Value.boolean := rfl

@[simp] private theorem fields_equation (frame : Frame) :
    fields (some frame) .equation ['s', 't', 'a', 't', 'e'] = frame.equationPhase.map Value.unsigned := rfl

private theorem result_if (view : Option Frame) (selected yes no : Bool) :
    (if selected then returned view yes else returned view no) =
      returned view (if selected then yes else no) := by cases selected <;> rfl


private theorem branch_returns_or_continues (reader : FieldReader Address)
    (locals : Environment Address) (fuel : Nat) (condition : CExpr)
    (selected answer : Bool) (rest : List CStatement)
    (read : (expression locals reader condition).bind truth? = some selected) :
    LocalBlock.execute reader (fuel + 2) locals
      (.branch condition (reply (.bool answer)) [] :: rest) =
      if selected then .finished (some (.returned locals (some (.boolean answer))))
      else LocalBlock.execute reader (fuel + 1) locals rest :=
  LocalBlock.branch_returns_expression reader locals fuel condition (.bool answer)
    selected (.boolean answer) rest read rfl

private theorem role_code_equal (left right : Role) :
    (left.code == right.code) = (left == right) := by
  cases left <;> cases right <;> rfl

private def closedCondition : CExpr :=
  .binary .or (.binary .or (.unary .not f) (field "control_closed"))
    (field "weight_ownership_parked")
private def admitCondition : CExpr := .binary .and (kind "WEIGHT_ADMIT") (field "weight_index")
private def nestedCondition : CExpr := .binary .and (kind "CONTROL_NESTED") (field "control_nested_parked")
private def pendingCondition : CExpr := .binary .eq (field "control_pending") (.unsignedInteger 0)

private theorem closed_read (frame : Frame) :
    (expression (environment (some frame)) (fields (some frame)) closedCondition).bind truth? =
      some (frame.closed || frame.ownershipParked) := by
  cases h : frame.closed <;>
    simp [closedCondition, f, field, expression, truth?, h]

private theorem admit_read (frame : Frame) :
    (expression (environment (some frame)) (fields (some frame)) admitCondition).bind truth? =
      some (frame.role == .admit && frame.weightIndex != 0) := by
  have code : (frame.role.code == (15 : UInt32)) = (frame.role == .admit) :=
    role_code_equal frame.role .admit
  cases h : (frame.role == .admit) <;>
    simp [admitCondition, kind, field, tag, f, expression, truth?, equal?, code, h]

private theorem nested_read (frame : Frame) :
    (expression (environment (some frame)) (fields (some frame)) nestedCondition).bind truth? =
      some (frame.role == .nested && frame.nestedParked) := by
  have code : (frame.role.code == (12 : UInt32)) = (frame.role == .nested) :=
    role_code_equal frame.role .nested
  cases h : (frame.role == .nested) <;>
    simp [nestedCondition, kind, field, tag, f, expression, truth?, equal?, code, h]

private theorem rows_kind_read (frame : Frame) :
    (expression (environment (some frame)) (fields (some frame)) (kind "MATCH_ROWS")).bind truth? =
      some (frame.role == .matchRows) := by
  have code : (frame.role.code == (20 : UInt32)) = (frame.role == .matchRows) :=
    role_code_equal frame.role .matchRows
  simp [kind, field, tag, f, expression, truth?, equal?, code]

private theorem alternatives_kind_read (frame : Frame) :
    (expression (environment (some frame)) (fields (some frame)) (kind "ALTERNATIVES")).bind truth? =
      some (frame.role == .alternatives) := by
  have code : (frame.role.code == (21 : UInt32)) = (frame.role == .alternatives) :=
    role_code_equal frame.role .alternatives
  simp [kind, field, tag, f, expression, truth?, equal?, code]

private theorem pending_read (frame : Frame) :
    (expression (environment (some frame)) (fields (some frame)) pendingCondition).bind truth? =
      some (frame.pending == 0) := by
  simp [pendingCondition, field, f, expression, truth?, equal?]


private theorem unread_read (frame : Frame) :
    expression (environment (some frame)) (fields (some frame)) unread =
      some (.boolean (decide (frame.cursor < frame.childLength))) := by
  simp [unread, length, field, f, expression, numericBinary, unsigned64Binary]

private theorem forwarded_read (frame : Frame) :
    expression (environment (some frame)) (fields (some frame))
      (.binary .lt (field "stream_forwarded") length) =
      some (.boolean (decide (frame.forwarded < frame.childLength))) := by
  simp [length, field, f, expression, numericBinary, unsigned64Binary]

private theorem phase_call_read (frame : Frame) :
    expression (environment (some frame)) (fields (some frame)) (phase "WAIT_CALL") =
      some (.boolean (frame.phase == 1)) := by
  simp [phase, field, tag, f, expression, equal?]

private theorem phase_demand_read (frame : Frame) :
    expression (environment (some frame)) (fields (some frame)) (phase "DEMAND") =
      some (.boolean (frame.phase == 0)) := by
  simp [phase, field, tag, f, expression, equal?]

private theorem phase_branch_read (frame : Frame) :
    expression (environment (some frame)) (fields (some frame)) (phase "WAIT_BRANCH") =
      some (.boolean (frame.phase == 2)) := by
  simp [phase, field, tag, f, expression, equal?]

private theorem phase_iterate_read (frame : Frame) :
    expression (environment (some frame)) (fields (some frame)) (phase "ITERATE") =
      some (.boolean (frame.phase == 3)) := by
  simp [phase, field, tag, f, expression, equal?]

private theorem normalize_read (frame : Frame) :
    expression (environment (some frame)) (fields (some frame))
      (.binary .and (phase "WAIT_CALL") unread) =
      some (.boolean (frame.phase == 1 && decide (frame.cursor < frame.childLength))) :=
  boolean_and_read _ _ _ _ _ _ (phase_call_read frame) (unread_read frame)

private theorem strict_read (frame : Frame) :
    expression (environment (some frame)) (fields (some frame))
      (.binary .and (.binary .or (.binary .or (phase "DEMAND") (phase "WAIT_BRANCH"))
        (phase "ITERATE")) unread) =
      some (.boolean ((frame.phase == 0 || frame.phase == 2 || frame.phase == 3) &&
        decide (frame.cursor < frame.childLength))) :=
  boolean_and_read _ _ _ _ _ _
    (boolean_or_read _ _ _ _ _ _
      (boolean_or_read _ _ _ _ _ _ (phase_demand_read frame) (phase_branch_read frame))
      (phase_iterate_read frame)) (unread_read frame)

private theorem rows_read (frame : Frame) :
    expression (environment (some frame)) (fields (some frame))
      (.binary .and (field "match_rows")
        (.unary .not (.field (field "match_rows") "blocked".toList true))) =
      some (.boolean (frame.rowsBlocked.any (! ·))) := by
  cases h : frame.rowsBlocked <;> simp [field, f, expression, truth?, h]

private theorem equation_read (frame : Frame) :
    expression (environment (some frame)) (fields (some frame)) equation =
      some (.boolean (frame.equationPhase.any fun phaseValue =>
        phaseValue == 2 || (frame.forceStream && phaseValue == 1 &&
          decide (frame.cursor < frame.childLength)))) := by
  cases h : frame.equationPhase with
  | none => simp [equation, field, f, expression, truth?, h]
  | some phaseValue =>
      cases hf : frame.forceStream <;> cases hb : (phaseValue == 2) <;>
        cases hw : (phaseValue == 1) <;>
        simp [equation, unread, length, field, f, expression, truth?, equal?,
          numericBinary, unsigned64Binary, h, hf, hb, hw]


private theorem select_bindFinish (frame : Frame) (role : frame.role = .bindFinish) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_strict (frame : Frame) (role : frame.role = .strict) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some ((arms.drop 13).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_conditional (frame : Frame) (role : frame.role = .conditional) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some [.block (reply (.bool false))] := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_letBody (frame : Frame) (role : frame.role = .letBody) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some ((arms.drop 12).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_equationSearch (frame : Frame) (role : frame.role = .equationSearch) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some ((arms.drop 0).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_force (frame : Frame) (role : frame.role = .force) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some ((arms.drop 1).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_normalizeAtom (frame : Frame) (role : frame.role = .normalizeAtom) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some ((arms.drop 10).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_normalizeChildren (frame : Frame) (role : frame.role = .normalizeChildren) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some ((arms.drop 11).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_streamResume (frame : Frame) (role : frame.role = .streamResume) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some [.block (reply (.bool false))] := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_score (frame : Frame) (role : frame.role = .score) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some [.block (reply (.bool false))] := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_goal (frame : Frame) (role : frame.role = .goal) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some [.block (reply (.bool false))] := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_cost (frame : Frame) (role : frame.role = .cost) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some [.block (reply (.bool false))] := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_nested (frame : Frame) (role : frame.role = .nested) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some [.block (reply (.bool false))] := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_exactRational (frame : Frame) (role : frame.role = .exactRational) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some ((arms.drop 2).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_whereWeight (frame : Frame) (role : frame.role = .whereWeight) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some ((arms.drop 3).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_admit (frame : Frame) (role : frame.role = .admit) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some ((arms.drop 4).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_algebra (frame : Frame) (role : frame.role = .algebra) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some ((arms.drop 5).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_read (frame : Frame) (role : frame.role = .read) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some ((arms.drop 6).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_fold (frame : Frame) (role : frame.role = .fold) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some ((arms.drop 7).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_dialect (frame : Frame) (role : frame.role = .dialect) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some ((arms.drop 8).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_matchRows (frame : Frame) (role : frame.role = .matchRows) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some [.block (reply (.bool false))] := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem select_alternatives (frame : Frame) (role : frame.role = .alternatives) :
    LocalBlock.selectedSwitch? (fields (some frame)) (environment (some frame))
      (field "kind") arms (reply (.bool false)) =
      some [.block (reply (.bool false))] := by
  simp [LocalBlock.selectedSwitch?, LocalBlock.switchBody?, arms, field, f, tag,
    expression, equal?, Role.code, role]

private theorem switch_bindFinish (frame : Frame) (role : frame.role = .bindFinish) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_bindFinish frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (21 + 0 + 2) _
      (List.replicate 0 (.block []) ++ .block (reply (.binary .lt (field "stream_forwarded") length)) :: ((arms.drop 10).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]))) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 21 0 (.binary .lt (field "stream_forwarded") length) (.boolean (decide (frame.forwarded < frame.childLength))) ((arms.drop 10).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) (forwarded_read frame)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_strict (frame : Frame) (role : frame.role = .strict) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_strict frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (21 + 0 + 2) _
      (List.replicate 0 (.block []) ++ .block (reply (.binary .and (.binary .or (.binary .or (phase "DEMAND") (phase "WAIT_BRANCH")) (phase "ITERATE")) unread)) :: ((arms.drop 14).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]))) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 21 0 (.binary .and (.binary .or (.binary .or (phase "DEMAND") (phase "WAIT_BRANCH")) (phase "ITERATE")) unread) (.boolean ((frame.phase == 0 || frame.phase == 2 || frame.phase == 3) && decide (frame.cursor < frame.childLength))) ((arms.drop 14).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) (strict_read frame)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_conditional (frame : Frame) (role : frame.role = .conditional) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_conditional frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (21 + 0 + 2) _
      (List.replicate 0 (.block []) ++ .block (reply (.bool false)) :: [])) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 21 0 (.bool false) (.boolean false) [] (rfl)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_letBody (frame : Frame) (role : frame.role = .letBody) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_letBody frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (20 + 1 + 2) _
      (List.replicate 1 (.block []) ++ .block (reply (.binary .and (.binary .or (.binary .or (phase "DEMAND") (phase "WAIT_BRANCH")) (phase "ITERATE")) unread)) :: ((arms.drop 14).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]))) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 20 1 (.binary .and (.binary .or (.binary .or (phase "DEMAND") (phase "WAIT_BRANCH")) (phase "ITERATE")) unread) (.boolean ((frame.phase == 0 || frame.phase == 2 || frame.phase == 3) && decide (frame.cursor < frame.childLength))) ((arms.drop 14).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) (strict_read frame)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_equationSearch (frame : Frame) (role : frame.role = .equationSearch) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_equationSearch frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (21 + 0 + 2) _
      (List.replicate 0 (.block []) ++ .block (reply equation) :: ((arms.drop 1).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]))) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 21 0 equation (.boolean (frame.equationPhase.any fun phaseValue => phaseValue == 2 || (frame.forceStream && phaseValue == 1 && decide (frame.cursor < frame.childLength)))) ((arms.drop 1).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) (equation_read frame)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_force (frame : Frame) (role : frame.role = .force) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_force frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (14 + 7 + 2) _
      (List.replicate 7 (.block []) ++ .block (reply unread) :: ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]))) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 14 7 unread (.boolean (decide (frame.cursor < frame.childLength))) ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) (unread_read frame)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_normalizeAtom (frame : Frame) (role : frame.role = .normalizeAtom) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_normalizeAtom frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (20 + 1 + 2) _
      (List.replicate 1 (.block []) ++ .block (reply (.binary .and (phase "WAIT_CALL") unread)) :: ((arms.drop 12).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]))) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 20 1 (.binary .and (phase "WAIT_CALL") unread) (.boolean (frame.phase == 1 && decide (frame.cursor < frame.childLength))) ((arms.drop 12).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) (normalize_read frame)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_normalizeChildren (frame : Frame) (role : frame.role = .normalizeChildren) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_normalizeChildren frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (21 + 0 + 2) _
      (List.replicate 0 (.block []) ++ .block (reply (.binary .and (phase "WAIT_CALL") unread)) :: ((arms.drop 12).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]))) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 21 0 (.binary .and (phase "WAIT_CALL") unread) (.boolean (frame.phase == 1 && decide (frame.cursor < frame.childLength))) ((arms.drop 12).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) (normalize_read frame)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_streamResume (frame : Frame) (role : frame.role = .streamResume) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_streamResume frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (21 + 0 + 2) _
      (List.replicate 0 (.block []) ++ .block (reply (.bool false)) :: [])) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 21 0 (.bool false) (.boolean false) [] (rfl)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_score (frame : Frame) (role : frame.role = .score) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_score frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (21 + 0 + 2) _
      (List.replicate 0 (.block []) ++ .block (reply (.bool false)) :: [])) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 21 0 (.bool false) (.boolean false) [] (rfl)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_goal (frame : Frame) (role : frame.role = .goal) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_goal frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (21 + 0 + 2) _
      (List.replicate 0 (.block []) ++ .block (reply (.bool false)) :: [])) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 21 0 (.bool false) (.boolean false) [] (rfl)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_cost (frame : Frame) (role : frame.role = .cost) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_cost frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (21 + 0 + 2) _
      (List.replicate 0 (.block []) ++ .block (reply (.bool false)) :: [])) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 21 0 (.bool false) (.boolean false) [] (rfl)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_nested (frame : Frame) (role : frame.role = .nested) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_nested frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (21 + 0 + 2) _
      (List.replicate 0 (.block []) ++ .block (reply (.bool false)) :: [])) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 21 0 (.bool false) (.boolean false) [] (rfl)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_exactRational (frame : Frame) (role : frame.role = .exactRational) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_exactRational frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (15 + 6 + 2) _
      (List.replicate 6 (.block []) ++ .block (reply unread) :: ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]))) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 15 6 unread (.boolean (decide (frame.cursor < frame.childLength))) ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) (unread_read frame)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_whereWeight (frame : Frame) (role : frame.role = .whereWeight) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_whereWeight frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (16 + 5 + 2) _
      (List.replicate 5 (.block []) ++ .block (reply unread) :: ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]))) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 16 5 unread (.boolean (decide (frame.cursor < frame.childLength))) ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) (unread_read frame)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_admit (frame : Frame) (role : frame.role = .admit) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_admit frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (17 + 4 + 2) _
      (List.replicate 4 (.block []) ++ .block (reply unread) :: ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]))) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 17 4 unread (.boolean (decide (frame.cursor < frame.childLength))) ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) (unread_read frame)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_algebra (frame : Frame) (role : frame.role = .algebra) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_algebra frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (18 + 3 + 2) _
      (List.replicate 3 (.block []) ++ .block (reply unread) :: ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]))) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 18 3 unread (.boolean (decide (frame.cursor < frame.childLength))) ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) (unread_read frame)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_read (frame : Frame) (role : frame.role = .read) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_read frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (19 + 2 + 2) _
      (List.replicate 2 (.block []) ++ .block (reply unread) :: ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]))) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 19 2 unread (.boolean (decide (frame.cursor < frame.childLength))) ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) (unread_read frame)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_fold (frame : Frame) (role : frame.role = .fold) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_fold frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (20 + 1 + 2) _
      (List.replicate 1 (.block []) ++ .block (reply unread) :: ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]))) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 20 1 unread (.boolean (decide (frame.cursor < frame.childLength))) ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) (unread_read frame)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_dialect (frame : Frame) (role : frame.role = .dialect) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_dialect frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (21 + 0 + 2) _
      (List.replicate 0 (.block []) ++ .block (reply unread) :: ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]))) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 21 0 unread (.boolean (decide (frame.cursor < frame.childLength))) ((arms.drop 9).map (fun arm => .block arm.2) ++ [.block (reply (.bool false))]) (unread_read frame)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_matchRows (frame : Frame) (role : frame.role = .matchRows) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_matchRows frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (21 + 0 + 2) _
      (List.replicate 0 (.block []) ++ .block (reply (.bool false)) :: [])) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 21 0 (.bool false) (.boolean false) [] (rfl)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_alternatives (frame : Frame) (role : frame.role = .alternatives) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  change LocalBlock.execute _ 24 _ [.switch (field "kind") arms (reply (.bool false))] = _
  rw [LocalBlock.switch_executes_selected_body _ 23 _ _ _ _ _ [] (select_alternatives frame role)]
  change LocalBlock.switchResume _
    (LocalBlock.execute _ (21 + 0 + 2) _
      (List.replicate 0 (.block []) ++ .block (reply (.bool false)) :: [])) = _
  have run := LocalBlock.empty_blocks_then_return (fields (some frame)) (environment (some frame)) 21 0 (.bool false) (.boolean false) [] (rfl)
  simp only [reply] at run ⊢
  rw [run]
  simp only [LocalBlock.switchResume, returned, waiting, role]

private theorem switch_returns_waiting (frame : Frame) :
    LocalBlock.execute (fields (some frame)) 24 (environment (some frame)) (body.drop 6) =
      returned (some frame) (waiting frame) := by
  cases role : frame.role with
  | bindFinish => exact switch_bindFinish frame role
  | strict => exact switch_strict frame role
  | conditional => exact switch_conditional frame role
  | letBody => exact switch_letBody frame role
  | equationSearch => exact switch_equationSearch frame role
  | force => exact switch_force frame role
  | normalizeAtom => exact switch_normalizeAtom frame role
  | normalizeChildren => exact switch_normalizeChildren frame role
  | streamResume => exact switch_streamResume frame role
  | score => exact switch_score frame role
  | goal => exact switch_goal frame role
  | cost => exact switch_cost frame role
  | nested => exact switch_nested frame role
  | exactRational => exact switch_exactRational frame role
  | whereWeight => exact switch_whereWeight frame role
  | admit => exact switch_admit frame role
  | algebra => exact switch_algebra frame role
  | read => exact switch_read frame role
  | fold => exact switch_fold frame role
  | dialect => exact switch_dialect frame role
  | matchRows => exact switch_matchRows frame role
  | alternatives => exact switch_alternatives frame role

theorem frame_returns_ready (frame : Frame) :
    LocalBlock.execute (fields (some frame)) 30 (environment (some frame)) body =
      returned (some frame) (ready (some frame)) := by
  change LocalBlock.execute _ 30 _
    (.branch closedCondition (reply (.bool false)) [] :: body.drop 1) = _
  rw [branch_returns_or_continues _ _ 28 _ _ false _ (closed_read frame)]
  change (if frame.closed || frame.ownershipParked then returned (some frame) false else
    LocalBlock.execute _ 29 _
      (.branch admitCondition (reply (.bool false)) [] :: body.drop 2)) = _
  rw [branch_returns_or_continues _ _ 27 _ _ false _ (admit_read frame)]
  change (if frame.closed || frame.ownershipParked then returned (some frame) false else
    if frame.role == .admit && frame.weightIndex != 0 then returned (some frame) false else
    LocalBlock.execute _ 28 _
      (.branch nestedCondition (reply (.bool false)) [] :: body.drop 3)) = _
  rw [branch_returns_or_continues _ _ 26 _ _ false _ (nested_read frame)]
  change (if frame.closed || frame.ownershipParked then returned (some frame) false else
    if frame.role == .admit && frame.weightIndex != 0 then returned (some frame) false else
    if frame.role == .nested && frame.nestedParked then returned (some frame) false else
    LocalBlock.execute _ 27 _
      (.branch (kind "MATCH_ROWS")
        (reply (.binary .and (field "match_rows")
          (.unary .not (.field (field "match_rows") "blocked".toList true)))) [] ::
        body.drop 4)) = _
  simp only [reply]
  rw [LocalBlock.branch_returns_expression _ _ 25 _ _ _ _ _ (rows_kind_read frame) (rows_read frame)]
  change (if frame.closed || frame.ownershipParked then returned (some frame) false else
    if frame.role == .admit && frame.weightIndex != 0 then returned (some frame) false else
    if frame.role == .nested && frame.nestedParked then returned (some frame) false else
    if frame.role == .matchRows then returned (some frame) (frame.rowsBlocked.any (! ·)) else
    LocalBlock.execute _ 26 _
      (.branch (kind "ALTERNATIVES") (reply (.bool true)) [] :: body.drop 5)) = _
  rw [branch_returns_or_continues _ _ 24 _ _ true _ (alternatives_kind_read frame)]
  change (if frame.closed || frame.ownershipParked then returned (some frame) false else
    if frame.role == .admit && frame.weightIndex != 0 then returned (some frame) false else
    if frame.role == .nested && frame.nestedParked then returned (some frame) false else
    if frame.role == .matchRows then returned (some frame) (frame.rowsBlocked.any (! ·)) else
    if frame.role == .alternatives then returned (some frame) true else
    LocalBlock.execute _ 25 _
      (.branch pendingCondition (reply (.bool true)) [] :: body.drop 6)) = _
  rw [branch_returns_or_continues _ _ 23 _ _ true _ (pending_read frame),
    switch_returns_waiting frame]
  change (if frame.closed || frame.ownershipParked then returned (some frame) false else
    if frame.role == .admit && frame.weightIndex != 0 then returned (some frame) false else
    if frame.role == .nested && frame.nestedParked then returned (some frame) false else
    if frame.role == .matchRows then returned (some frame) (frame.rowsBlocked.any (! ·)) else
    if frame.role == .alternatives then returned (some frame) true else
    if frame.pending == 0 then returned (some frame) true else
      returned (some frame) (waiting frame)) = _
  simp only [result_if]
  congr 1
  cases role : frame.role <;> simp [ready, role] <;> simp only [Bool.beq_eq_decide_eq]

theorem source_returns_ready (view : Option Frame) :
    LocalBlock.execute (fields view) 30 (environment view) body =
      returned view (ready view) := by
  cases view with
  | none => rfl
  | some frame => exact frame_returns_ready frame


namespace Controls

def base : Frame :=
  ⟨.force, 1, false, false, 0, false, 1, 0, 0, 1, none, none, false⟩

theorem wide_prefix_is_ready :
    let view := some {base with cursor := 4294967296, childLength := 4294967297}
    LocalBlock.execute (fields view) 30 (environment view) body = returned view true := by
  dsimp only
  rw [source_returns_ready]
  rfl

theorem wide_nonzero_obligation_does_not_become_zero :
    let view := some {base with role := .conditional, pending := 4294967296}
    LocalBlock.execute (fields view) 30 (environment view) body = returned view false := by
  dsimp only
  rw [source_returns_ready]
  rfl

theorem closed_work_is_unavailable :
    let view := some {base with closed := true, pending := 0}
    LocalBlock.execute (fields view) 30 (environment view) body = returned view false := by
  dsimp only
  rw [source_returns_ready]
  rfl

theorem parked_weight_owner_is_unavailable :
    let view := some {base with ownershipParked := true, pending := 0}
    LocalBlock.execute (fields view) 30 (environment view) body = returned view false := by
  dsimp only
  rw [source_returns_ready]
  rfl

theorem admission_pending_verdict_blocks_zero_obligation :
    let view := some {base with role := .admit, weightIndex := 4294967296, pending := 0}
    LocalBlock.execute (fields view) 30 (environment view) body = returned view false := by
  dsimp only
  rw [source_returns_ready]
  rfl

theorem nested_park_blocks_zero_obligation :
    let view := some {base with role := .nested, nestedParked := true, pending := 0}
    LocalBlock.execute (fields view) 30 (environment view) body = returned view false := by
  dsimp only
  rw [source_returns_ready]
  rfl

theorem missing_rows_are_not_made_ready_by_zero_obligation :
    let view := some {base with role := .matchRows, pending := 0}
    LocalBlock.execute (fields view) 30 (environment view) body = returned view false := by
  dsimp only
  rw [source_returns_ready]
  rfl

theorem blocked_rows_are_not_made_ready_by_zero_obligation :
    let view := some {base with role := .matchRows, rowsBlocked := some true, pending := 0}
    LocalBlock.execute (fields view) 30 (environment view) body = returned view false := by
  dsimp only
  rw [source_returns_ready]
  rfl

theorem available_rows_progress_with_producer_obligations :
    let view := some {base with role := .matchRows, rowsBlocked := some false}
    LocalBlock.execute (fields view) 30 (environment view) body = returned view true := by
  dsimp only
  rw [source_returns_ready]
  rfl

theorem alternatives_progress_with_producer_obligations :
    let view := some {base with role := .alternatives}
    LocalBlock.execute (fields view) 30 (environment view) body = returned view true := by
  dsimp only
  rw [source_returns_ready]
  rfl

theorem binding_uses_forwarded_cursor_instead_of_input_cursor :
    let view := some {base with role := .bindFinish, cursor := 0, forwarded := 1}
    LocalBlock.execute (fields view) 30 (environment view) body = returned view false := by
  dsimp only
  rw [source_returns_ready]
  rfl

theorem publication_progress_does_not_require_an_unread_child :
    let view := some {base with role := .equationSearch, equationPhase := some 2, cursor := 1}
    LocalBlock.execute (fields view) 30 (environment view) body = returned view true := by
  dsimp only
  rw [source_returns_ready]
  rfl

theorem waiting_equation_requires_stream_permission :
    let view := some {base with role := .equationSearch, equationPhase := some 1}
    LocalBlock.execute (fields view) 30 (environment view) body = returned view false := by
  dsimp only
  rw [source_returns_ready]
  rfl

theorem strict_wait_call_does_not_consume_an_available_branch :
    let view := some {base with role := .strict, phase := 1}
    LocalBlock.execute (fields view) 30 (environment view) body = returned view false := by
  dsimp only
  rw [source_returns_ready]
  rfl

end Controls

end ReadView
/-- Complete source consumption and execution agree with the independent
readiness contract for a coherent immutable view of the admitted frame roles.
The execution retains the whole local environment. Physical pointer validity,
layout, compiler correctness and concurrent reads remain service obligations. -/
theorem source_view_exact (view : Option ReadView.Frame) :
    qualifiedFunctionText? types source = some parsed ∧
    NativeC.LocalBlock.execute (ReadView.fields view) 30 (ReadView.environment view) parsed.body =
      ReadView.returned view (ReadView.ready view) :=
  ⟨source_recognized, ReadView.source_returns_ready view⟩

end FrameReadiness

end Mettapedia.Languages.MeTTa.CeTTaNativeCost


namespace Mettapedia.Languages.MeTTa.CeTTaNativeCost.IssuedReturnSource.TakeForResume.Append

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn

universe u

/-- Execute the retained aggregate's operands through the physical scalar
reader. The record's scalar widths and nullable identities are checked after
the supplied operands have been read. -/
def physicalRow (layout : ReadExpressions.Layout) (environment : ReadExpressions.Environment) :
    CExpr → CProg CVal (Row (Option Ptr) (Option Ptr))
  | .aggregate type arguments =>
      if type = ⟨"CettaContinuationLease".toList, 0⟩ then do
        let values ← ReadExpressions.operands layout environment arguments
        match values with
        | [.u64 occurrence, .u64 token, .ptr payload, .ptr provider] =>
            pure ⟨occurrence.toNat, token.toNat, payload, provider⟩
        | _ => CProg.undefined
      else CProg.undefined
  | _ => CProg.undefined

section Physical

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

theorem actual_row_physical_reads (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (owner : Ptr)
    (occurrence token : UInt64) (payload provider : Option Ptr)
    (occurrenceOffset tokenOffset payloadOffset providerOffset : Nat)
    {P : Heap L → Prop}
    (ownerRead : environment "owned".toList = some (.ptr (some owner)))
    (occurrenceSelected : layout "occurrence_id".toList = some ⟨occurrenceOffset, .word64⟩)
    (tokenSelected : layout "resume_lease".toList = some ⟨tokenOffset, .word64⟩)
    (payloadSelected : layout "payload".toList = some ⟨payloadOffset, .pointer⟩)
    (providerSelected : layout "provider".toList = some ⟨providerOffset, .pointer⟩)
    (occurrenceRead : ∀ heap, P heap → CellPermission.read
      ((heap (owner + occurrenceOffset).block).2 (owner + occurrenceOffset).offset) =
        some (some (.u64 occurrence)))
    (tokenRead : ∀ heap, P heap → CellPermission.read
      ((heap (owner + tokenOffset).block).2 (owner + tokenOffset).offset) =
        some (some (.u64 token)))
    (payloadRead : ∀ heap, P heap → CellPermission.read
      ((heap (owner + payloadOffset).block).2 (owner + payloadOffset).offset) =
        some (some (.ptr payload)))
    (providerRead : ∀ heap, P heap → CellPermission.read
      ((heap (owner + providerOffset).block).2 (owner + providerOffset).offset) =
        some (some (.ptr provider))) :
    CTriple P (physicalRow layout environment leaseRhs)
      (fun row heap => row = ⟨occurrence.toNat, token.toNat, payload, provider⟩ ∧ P heap) := by
  have operandsSpec := ReadExpressions.operands_read_rule layout environment
    (List.Forall₂.cons
      (ReadExpressions.expression_field_read_rule layout environment "owned".toList
        "occurrence_id".toList owner occurrenceOffset (.u64 occurrence)
          ownerRead occurrenceSelected occurrenceRead)
      (List.Forall₂.cons
        (ReadExpressions.expression_field_read_rule layout environment "owned".toList
          "resume_lease".toList owner tokenOffset (.u64 token)
            ownerRead tokenSelected tokenRead)
        (List.Forall₂.cons
          (ReadExpressions.expression_field_read_rule layout environment "owned".toList
            "payload".toList owner payloadOffset (.ptr payload)
              ownerRead payloadSelected payloadRead)
          (List.Forall₂.cons
            (ReadExpressions.expression_field_read_rule layout environment "owned".toList
              "provider".toList owner providerOffset (.ptr provider)
                ownerRead providerSelected providerRead)
            List.Forall₂.nil))))
  simp only [physicalRow, leaseRhs]
  refine triple_bind _ operandsSpec fun values => ?_
  apply triple_pure
  intro same
  subst values
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

theorem actual_row_heap_view (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (heap : Heap L) (owner : Ptr)
    (occurrence token : UInt64) (payload provider : Option Ptr)
    (occurrenceOffset tokenOffset payloadOffset providerOffset : Nat)
    (ownerRead : environment "owned".toList = some (.ptr (some owner)))
    (occurrenceSelected : layout "occurrence_id".toList = some ⟨occurrenceOffset, .word64⟩)
    (tokenSelected : layout "resume_lease".toList = some ⟨tokenOffset, .word64⟩)
    (payloadSelected : layout "payload".toList = some ⟨payloadOffset, .pointer⟩)
    (providerSelected : layout "provider".toList = some ⟨providerOffset, .pointer⟩)
    (occurrenceRead : CellPermission.read
      ((heap (owner + occurrenceOffset).block).2 (owner + occurrenceOffset).offset) =
        some (some (.u64 occurrence)))
    (tokenRead : CellPermission.read
      ((heap (owner + tokenOffset).block).2 (owner + tokenOffset).offset) =
        some (some (.u64 token)))
    (payloadRead : CellPermission.read
      ((heap (owner + payloadOffset).block).2 (owner + payloadOffset).offset) =
        some (some (.ptr payload)))
    (providerRead : CellPermission.read
      ((heap (owner + providerOffset).block).2 (owner + providerOffset).offset) =
        some (some (.ptr provider))) :
    leaseRow? (ReadExpressions.environmentView environment)
      (ReadExpressions.fieldView layout heap) leaseRhs =
        some ⟨occurrence.toNat, token.toNat, payload, provider⟩ := by
  apply actual_row_read _ _ owner occurrence token payload provider
  · simp only [ReadExpressions.environmentView, ownerRead, Option.map_some,
      ReadExpressions.scalar]
  · exact ReadExpressions.field_view_of_read layout heap owner "occurrence_id".toList
      occurrenceOffset (.u64 occurrence) occurrenceSelected occurrenceRead
  · exact ReadExpressions.field_view_of_read layout heap owner "resume_lease".toList
      tokenOffset (.u64 token) tokenSelected tokenRead
  · exact ReadExpressions.field_view_of_read layout heap owner "payload".toList
      payloadOffset (.ptr payload) payloadSelected payloadRead
  · exact ReadExpressions.field_view_of_read layout heap owner "provider".toList
      providerOffset (.ptr provider) providerSelected providerRead

open scoped Mettapedia.GSLT.SeparationAlgebra

/-- The four held cells, with an arbitrary separate frame. Offsets are
cell descriptors; this assertion does not choose a compiled byte layout. -/
def leaseFootprint {L : Type u} [Zero L] [Add L] [SepAlgebra L]
    [CellPermission L (Option CVal)] (owner : Ptr)
    (occurrenceOffset tokenOffset payloadOffset providerOffset : Nat)
    (occurrence token : UInt64) (payload provider : Option Ptr)
    (frame : Heap L → Prop) : Heap L → Prop :=
  PointsTo (owner + occurrenceOffset) (.u64 occurrence) ∗
    (PointsTo (owner + tokenOffset) (.u64 token) ∗
      (PointsTo (owner + payloadOffset) (.ptr payload) ∗
        (PointsTo (owner + providerOffset) (.ptr provider) ∗ frame)))

theorem leaseFootprint_reads {L : Type u} [Zero L] [Add L] [SepAlgebra L]
    [CellPermission L (Option CVal)] (owner : Ptr)
    (occurrenceOffset tokenOffset payloadOffset providerOffset : Nat)
    (occurrence token : UInt64) (payload provider : Option Ptr)
    (frame : Heap L → Prop) (heap : Heap L)
    (held : leaseFootprint owner occurrenceOffset tokenOffset payloadOffset providerOffset
      occurrence token payload provider frame heap) :
    CellPermission.read ((heap (owner + occurrenceOffset).block).2
      (owner + occurrenceOffset).offset) = some (some (.u64 occurrence)) ∧
    CellPermission.read ((heap (owner + tokenOffset).block).2
      (owner + tokenOffset).offset) = some (some (.u64 token)) ∧
    CellPermission.read ((heap (owner + payloadOffset).block).2
      (owner + payloadOffset).offset) = some (some (.ptr payload)) ∧
    CellPermission.read ((heap (owner + providerOffset).block).2
      (owner + providerOffset).offset) = some (some (.ptr provider)) := by
  change (PointsTo _ _ ∗ (PointsTo _ _ ∗ (PointsTo _ _ ∗ (PointsTo _ _ ∗ frame)))) heap at held
  refine ⟨read_of_pointsTo held, ?_, ?_, ?_⟩
  · exact read_framed_right held fun _ rest => read_of_pointsTo rest
  · exact read_framed_right held fun _ rest =>
      read_framed_right rest fun _ rest => read_of_pointsTo rest
  · exact read_framed_right held fun _ rest =>
      read_framed_right rest fun _ rest =>
        read_framed_right rest fun _ rest => read_of_pointsTo rest

/-- Ownership of the physical fields discharges the read premises for the
retained initializer. No field-result service is assumed. -/
theorem actual_row_owned_cells (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (owner : Ptr)
    (occurrence token : UInt64) (payload provider : Option Ptr)
    (occurrenceOffset tokenOffset payloadOffset providerOffset : Nat)
    (frame : Heap L → Prop)
    (ownerRead : environment "owned".toList = some (.ptr (some owner)))
    (occurrenceSelected : layout "occurrence_id".toList = some ⟨occurrenceOffset, .word64⟩)
    (tokenSelected : layout "resume_lease".toList = some ⟨tokenOffset, .word64⟩)
    (payloadSelected : layout "payload".toList = some ⟨payloadOffset, .pointer⟩)
    (providerSelected : layout "provider".toList = some ⟨providerOffset, .pointer⟩) :
    CTriple (leaseFootprint owner occurrenceOffset tokenOffset payloadOffset providerOffset
        occurrence token payload provider frame)
      (physicalRow layout environment leaseRhs)
      (fun row heap => row = ⟨occurrence.toNat, token.toNat, payload, provider⟩ ∧
        leaseFootprint owner occurrenceOffset tokenOffset payloadOffset providerOffset
          occurrence token payload provider frame heap) := by
  apply actual_row_physical_reads layout environment owner occurrence token payload provider
    occurrenceOffset tokenOffset payloadOffset providerOffset ownerRead
    occurrenceSelected tokenSelected payloadSelected providerSelected
  · intro heap held
    exact (leaseFootprint_reads owner occurrenceOffset tokenOffset payloadOffset providerOffset
      occurrence token payload provider frame heap held).1
  · intro heap held
    exact (leaseFootprint_reads owner occurrenceOffset tokenOffset payloadOffset providerOffset
      occurrence token payload provider frame heap held).2.1
  · intro heap held
    exact (leaseFootprint_reads owner occurrenceOffset tokenOffset payloadOffset providerOffset
      occurrence token payload provider frame heap held).2.2.1
  · intro heap held
    exact (leaseFootprint_reads owner occurrenceOffset tokenOffset payloadOffset providerOffset
      occurrence token payload provider frame heap held).2.2.2

/-- The observer is derived from the same owned cells used by execution. -/
theorem actual_row_owned_heap_view (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (heap : Heap L) (owner : Ptr)
    (occurrence token : UInt64) (payload provider : Option Ptr)
    (occurrenceOffset tokenOffset payloadOffset providerOffset : Nat)
    (frame : Heap L → Prop)
    (ownerRead : environment "owned".toList = some (.ptr (some owner)))
    (occurrenceSelected : layout "occurrence_id".toList = some ⟨occurrenceOffset, .word64⟩)
    (tokenSelected : layout "resume_lease".toList = some ⟨tokenOffset, .word64⟩)
    (payloadSelected : layout "payload".toList = some ⟨payloadOffset, .pointer⟩)
    (providerSelected : layout "provider".toList = some ⟨providerOffset, .pointer⟩)
    (held : leaseFootprint owner occurrenceOffset tokenOffset payloadOffset providerOffset
      occurrence token payload provider frame heap) :
    leaseRow? (ReadExpressions.environmentView environment)
      (ReadExpressions.fieldView layout heap) leaseRhs =
        some ⟨occurrence.toNat, token.toNat, payload, provider⟩ := by
  obtain ⟨readsOccurrence, readsToken, readsPayload, readsProvider⟩ :=
    leaseFootprint_reads owner occurrenceOffset tokenOffset payloadOffset providerOffset
      occurrence token payload provider frame heap held
  exact actual_row_heap_view layout environment heap owner occurrence token payload provider
    occurrenceOffset tokenOffset payloadOffset providerOffset ownerRead occurrenceSelected
    tokenSelected payloadSelected providerSelected readsOccurrence readsToken readsPayload readsProvider

theorem leaseFootprint_four_cell_range (owner : Ptr) (occurrence token : UInt64)
    (payload provider : Option Ptr) :
    leaseFootprint (L := L) owner 0 1 2 3 occurrence token payload provider emp =
      Cells owner [some (.u64 occurrence), some (.u64 token),
        some (.ptr payload), some (.ptr provider)] := by
  simp only [leaseFootprint, PointsTo, sepConj_emp]
  have shifted (n : Nat) : owner + n + 1 = owner + (n + 1) := by
    show (⟨owner.block, owner.offset + n + 1⟩ : Ptr) =
      ⟨owner.block, owner.offset + (n + 1)⟩
    rw [Nat.add_assoc]
  rw [← shifted 2, ← cells_cons, ← shifted 1, ← cells_cons, ← shifted 0, ← cells_cons]
  rfl


/-- The four consecutive fields can be read beside an arbitrary owned frame. -/
theorem leaseFootprint_four_cell_range_framed (owner : Ptr) (occurrence token : UInt64)
    (payload provider : Option Ptr) (frame : Heap L → Prop) :
    leaseFootprint (L := L) owner 0 1 2 3 occurrence token payload provider frame =
      (Cells owner [some (.u64 occurrence), some (.u64 token),
        some (.ptr payload), some (.ptr provider)] ∗ frame) := by
  rw [← leaseFootprint_four_cell_range]
  simp only [leaseFootprint, sepConj_emp, sepConj_assoc]

namespace PhysicalControls

abbrev Permission := Excl (Option CVal)

def owner : Ptr := ⟨41, 0⟩
def occurrence : UInt64 := UInt64.ofNat (2 ^ 63 + 7)
def token : UInt64 := UInt64.ofNat (2 ^ 64 - 1)

def layout : ReadExpressions.Layout := fun name =>
  if name = "occurrence_id".toList then some ⟨0, .word64⟩
  else if name = "resume_lease".toList then some ⟨1, .word64⟩
  else if name = "payload".toList then some ⟨2, .pointer⟩
  else if name = "provider".toList then some ⟨3, .pointer⟩
  else none

def environment : ReadExpressions.Environment := fun name =>
  if name = "owned".toList then some (.ptr (some owner)) else none

def cells : List (Option CVal) :=
  [some (.u64 occurrence), some (.u64 token), some (.ptr none), some (.ptr none)]

def heap : Heap Permission :=
  atBlock owner.block (.empty, segment owner.offset (cells.map CellPermission.whole))

def held : Heap Permission → Prop :=
  leaseFootprint owner 0 1 2 3 occurrence token none none emp

theorem concrete_footprint_is_inhabited : held heap := by
  rw [held, leaseFootprint_four_cell_range]
  rfl

theorem wide_nullable_row_spec :
    CTriple held (physicalRow layout environment leaseRhs)
      (fun row heap => row = ⟨occurrence.toNat, token.toNat, none, none⟩ ∧ held heap) :=
  actual_row_owned_cells layout environment owner occurrence token none none 0 1 2 3 emp
    rfl rfl rfl rfl rfl

/-- The positive row has an actual execution in the existing memory semantics;
the footprint premise is supplied by a concrete heap above. -/
theorem wide_nullable_row_runs :
    ∃ finalHeap, (physicalRow layout environment leaseRhs).Runs act heap
      ⟨occurrence.toNat, token.toNat, none, none⟩ finalHeap ∧ held finalHeap := by
  have spec := wide_nullable_row_spec heap concrete_footprint_is_inhabited
  obtain ⟨row, finalHeap, runs⟩ := Mettapedia.Machines.CMemory.exists_runs
    (physicalRow layout environment leaseRhs) heap spec.1
  obtain ⟨same, remains⟩ := spec.2 row finalHeap runs
  subst row
  exact ⟨finalHeap, runs, remains⟩

theorem wide_values_are_retained :
    occurrence.toNat = 2 ^ 63 + 7 ∧ token.toNat = 2 ^ 64 - 1 := by
  decide +kernel

theorem concrete_heap_readout :
    leaseRow? (ReadExpressions.environmentView environment)
      (ReadExpressions.fieldView layout heap) leaseRhs =
        some ⟨occurrence.toNat, token.toNat, none, none⟩ :=
  actual_row_owned_heap_view layout environment heap owner occurrence token none none
    0 1 2 3 emp rfl rfl rfl rfl rfl concrete_footprint_is_inhabited

theorem absent_ownership_is_not_a_row :
    leaseRow? (ReadExpressions.environmentView environment)
      (ReadExpressions.fieldView layout (0 : Heap Permission)) leaseRhs = none := rfl

theorem wrong_aggregate_tag_is_undefined :
    physicalRow layout environment (.aggregate ⟨"OtherRecord".toList, 0⟩
      [.field (.identifier "owned".toList) "occurrence_id".toList true,
        .field (.identifier "owned".toList) "resume_lease".toList true,
        .field (.identifier "owned".toList) "payload".toList true,
        .field (.identifier "owned".toList) "provider".toList true]) = CProg.undefined := rfl

theorem absent_ownership_is_unsafe :
    ¬ (physicalRow layout environment leaseRhs).Safe act (0 : Heap Permission) := by
  intro safe
  simp only [physicalRow, leaseRhs] at safe
  have safeOperands := (Prog.safe_bind _ _ _ _).mp safe |>.1
  simp only [ReadExpressions.operands, List.mapM_cons] at safeOperands
  have safeFirst := (Prog.safe_bind _ _ _ _).mp safeOperands |>.1
  change (CProg.loadU64 (owner + 0) >>= fun value => (pure (CVal.u64 value) : CProg CVal CVal)).Safe act
    (0 : Heap Permission) at safeFirst
  have safeTypedLoad := (Prog.safe_bind _ _ _ _).mp safeFirst |>.1
  have safeLoad := (Prog.safe_bind _ _ _ _).mp safeTypedLoad |>.1
  obtain ⟨value, permission⟩ := safeLoad.1
  change (none : Option (Option CVal)) = some (some value) at permission
  cases permission


/-- A whole, live four-cell heap supplies the footprint and its header. -/
def liveHeap : Heap Permission :=
  atBlock owner.block (.own ⟨4, true⟩, segment owner.offset (cells.map CellPermission.whole))

def liveHeld : Heap Permission → Prop :=
  leaseFootprint owner 0 1 2 3 occurrence token none none (LiveBlock owner.block 4)

theorem live_footprint_is_inhabited : liveHeld liveHeap := by
  rw [liveHeld, leaseFootprint_four_cell_range_framed, sepConj_comm]
  exact (liveBlock_cells_iff owner.block cells 4 liveHeap).mpr rfl

theorem live_heap_wellFormed : WellFormed liveHeap := by
  have empty : WellFormed (0 : Heap Permission) := by
    intro block index held
    exact False.elim (held rfl)
  apply wellFormed_update empty owner.block
  intro index nonzero
  refine ⟨4, rfl, ?_⟩
  by_contra outside
  have after : 4 ≤ index := Nat.not_lt.mp outside
  have absent : segment (L := Permission) owner.offset (cells.map CellPermission.whole) index = 0 :=
    segment_of_le (L := Permission) _ (by simpa [owner, cells] using after)
  exact nonzero absent

/-- This control runs in a well-formed whole heap, rather than only its
separated cell footprint. The live header survives with the read fields. -/
theorem wide_nullable_live_row_runs :
    ∃ finalHeap, (physicalRow layout environment leaseRhs).Runs act liveHeap
      ⟨occurrence.toNat, token.toNat, none, none⟩ finalHeap ∧
        liveHeld finalHeap ∧ WellFormed finalHeap := by
  have rule := actual_row_owned_cells (L := Permission) layout environment owner occurrence token none none
    0 1 2 3 (LiveBlock owner.block 4) rfl rfl rfl rfl rfl
  have spec := rule liveHeap live_footprint_is_inhabited
  obtain ⟨row, finalHeap, runs⟩ := Mettapedia.Machines.CMemory.exists_runs
    (physicalRow layout environment leaseRhs) liveHeap spec.1
  obtain ⟨same, remains⟩ := spec.2 row finalHeap runs
  subst row
  exact ⟨finalHeap, runs, remains, runs_wellFormed _ live_heap_wellFormed spec.1 runs⟩

end PhysicalControls

end Physical

end Mettapedia.Languages.MeTTa.CeTTaNativeCost.IssuedReturnSource.TakeForResume.Append

namespace Mettapedia.Languages.MeTTa.CeTTaNativeCost.IssuedReturnSource.TakeForResume.Append

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.PostIndex
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.PostIndex.WordStore
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn

universe u

section PhysicalIssuance

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

/-- The source append view reads its initializer from the same held memory
cells as the physical program. The backing-row list is still a representation
view; this theorem does not claim physical array publication or allocation. -/
theorem actual_owned_append_issues (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (heap : Heap L)
    (registry : Registry (Option Ptr) (Option Ptr))
    (selected : Handle (Option Ptr) (Option Ptr))
    (slots : List (Row (Option Ptr) (Option Ptr))) (count : UInt64)
    (owner : Ptr) (occurrence token : UInt64) (payload provider : Option Ptr)
    (occurrenceOffset tokenOffset payloadOffset providerOffset : Nat)
    (frame : Heap L → Prop)
    (ownerRead : environment "owned".toList = some (.ptr (some owner)))
    (occurrenceSelected : layout "occurrence_id".toList = some ⟨occurrenceOffset, .word64⟩)
    (tokenSelected : layout "resume_lease".toList = some ⟨tokenOffset, .word64⟩)
    (payloadSelected : layout "payload".toList = some ⟨payloadOffset, .pointer⟩)
    (providerSelected : layout "provider".toList = some ⟨providerOffset, .pointer⟩)
    (held : leaseFootprint owner occurrenceOffset tokenOffset payloadOffset providerOffset
      occurrence token payload provider frame heap)
    (representedOccurrence : selected.row.occurrence = occurrence.toNat)
    (representedPayload : selected.row.payload = payload)
    (representedProvider : selected.row.provider = provider)
    (sized : slots.length < 2 ^ 64) (room : count.toNat < slots.length)
    (representedRows : registry.rows = slots.take count.toNat) :
    ∃ next after,
      body[10]?.bind (executeAppend (resolve (ReadExpressions.environmentView environment)
        (ReadExpressions.fieldView layout heap) slots count)) = some (next, after) ∧
      (registerIssued registry selected token.toNat).1.rows = after.take next.toNat ∧
      (registerIssued registry selected token.toNat).2.store = registry.identity ∧
      (registerIssued registry selected token.toNat).2.parent = selected.parent ∧
      (registerIssued registry selected token.toNat).2.row =
        { selected.row with token := token.toNat } ∧
      next.toNat = count.toNat + 1 ∧ after.length = slots.length ∧
      after.take count.toNat = slots.take count.toNat := by
  obtain ⟨occurrenceRead, tokenRead, payloadRead, providerRead⟩ :=
    leaseFootprint_reads owner occurrenceOffset tokenOffset payloadOffset providerOffset
      occurrence token payload provider frame heap held
  apply actual_append_issues (ReadExpressions.environmentView environment)
    (ReadExpressions.fieldView layout heap) registry selected slots count owner occurrence token
    payload provider
  · simp only [ReadExpressions.environmentView, ownerRead, Option.map_some,
      ReadExpressions.scalar]
  · exact ReadExpressions.field_view_of_read layout heap owner "occurrence_id".toList
      occurrenceOffset (.u64 occurrence) occurrenceSelected occurrenceRead
  · exact ReadExpressions.field_view_of_read layout heap owner "resume_lease".toList
      tokenOffset (.u64 token) tokenSelected tokenRead
  · exact ReadExpressions.field_view_of_read layout heap owner "payload".toList
      payloadOffset (.ptr payload) payloadSelected payloadRead
  · exact ReadExpressions.field_view_of_read layout heap owner "provider".toList
      providerOffset (.ptr provider) providerSelected providerRead
  · exact representedOccurrence
  · exact representedPayload
  · exact representedProvider
  · exact sized
  · exact room
  · exact representedRows

/-- Every physical initializer execution preserves the owned fields and frame,
and its resulting row agrees with the source append and independent issuance.
No field-value oracle or whole-helper execution premise is assumed. -/
theorem actual_read_to_issued_registration (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment)
    (registry : Registry (Option Ptr) (Option Ptr))
    (selected : Handle (Option Ptr) (Option Ptr))
    (slots : List (Row (Option Ptr) (Option Ptr))) (count : UInt64)
    (owner : Ptr) (occurrence token : UInt64) (payload provider : Option Ptr)
    (occurrenceOffset tokenOffset payloadOffset providerOffset : Nat)
    (frame : Heap L → Prop)
    (ownerRead : environment "owned".toList = some (.ptr (some owner)))
    (occurrenceSelected : layout "occurrence_id".toList = some ⟨occurrenceOffset, .word64⟩)
    (tokenSelected : layout "resume_lease".toList = some ⟨tokenOffset, .word64⟩)
    (payloadSelected : layout "payload".toList = some ⟨payloadOffset, .pointer⟩)
    (providerSelected : layout "provider".toList = some ⟨providerOffset, .pointer⟩)
    (representedOccurrence : selected.row.occurrence = occurrence.toNat)
    (representedPayload : selected.row.payload = payload)
    (representedProvider : selected.row.provider = provider)
    (sized : slots.length < 2 ^ 64) (room : count.toNat < slots.length)
    (representedRows : registry.rows = slots.take count.toNat) :
    CTriple (leaseFootprint owner occurrenceOffset tokenOffset payloadOffset providerOffset
        occurrence token payload provider frame)
      (physicalRow layout environment leaseRhs)
      (fun row heap =>
        row = (registerIssued registry selected token.toNat).2.row ∧
        leaseFootprint owner occurrenceOffset tokenOffset payloadOffset providerOffset
          occurrence token payload provider frame heap ∧
        ∃ next after,
          body[10]?.bind (executeAppend (resolve (ReadExpressions.environmentView environment)
            (ReadExpressions.fieldView layout heap) slots count)) = some (next, after) ∧
          (registerIssued registry selected token.toNat).1.rows = after.take next.toNat ∧
          next.toNat = count.toNat + 1 ∧ after.length = slots.length ∧
          after.take count.toNat = slots.take count.toNat) := by
  apply triple_post _ (actual_row_owned_cells layout environment owner occurrence token
    payload provider occurrenceOffset tokenOffset payloadOffset providerOffset frame ownerRead
    occurrenceSelected tokenSelected payloadSelected providerSelected)
  intro row heap obtained
  obtain ⟨same, held⟩ := obtained
  obtain ⟨next, after, appended, rows, _, _, issued, increment, extent, retained⟩ :=
    actual_owned_append_issues layout environment heap registry selected slots count owner
      occurrence token payload provider occurrenceOffset tokenOffset payloadOffset providerOffset
      frame ownerRead occurrenceSelected tokenSelected payloadSelected providerSelected held
      representedOccurrence representedPayload representedProvider sized room representedRows
  refine ⟨?_, held, next, after, appended, rows, increment, extent, retained⟩
  rw [same, issued]
  cases selected with
  | mk store parent selectedRow =>
    cases selectedRow with
    | mk o t p r =>
      change o = occurrence.toNat at representedOccurrence
      change p = payload at representedPayload
      change r = provider at representedProvider
      subst o
      subst p
      subst r
      rfl

/-- Nonzero store/token and a fresh selected occurrence authorize the newly
issued handle after the same physical read. Lookup retains its scan cost. -/
theorem actual_read_authenticates_issued_handle (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment)
    (registry : Registry (Option Ptr) (Option Ptr))
    (selected : Handle (Option Ptr) (Option Ptr))
    (owner : Ptr) (occurrence token : UInt64) (payload provider : Option Ptr)
    (occurrenceOffset tokenOffset payloadOffset providerOffset : Nat)
    (frame : Heap L → Prop)
    (ownerRead : environment "owned".toList = some (.ptr (some owner)))
    (occurrenceSelected : layout "occurrence_id".toList = some ⟨occurrenceOffset, .word64⟩)
    (tokenSelected : layout "resume_lease".toList = some ⟨tokenOffset, .word64⟩)
    (payloadSelected : layout "payload".toList = some ⟨payloadOffset, .pointer⟩)
    (providerSelected : layout "provider".toList = some ⟨providerOffset, .pointer⟩)
    (live : registry.identity ≠ 0) (positive : token.toNat ≠ 0)
    (fresh : occurrence.toNat ∉ registry.rows.map Row.occurrence) :
    CTriple (leaseFootprint owner occurrenceOffset tokenOffset payloadOffset providerOffset
        occurrence token payload provider frame)
      (physicalRow layout environment leaseRhs)
      (fun row heap =>
        leaseFootprint owner occurrenceOffset tokenOffset payloadOffset providerOffset
          occurrence token payload provider frame heap ∧
        lookup (registerIssued registry { selected with row := row } token.toNat).1
          (registerIssued registry { selected with row := row } token.toNat).2 =
          (some registry.rows.length, registry.rows.length + 1)) := by
  apply triple_post _ (actual_row_owned_cells layout environment owner occurrence token
    payload provider occurrenceOffset tokenOffset payloadOffset providerOffset frame ownerRead
    occurrenceSelected tokenSelected payloadSelected providerSelected)
  intro row heap obtained
  obtain ⟨same, held⟩ := obtained
  refine ⟨held, registerIssued_lookup registry { selected with row := row } token.toNat
    live positive ?_⟩
  simpa only [same] using fresh

end PhysicalIssuance

namespace PhysicalControls

def priorRow : Row (Option Ptr) (Option Ptr) := ⟨8, 11, none, none⟩
def spareRow : Row (Option Ptr) (Option Ptr) := ⟨9, 12, some ⟨70, 0⟩, some ⟨71, 0⟩⟩
def selected : Handle (Option Ptr) (Option Ptr) :=
  ⟨87, 93, ⟨occurrence.toNat, 0, none, none⟩⟩
def registry : Registry (Option Ptr) (Option Ptr) := ⟨29, [priorRow]⟩
def slots : List (Row (Option Ptr) (Option Ptr)) := [priorRow, spareRow, spareRow]

/-- A nonempty live prefix receives the wide nullable row and retains its
unwritten spare tail. The abstract array view is read from a concrete heap. -/
theorem wide_nullable_owned_append :
    body[10]?.bind (executeAppend (resolve (ReadExpressions.environmentView environment)
      (ReadExpressions.fieldView layout liveHeap) slots 1)) =
        some ((2 : UInt64).toBitVec,
          [priorRow, ⟨occurrence.toNat, token.toNat, none, none⟩, spareRow]) := by
  rw [actual_append_statement]
  simp only [Option.bind_some]
  change executeAppend (resolve (ReadExpressions.environmentView environment)
    (ReadExpressions.fieldView layout liveHeap) slots 1) (site.statement leaseRhs) =
      WordStore.store slots (1 : UInt64).toBitVec
        ⟨occurrence.toNat, token.toNat, none, none⟩
  apply recognized_append_execution
  unfold resolve
  have actualRead := actual_row_owned_heap_view layout environment liveHeap owner occurrence
    token none none 0 1 2 3 (LiveBlock owner.block 4) rfl rfl rfl rfl rfl
      live_footprint_is_inhabited
  rw [if_pos rfl, actualRead]
  rfl

theorem read_row_issues_lookup_with_exact_scan :
    lookup (registerIssued registry selected token.toNat).1
      (registerIssued registry selected token.toNat).2 = (some 1, 2) := by
  apply registerIssued_lookup
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem truncated_occurrence_is_not_the_issued_handle :
    let issued := registerIssued registry selected token.toNat
    lookup issued.1 { issued.2 with row.occurrence := occurrence.toNat % (2 ^ 32) } =
      (none, 2) := by decide +kernel

theorem changed_payload_is_not_the_issued_handle :
    let issued := registerIssued registry selected token.toNat
    lookup issued.1 { issued.2 with row.payload := some ⟨70, 0⟩ } = (none, 2) := by
  decide +kernel

theorem changed_provider_is_not_the_issued_handle :
    let issued := registerIssued registry selected token.toNat
    lookup issued.1 { issued.2 with row.provider := some ⟨71, 0⟩ } = (none, 2) := by
  decide +kernel

theorem zero_token_does_not_authorize_the_issued_row :
    let issued := registerIssued registry selected token.toNat
    lookup issued.1 { issued.2 with row.token := 0 } = (none, 0) := by decide +kernel

end PhysicalControls

end Mettapedia.Languages.MeTTa.CeTTaNativeCost.IssuedReturnSource.TakeForResume.Append


namespace Mettapedia.Languages.MeTTa.CeTTaNativeCost

open Mettapedia.Machines.CMemory

/-- Frame allocation, child initialization and retirement are shared by
source constructors and scheduling wrappers. These named operations retain
their effects; physical allocation, lifetime and ABI laws are independent
provider obligations. A normally returned allocation is non-null. -/
structure FrameOperations where
  newFrame : Int32 → CProg CVal Ptr
  initializeChild : Ptr → CProg CVal Unit
  retireFrame : Ptr → CProg CVal Unit

end Mettapedia.Languages.MeTTa.CeTTaNativeCost

namespace Mettapedia.Languages.MeTTa.CeTTaNativeCost.NormalizeAtomConstructor

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

/-! The original constructor is parsed into independently authored syntax,
then its scoped execution is compared with the retained operation sequence.
Named allocation, capture, cleanup and automatic-storage providers keep their
separate ownership, native layout and lifetime obligations. -/

def names : TypeNames := ["PrimeEvalStackFrame", "Space", "Arena", "Atom", "int",
  "Bindings", "uint64_t", "OutcomeSet"].map String.toList

def ident (name : String) : CExpr := .identifier name.toList
def frameField (name : String) : CExpr := .field (ident "frame") name.toList true

def constructorSyntax : CDeclaratorFunction :=
  ⟨⟨"PrimeEvalStackFrame".toList, 1⟩,
    "prime_eval_stack_normalize_atom_frame_new".toList,
    [⟨⟨"Space".toList, false, [false]⟩, "s".toList⟩,
     ⟨⟨"Arena".toList, false, [false]⟩, "a".toList⟩,
     ⟨⟨"Atom".toList, false, [false]⟩, "atom".toList⟩,
     ⟨⟨"int".toList, false, []⟩, "fuel".toList⟩,
     ⟨⟨"Bindings".toList, true, [false]⟩, "env".toList⟩,
     ⟨⟨"uint64_t".toList, false, []⟩, "evaluator_id".toList⟩,
     ⟨⟨"OutcomeSet".toList, false, [false]⟩, "target".toList⟩],
    [.declare ⟨"PrimeEvalStackFrame".toList, 1⟩ "frame".toList
       (.call "prime_eval_stack_frame_new".toList [ident "PRIME_EVAL_STACK_FRAME_NORMALIZE_ATOM"]),
     .assign (frameField "space") (ident "s"),
     .assign (frameField "arena") (ident "a"),
     .assign (frameField "target") (ident "target"),
     .assign (frameField "atom") (ident "atom"),
     .assign (frameField "fuel") (ident "fuel"),
     .assign (frameField "evaluator_id") (ident "evaluator_id"),
     .effect (.call "outcome_set_init".toList [.unary .address (frameField "child")]),
     .assign (frameField "child_initialized") (.bool true),
     .declareArray ⟨"Atom".toList, 1⟩ "roots".toList none [ident "atom"],
     .branch (.unary .not (.call "prime_eval_stack_capture_value_support".toList
       [.unary .address (frameField "env"), ident "env", ident "roots", .unsignedInteger 1]))
       [.effect (.call "prime_eval_stack_frame_free".toList [ident "frame"]),
        .return (some .null)] [],
     .assign (frameField "env_initialized") (.bool true),
     .return (some (ident "frame"))]⟩

def source : String := "static PrimeEvalStackFrame *prime_eval_stack_normalize_atom_frame_new(\n    Space *s, Arena *a, Atom *atom, int fuel,\n    const Bindings *env, uint64_t evaluator_id,\n    OutcomeSet *target) {\n    PrimeEvalStackFrame *frame = prime_eval_stack_frame_new(\n        PRIME_EVAL_STACK_FRAME_NORMALIZE_ATOM);\n    frame->space = s;\n    frame->arena = a;\n    frame->target = target;\n    frame->atom = atom;\n    frame->fuel = fuel;\n    frame->evaluator_id = evaluator_id;\n    outcome_set_init(&frame->child);\n    frame->child_initialized = true;\n    Atom *roots[] = {atom};\n    if (!prime_eval_stack_capture_value_support(\n            &frame->env, env, roots, 1u)) {\n        prime_eval_stack_frame_free(frame);\n        return NULL;\n    }\n    frame->env_initialized = true;\n    return frame;\n}"

def characters : List Char := native_c_characters% "static PrimeEvalStackFrame *prime_eval_stack_normalize_atom_frame_new(\n    Space *s, Arena *a, Atom *atom, int fuel,\n    const Bindings *env, uint64_t evaluator_id,\n    OutcomeSet *target) {\n    PrimeEvalStackFrame *frame = prime_eval_stack_frame_new(\n        PRIME_EVAL_STACK_FRAME_NORMALIZE_ATOM);\n    frame->space = s;\n    frame->arena = a;\n    frame->target = target;\n    frame->atom = atom;\n    frame->fuel = fuel;\n    frame->evaluator_id = evaluator_id;\n    outcome_set_init(&frame->child);\n    frame->child_initialized = true;\n    Atom *roots[] = {atom};\n    if (!prime_eval_stack_capture_value_support(\n            &frame->env, env, roots, 1u)) {\n        prime_eval_stack_frame_free(frame);\n        return NULL;\n    }\n    frame->env_initialized = true;\n    return frame;\n}"

theorem characters_are_actual_source : source.toList = characters := by
  native_c_character_reflexivity

theorem actual_constructor_parses : declaratorFunctionText? names characters = some constructorSyntax := by
  native_c_parser_reflexivity


theorem original_source_recognized :
    declaratorFunctionText? names source.toList = some constructorSyntax := by
  rw [characters_are_actual_source]
  exact actual_constructor_parses

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

/-- Offsets name logical scalar cells in the admitted physical layout.
Their native byte representation, disjointness and live frame ownership
remain separate obligations. Embedded fields supply addresses, not loads. -/
structure FrameLayout where
  space : Nat
  arena : Nat
  target : Nat
  atom : Nat
  fuel : Nat
  evaluator : Nat
  child : Nat
  childInitialized : Nat
  environment : Nat
  environmentInitialized : Nat

def FrameLayout.fields (offsets : FrameLayout) : ReadExpressions.Layout := fun name =>
  if name = "space".toList then some ⟨offsets.space, .pointer⟩
  else if name = "arena".toList then some ⟨offsets.arena, .pointer⟩
  else if name = "target".toList then some ⟨offsets.target, .pointer⟩
  else if name = "atom".toList then some ⟨offsets.atom, .pointer⟩
  else if name = "fuel".toList then some ⟨offsets.fuel, .signedWord⟩
  else if name = "evaluator_id".toList then some ⟨offsets.evaluator, .word64⟩
  else if name = "child".toList then some ⟨offsets.child, .embedded⟩
  else if name = "child_initialized".toList then some ⟨offsets.childInitialized, .boolean⟩
  else if name = "env".toList then some ⟨offsets.environment, .embedded⟩
  else if name = "env_initialized".toList then some ⟨offsets.environmentInitialized, .boolean⟩
  else none

structure ConstructorInputs where
  space : Option Ptr
  arena : Option Ptr
  atom : Option Ptr
  environment : Option Ptr
  target : Option Ptr
  fuel : Int32
  evaluator : UInt64

def ConstructorInputs.locals (input : ConstructorInputs) : ReadExpressions.Environment := fun name =>
  if name = "s".toList then some (.ptr input.space)
  else if name = "a".toList then some (.ptr input.arena)
  else if name = "atom".toList then some (.ptr input.atom)
  else if name = "env".toList then some (.ptr input.environment)
  else if name = "target".toList then some (.ptr input.target)
  else if name = "fuel".toList then some (.i32 input.fuel)
  else if name = "evaluator_id".toList then some (.u64 input.evaluator)
  else if name = "PRIME_EVAL_STACK_FRAME_NORMALIZE_ATOM".toList then some (.i32 6)
  else none

/-- Each named provider retains its full physical operation contract.
The frame provider's normal return is non-null. Its allocator/zeroing/kind,
the source enumeration binding, capture postworld and automatic-region
lifetime are not established merely by this interface. -/
structure ConstructorOperations extends FrameOperations where
  capture : Ptr → Option Ptr → Ptr → UInt64 → CProg CVal Bool
  automatic : StatementBlock.AutomaticRegion

def ConstructorOperations.values (operations : ConstructorOperations) : ReadExpressions.Calls :=
  fun name arguments =>
    if name = "prime_eval_stack_frame_new".toList then
      match arguments with
      | [.i32 kind] => operations.newFrame kind >>= fun frame => pure (.ptr (some frame))
      | _ => CProg.undefined
    else if name = "prime_eval_stack_capture_value_support".toList then
      match arguments with
      | [.ptr (some destination), .ptr source, .ptr (some roots), .u32 count] =>
          operations.capture destination source roots (UInt64.ofNat count.toNat) >>=
            fun captured => pure (.bool captured)
      | _ => CProg.undefined
    else CProg.undefined

def ConstructorOperations.effects (operations : ConstructorOperations) : ReadExpressions.CallService Unit :=
  fun name arguments =>
    if name = "outcome_set_init".toList then
      match arguments with
      | [.ptr (some child)] => operations.initializeChild child
      | _ => CProg.undefined
    else if name = "prime_eval_stack_frame_free".toList then
      match arguments with
      | [.ptr (some frame)] => operations.retireFrame frame
      | _ => CProg.undefined
    else CProg.undefined

def ConstructorOperations.profile (operations : ConstructorOperations) : StatementBlock.Services where
  read := ReadExpressions.expressionWith operations.values
  initialValue := StatementBlock.objectInitialValue
  effect := EffectStatements.invoke operations.values operations.effects
  array := StatementBlock.arrayBinding
    (ReadExpressions.expressionWith operations.values) operations.automatic

def interpretedConstructor (operations : ConstructorOperations) (offsets : FrameLayout)
    (input : ConstructorInputs) : CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith operations.profile
    (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
    offsets.fields 0 13 input.locals constructorSyntax.body

/-- The independently written operation sequence has eight typed scalar
stores, two embedded-field addresses and one initialized root cell. Failure
retires the actual frame and returns null; success stores the environment
flag and returns that frame. Both local declarations restore their scopes.
Named service effects remain in the program, including through failure. -/
def constructorOperations (operations : ConstructorOperations) (offsets : FrameLayout)
    (input : ConstructorInputs) : CProg CVal ReadBlock.Result := do
  let frame ← operations.newFrame 6
  let environment := Function.update input.locals "frame".toList (some (.ptr (some frame)))
  let result ← do
    CProg.store (frame + offsets.space) (.ptr input.space)
    CProg.store (frame + offsets.arena) (.ptr input.arena)
    CProg.store (frame + offsets.target) (.ptr input.target)
    CProg.store (frame + offsets.atom) (.ptr input.atom)
    CProg.store (frame + offsets.fuel) (.i32 input.fuel)
    CProg.store (frame + offsets.evaluator) (.u64 input.evaluator)
    operations.initializeChild (frame + offsets.child)
    CProg.store (frame + offsets.childInitialized) (.bool true)
    let result ← operations.automatic "roots".toList 1 fun roots => do
      CProg.initializeCells roots [.ptr input.atom]
      let captured ← operations.capture (frame + offsets.environment) input.environment roots 1
      let localEnvironment := Function.update environment "roots".toList (some (.ptr (some roots)))
      if !captured then do
        operations.retireFrame frame
        pure (.finished (.returned localEnvironment (some (.ptr none))))
      else do
        CProg.store (frame + offsets.environmentInitialized) (.bool true)
        pure (.finished (.returned localEnvironment (some (.ptr (some frame)))))
    pure (ReadBlock.restore "roots".toList (environment "roots".toList) result)
  pure (ReadBlock.restore "frame".toList (input.locals "frame".toList) result)

def frameEnvironment (input : ConstructorInputs) (frame : Ptr) : ReadExpressions.Environment :=
  Function.update input.locals "frame".toList (some (.ptr (some frame)))

theorem frame_environment_lookup (input : ConstructorInputs) (frame : Ptr) :
    frameEnvironment input frame "frame".toList = some (.ptr (some frame)) := by
  rw [frameEnvironment, Function.update_self]

theorem identifier_reads_resolved_slot (operations : ConstructorOperations)
    (offsets : FrameLayout) (environment : ReadExpressions.Environment)
    (name : String) (value : CVal) (known : environment name.toList = some value) :
    ReadExpressions.expressionWith operations.values offsets.fields environment (ident name) = pure value := by
  simp only [ident, ReadExpressions.expressionWith_equation, known, ReadExpressions.resolved]

theorem free_call_keeps_frame (operations : ConstructorOperations)
    (offsets : FrameLayout) (environment : ReadExpressions.Environment)
    (frame : Ptr) (known : environment "frame".toList = some (.ptr (some frame))) :
    operations.profile.effect offsets.fields environment
      (.call "prime_eval_stack_frame_free".toList [ident "frame"]) = operations.retireFrame frame := by
  simp only [ConstructorOperations.profile, EffectStatements.invoke_equation,
    ReadExpressions.argumentsWith_equation, identifier_reads_resolved_slot operations offsets environment "frame" _ known,
    Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  rfl

theorem failure_body_keeps_cleanup_and_return (operations : ConstructorOperations)
    (offsets : FrameLayout) (environment : ReadExpressions.Environment)
    (frame : Ptr) (known : environment "frame".toList = some (.ptr (some frame))) :
    StatementBlock.executeWith operations.profile
      (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
      offsets.fields 0 2 environment
      [.effect (.call "prime_eval_stack_frame_free".toList [ident "frame"]), .return (some .null)] =
      (operations.retireFrame frame >>= fun _ =>
        pure (.finished (.returned environment (some (.ptr none))))) := by
  rw [StatementBlock.executeWith_equation]
  dsimp only
  rw [free_call_keeps_frame operations offsets environment frame known]
  rfl

theorem field_assignment_keeps_typed_write (operations : ConstructorOperations)
    (offsets : FrameLayout) (environment : ReadExpressions.Environment)
    (frame : Ptr) (known : environment "frame".toList = some (.ptr (some frame)))
    (name : String) (offset : Nat) (rhs : CExpr) (value : CVal)
    (selected : offsets.fields name.toList = some ⟨offset, ReadExpressions.valueKind value⟩)
    (actual : ReadExpressions.expressionWith operations.values offsets.fields environment rhs = pure value) :
    StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values)
      offsets.fields environment (.assign (frameField name) rhs) =
      (CProg.store (frame + offset) value >>= fun _ => pure environment) := by
  simp only [StatementBlock.fieldAssignment, frameField,
    identifier_reads_resolved_slot operations offsets environment "frame" _ known,
    actual, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  rw [ReadExpressions.field_store_retains_actual_value offsets.fields frame name.toList offset value selected]

theorem field_address_reads_embedded_offset (operations : ConstructorOperations)
    (offsets : FrameLayout) (environment : ReadExpressions.Environment)
    (frame : Ptr) (known : environment "frame".toList = some (.ptr (some frame)))
    (name : String) (offset : Nat) (kind : ReadExpressions.FieldKind)
    (selected : offsets.fields name.toList = some ⟨offset, kind⟩) :
    ReadExpressions.expressionWith operations.values offsets.fields environment
      (.unary .address (frameField name)) = pure (.ptr (some (frame + offset))) := by
  rw [ReadExpressions.expressionWith_equation]
  dsimp only [frameField]
  rw [identifier_reads_resolved_slot operations offsets environment "frame" _ known]
  simp only [Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  rw [ReadExpressions.field_address_retains_offset offsets.fields frame name.toList offset kind selected]
  rfl

theorem successful_tail_keeps_final_flag_and_frame (operations : ConstructorOperations)
    (offsets : FrameLayout) (environment : ReadExpressions.Environment)
    (frame : Ptr) (known : environment "frame".toList = some (.ptr (some frame))) :
    StatementBlock.executeWith operations.profile
      (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
      offsets.fields 0 2 environment (constructorSyntax.body.drop 11) =
      (CProg.store (frame + offsets.environmentInitialized) (.bool true) >>= fun _ =>
        pure (.finished (.returned environment (some (.ptr (some frame)))))) := by
  change StatementBlock.executeWith operations.profile
      (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
      offsets.fields 0 2 environment
      [.assign (frameField "env_initialized") (.bool true), .return (some (ident "frame"))] = _
  rw [StatementBlock.executeWith_equation]
  dsimp only
  rw [field_assignment_keeps_typed_write operations offsets environment frame known
    "env_initialized" offsets.environmentInitialized (.bool true) (.bool true) (by rfl) (by rfl)]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext ignored
  rw [StatementBlock.executeWith_equation]
  dsimp only [ConstructorOperations.profile]
  rw [identifier_reads_resolved_slot operations offsets environment "frame" _ known]
  rfl

def captureExpression : CExpr :=
  .call "prime_eval_stack_capture_value_support".toList
    [.unary .address (frameField "env"), ident "env", ident "roots", .unsignedInteger 1]

theorem capture_call_keeps_resolved_inputs (operations : ConstructorOperations)
    (offsets : FrameLayout) (environment : ReadExpressions.Environment)
    (frame roots : Ptr) (source : Option Ptr)
    (knownFrame : environment "frame".toList = some (.ptr (some frame)))
    (knownSource : environment "env".toList = some (.ptr source))
    (knownRoots : environment "roots".toList = some (.ptr (some roots))) :
    ReadExpressions.expressionWith operations.values offsets.fields environment captureExpression =
      (operations.capture (frame + offsets.environment) source roots 1 >>= fun captured => pure (.bool captured)) := by
  rw [captureExpression, ReadExpressions.call_retains_ordered_arguments]
  simp only [ReadExpressions.argumentsWith_equation,
    field_address_reads_embedded_offset operations offsets environment frame knownFrame
      "env" offsets.environment .embedded (by rfl),
    identifier_reads_resolved_slot operations offsets environment "env" _ knownSource,
    identifier_reads_resolved_slot operations offsets environment "roots" _ knownRoots,
    Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  rfl

theorem capture_test_keeps_resolved_inputs (operations : ConstructorOperations)
    (offsets : FrameLayout) (environment : ReadExpressions.Environment)
    (frame roots : Ptr) (source : Option Ptr)
    (knownFrame : environment "frame".toList = some (.ptr (some frame)))
    (knownSource : environment "env".toList = some (.ptr source))
    (knownRoots : environment "roots".toList = some (.ptr (some roots))) :
    ReadExpressions.expressionWith operations.values offsets.fields environment
      (.unary .not captureExpression) =
      (operations.capture (frame + offsets.environment) source roots 1 >>= fun captured => pure (.bool (!captured))) := by
  rw [ReadExpressions.expressionWith_equation]
  dsimp only
  rw [capture_call_keeps_resolved_inputs operations offsets environment frame roots source knownFrame knownSource knownRoots]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, ReadExpressions.truth]


theorem capture_branch_keeps_both_outcomes (operations : ConstructorOperations)
    (offsets : FrameLayout) (environment : ReadExpressions.Environment)
    (frame roots : Ptr) (source : Option Ptr)
    (knownFrame : environment "frame".toList = some (.ptr (some frame)))
    (knownSource : environment "env".toList = some (.ptr source))
    (knownRoots : environment "roots".toList = some (.ptr (some roots))) :
    StatementBlock.executeWith operations.profile
      (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
      offsets.fields 0 3 environment (constructorSyntax.body.drop 10) =
      (operations.capture (frame + offsets.environment) source roots 1 >>= fun captured =>
        if !captured then do
          operations.retireFrame frame
          pure (.finished (.returned environment (some (.ptr none))))
        else do
          CProg.store (frame + offsets.environmentInitialized) (.bool true)
          pure (.finished (.returned environment (some (.ptr (some frame)))))) := by
  change StatementBlock.executeWith operations.profile
      (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
      offsets.fields 0 3 environment
      [.branch (.unary .not captureExpression)
        [.effect (.call "prime_eval_stack_frame_free".toList [ident "frame"]), .return (some .null)] [],
       .assign (frameField "env_initialized") (.bool true), .return (some (ident "frame"))] = _
  rw [StatementBlock.executeWith_equation]
  dsimp only
  have reads : operations.profile.read offsets.fields environment (.unary .not captureExpression) =
      (operations.capture (frame + offsets.environment) source roots 1 >>= fun captured => pure (.bool (!captured))) :=
    capture_test_keeps_resolved_inputs operations offsets environment frame roots source knownFrame knownSource knownRoots
  rw [reads]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, ReadExpressions.truth]
  congr 1
  funext captured
  cases captured with
  | false =>
      simp only [Bool.not_false, ↓reduceIte]
      rw [failure_body_keeps_cleanup_and_return operations offsets environment frame knownFrame]
      simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        StatementBlock.executeWith_equation, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, ReadBlock.resume]
      exact successful_tail_keeps_final_flag_and_frame operations offsets environment frame knownFrame

theorem automatic_roots_keeps_initializer (operations : ConstructorOperations)
    (offsets : FrameLayout) (environment : ReadExpressions.Environment)
    (atom : Option Ptr) (knownAtom : environment "atom".toList = some (.ptr atom))
    (continuation : ReadExpressions.Environment → CProg CVal ReadBlock.Result) :
    operations.profile.array offsets.fields environment ⟨"Atom".toList, 1⟩
      "roots".toList none [ident "atom"] continuation =
      operations.automatic "roots".toList 1 (fun roots => do
        CProg.initializeCells roots [.ptr atom]
        continuation (Function.update environment "roots".toList (some (.ptr (some roots))))) := by
  dsimp only [ConstructorOperations.profile, StatementBlock.arrayBinding]
  simp only [List.mapM_cons, List.mapM_nil,
    identifier_reads_resolved_slot operations offsets environment "atom" _ knownAtom,
    StatementBlock.nullable_object_declaration_retains_value ⟨"Atom".toList, 1⟩ atom (by decide),
    Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, List.length_cons, List.length_nil]


theorem automatic_tail_keeps_cells_and_scope (operations : ConstructorOperations)
    (offsets : FrameLayout) (environment : ReadExpressions.Environment)
    (frame : Ptr) (atom source : Option Ptr)
    (knownFrame : environment "frame".toList = some (.ptr (some frame)))
    (knownAtom : environment "atom".toList = some (.ptr atom))
    (knownSource : environment "env".toList = some (.ptr source)) :
    StatementBlock.executeWith operations.profile
      (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
      offsets.fields 0 4 environment (constructorSyntax.body.drop 9) =
      (operations.automatic "roots".toList 1 (fun roots => do
        CProg.initializeCells roots [.ptr atom]
        let captured ← operations.capture (frame + offsets.environment) source roots 1
        let localEnvironment := Function.update environment "roots".toList (some (.ptr (some roots)))
        if !captured then do
          operations.retireFrame frame
          pure (.finished (.returned localEnvironment (some (.ptr none))))
        else do
          CProg.store (frame + offsets.environmentInitialized) (.bool true)
          pure (.finished (.returned localEnvironment (some (.ptr (some frame)))))) >>= fun result =>
        pure (ReadBlock.restore "roots".toList (environment "roots".toList) result)) := by
  change StatementBlock.executeWith operations.profile
      (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
      offsets.fields 0 4 environment
      (.declareArray ⟨"Atom".toList, 1⟩ "roots".toList none [ident "atom"] ::
        constructorSyntax.body.drop 10) = _
  rw [StatementBlock.executeWith_equation]
  dsimp only
  rw [automatic_roots_keeps_initializer operations offsets environment atom knownAtom]
  congr 1
  congr 1
  funext roots
  simp only [Prog.bind_eq]
  congr 1
  funext ignored
  apply capture_branch_keeps_both_outcomes operations offsets
    (Function.update environment "roots".toList (some (.ptr (some roots)))) frame roots source
  · change environment "frame".toList = some (.ptr (some frame))
    exact knownFrame
  · change environment "env".toList = some (.ptr source)
    exact knownSource
  · rw [Function.update_self]

theorem child_call_keeps_embedded_address (operations : ConstructorOperations)
    (offsets : FrameLayout) (environment : ReadExpressions.Environment)
    (frame : Ptr) (knownFrame : environment "frame".toList = some (.ptr (some frame))) :
    operations.profile.effect offsets.fields environment
      (.call "outcome_set_init".toList [.unary .address (frameField "child")]) =
      operations.initializeChild (frame + offsets.child) := by
  simp only [ConstructorOperations.profile, EffectStatements.invoke_equation,
    ReadExpressions.argumentsWith_equation,
    field_address_reads_embedded_offset operations offsets environment frame knownFrame
      "child" offsets.child .embedded (by rfl),
    Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  rfl

theorem assigned_head_keeps_continuation (operations : ConstructorOperations)
    (offsets : FrameLayout) (environment : ReadExpressions.Environment)
    (frame : Ptr) (knownFrame : environment "frame".toList = some (.ptr (some frame)))
    (name : String) (offset : Nat) (rhs : CExpr) (value : CVal)
    (selected : offsets.fields name.toList = some ⟨offset, ReadExpressions.valueKind value⟩)
    (actual : ReadExpressions.expressionWith operations.values offsets.fields environment rhs = pure value)
    (fuel : Nat) (rest : List CStatement) :
    StatementBlock.executeWith operations.profile
      (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
      offsets.fields 0 (fuel + 1) environment (.assign (frameField name) rhs :: rest) =
      (CProg.store (frame + offset) value >>= fun _ =>
        StatementBlock.executeWith operations.profile
          (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
          offsets.fields 0 fuel environment rest) := by
  rw [StatementBlock.executeWith_equation]
  dsimp only
  rw [field_assignment_keeps_typed_write operations offsets environment frame knownFrame name offset rhs value selected actual]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]

theorem child_initialization_keeps_suffix (operations : ConstructorOperations)
    (offsets : FrameLayout) (environment : ReadExpressions.Environment)
    (frame : Ptr) (knownFrame : environment "frame".toList = some (.ptr (some frame))) :
    StatementBlock.executeWith operations.profile
      (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
      offsets.fields 0 6 environment (constructorSyntax.body.drop 7) =
      (operations.initializeChild (frame + offsets.child) >>= fun _ =>
        CProg.store (frame + offsets.childInitialized) (.bool true) >>= fun _ =>
        StatementBlock.executeWith operations.profile
          (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
          offsets.fields 0 4 environment (constructorSyntax.body.drop 9)) := by
  change StatementBlock.executeWith operations.profile
      (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
      offsets.fields 0 6 environment
      (.effect (.call "outcome_set_init".toList [.unary .address (frameField "child")]) ::
        .assign (frameField "child_initialized") (.bool true) :: constructorSyntax.body.drop 9) = _
  rw [StatementBlock.executeWith_equation]
  dsimp only
  rw [child_call_keeps_embedded_address operations offsets environment frame knownFrame]
  congr 1
  funext ignored
  exact assigned_head_keeps_continuation operations offsets environment frame knownFrame
    "child_initialized" offsets.childInitialized (.bool true) (.bool true) (by rfl) (by rfl) 4 _

theorem constructor_fields_keep_actual_inputs (operations : ConstructorOperations)
    (offsets : FrameLayout) (input : ConstructorInputs) (frame : Ptr) :
    StatementBlock.executeWith operations.profile
      (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
      offsets.fields 0 12 (frameEnvironment input frame) (constructorSyntax.body.drop 1) =
      (do
        CProg.store (frame + offsets.space) (.ptr input.space)
        CProg.store (frame + offsets.arena) (.ptr input.arena)
        CProg.store (frame + offsets.target) (.ptr input.target)
        CProg.store (frame + offsets.atom) (.ptr input.atom)
        CProg.store (frame + offsets.fuel) (.i32 input.fuel)
        CProg.store (frame + offsets.evaluator) (.u64 input.evaluator)
        StatementBlock.executeWith operations.profile
          (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
          offsets.fields 0 6 (frameEnvironment input frame) (constructorSyntax.body.drop 7)) := by
  change StatementBlock.executeWith operations.profile
      (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
      offsets.fields 0 12 (frameEnvironment input frame)
      (.assign (frameField "space") (ident "s") ::
       .assign (frameField "arena") (ident "a") ::
       .assign (frameField "target") (ident "target") ::
       .assign (frameField "atom") (ident "atom") ::
       .assign (frameField "fuel") (ident "fuel") ::
       .assign (frameField "evaluator_id") (ident "evaluator_id") :: constructorSyntax.body.drop 7) = _
  rw [assigned_head_keeps_continuation operations offsets (frameEnvironment input frame) frame
    (frame_environment_lookup input frame) "space" offsets.space (ident "s") (.ptr input.space) (by rfl)
    (identifier_reads_resolved_slot operations offsets (frameEnvironment input frame) "s" (.ptr input.space) (by rfl)) 11 _]
  rw [assigned_head_keeps_continuation operations offsets (frameEnvironment input frame) frame
    (frame_environment_lookup input frame) "arena" offsets.arena (ident "a") (.ptr input.arena) (by rfl)
    (identifier_reads_resolved_slot operations offsets (frameEnvironment input frame) "a" (.ptr input.arena) (by rfl)) 10 _]
  rw [assigned_head_keeps_continuation operations offsets (frameEnvironment input frame) frame
    (frame_environment_lookup input frame) "target" offsets.target (ident "target") (.ptr input.target) (by rfl)
    (identifier_reads_resolved_slot operations offsets (frameEnvironment input frame) "target" (.ptr input.target) (by rfl)) 9 _]
  rw [assigned_head_keeps_continuation operations offsets (frameEnvironment input frame) frame
    (frame_environment_lookup input frame) "atom" offsets.atom (ident "atom") (.ptr input.atom) (by rfl)
    (identifier_reads_resolved_slot operations offsets (frameEnvironment input frame) "atom" (.ptr input.atom) (by rfl)) 8 _]
  rw [assigned_head_keeps_continuation operations offsets (frameEnvironment input frame) frame
    (frame_environment_lookup input frame) "fuel" offsets.fuel (ident "fuel") (.i32 input.fuel) (by rfl)
    (identifier_reads_resolved_slot operations offsets (frameEnvironment input frame) "fuel" (.i32 input.fuel) (by rfl)) 7 _]
  rw [assigned_head_keeps_continuation operations offsets (frameEnvironment input frame) frame
    (frame_environment_lookup input frame) "evaluator_id" offsets.evaluator (ident "evaluator_id") (.u64 input.evaluator) (by rfl)
    (identifier_reads_resolved_slot operations offsets (frameEnvironment input frame) "evaluator_id" (.u64 input.evaluator) (by rfl)) 6 _]

theorem allocation_call_keeps_original_kind (operations : ConstructorOperations)
    (offsets : FrameLayout) (input : ConstructorInputs) :
    ReadExpressions.expressionWith operations.values offsets.fields input.locals
      (.call "prime_eval_stack_frame_new".toList [ident "PRIME_EVAL_STACK_FRAME_NORMALIZE_ATOM"]) =
      (operations.newFrame 6 >>= fun frame => pure (.ptr (some frame))) := by
  rw [ReadExpressions.call_retains_ordered_arguments]
  simp only [ReadExpressions.argumentsWith_equation,
    identifier_reads_resolved_slot operations offsets input.locals
      "PRIME_EVAL_STACK_FRAME_NORMALIZE_ATOM" (.i32 6) (by rfl),
    Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  rfl


theorem original_constructor_executes_declared_operations
    (operations : ConstructorOperations) (offsets : FrameLayout) (input : ConstructorInputs) :
    interpretedConstructor operations offsets input = constructorOperations operations offsets input := by
  change StatementBlock.executeWith operations.profile
      (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
      offsets.fields 0 13 input.locals
      (.declare ⟨"PrimeEvalStackFrame".toList, 1⟩ "frame".toList
        (.call "prime_eval_stack_frame_new".toList [ident "PRIME_EVAL_STACK_FRAME_NORMALIZE_ATOM"]) ::
        constructorSyntax.body.drop 1) = _
  rw [StatementBlock.executeWith_equation]
  dsimp only
  have allocation : operations.profile.read offsets.fields input.locals
      (.call "prime_eval_stack_frame_new".toList [ident "PRIME_EVAL_STACK_FRAME_NORMALIZE_ATOM"]) =
      (operations.newFrame 6 >>= fun frame => pure (.ptr (some frame))) :=
    allocation_call_keeps_original_kind operations offsets input
  rw [allocation]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  unfold constructorOperations
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext frame
  have declaration : operations.profile.initialValue ⟨"PrimeEvalStackFrame".toList, 1⟩
      (.ptr (some frame)) = pure (.ptr (some frame)) :=
    StatementBlock.nullable_object_declaration_retains_value ⟨"PrimeEvalStackFrame".toList, 1⟩ (some frame) (by decide)
  rw [declaration]
  simp only [Prog.pure_eq, Prog.ret_bind]
  change (StatementBlock.executeWith operations.profile
      (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
      offsets.fields 0 12 (frameEnvironment input frame) (constructorSyntax.body.drop 1) >>=
        fun result => pure (ReadBlock.restore "frame".toList (input.locals "frame".toList) result)) = _
  rw [constructor_fields_keep_actual_inputs operations offsets input frame]
  rw [child_initialization_keeps_suffix operations offsets (frameEnvironment input frame) frame
    (frame_environment_lookup input frame)]
  rw [automatic_tail_keeps_cells_and_scope operations offsets (frameEnvironment input frame) frame
    input.atom input.environment (frame_environment_lookup input frame) (by rfl) (by rfl)]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl

/-- Parsing the pinned original source and then executing its body gives the
same operation sequence. This composition retains the named provider
obligations; it does not certify their compiled implementations. -/
theorem original_source_executes_declared_operations
    (operations : ConstructorOperations) (offsets : FrameLayout) (input : ConstructorInputs) :
    (declaratorFunctionText? names source.toList).map (fun parsed =>
      StatementBlock.executeWith operations.profile
        (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
        offsets.fields 0 13 input.locals parsed.body) =
        some (constructorOperations operations offsets input) := by
  rw [original_source_recognized, Option.map_some]
  exact congrArg some (original_constructor_executes_declared_operations operations offsets input)

/-- The admitted source catalogue retains the native unsigned root count.
A signed value is not silently repaired to the declared call signature. -/
theorem signed_capture_count_rejected (operations : ConstructorOperations)
    (destination roots : Ptr) (source : Option Ptr) :
    operations.values "prime_eval_stack_capture_value_support".toList
      [.ptr (some destination), .ptr source, .ptr (some roots), .i32 1] =
        CProg.undefined := by rfl

/-- A one-element automatic array needs a live storage address. Null does
not stand in for that region; the lifetime premise remains explicit. -/
theorem missing_root_storage_rejected (operations : ConstructorOperations)
    (destination : Ptr) (source : Option Ptr) :
    operations.values "prime_eval_stack_capture_value_support".toList
      [.ptr (some destination), .ptr source, .ptr none, .u32 1] =
        CProg.undefined := by rfl

theorem unsigned_frame_kind_rejected (operations : ConstructorOperations) :
    operations.values "prime_eval_stack_frame_new".toList [.u32 6] =
      CProg.undefined := by rfl

theorem extra_retirement_operand_rejected (operations : ConstructorOperations)
    (frame extra : Ptr) :
    operations.effects "prime_eval_stack_frame_free".toList
      [.ptr (some frame), .ptr (some extra)] = CProg.undefined := by rfl

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ReadExpressions

/-- The same authored storage and service operations return only the caller's
locals. Temporary frame/root bindings leave scope; success retains the frame
pointer as a value, and capture refusal retains cleanup and null return. -/
def constructorWithCallerLocals (operations : ConstructorOperations) (offsets : FrameLayout)
    (input : ConstructorInputs) : CProg CVal ReadBlock.Result := do
  let frame ← operations.newFrame 6
  CProg.store (frame + offsets.space) (.ptr input.space)
  CProg.store (frame + offsets.arena) (.ptr input.arena)
  CProg.store (frame + offsets.target) (.ptr input.target)
  CProg.store (frame + offsets.atom) (.ptr input.atom)
  CProg.store (frame + offsets.fuel) (.i32 input.fuel)
  CProg.store (frame + offsets.evaluator) (.u64 input.evaluator)
  operations.initializeChild (frame + offsets.child)
  CProg.store (frame + offsets.childInitialized) (.bool true)
  operations.automatic "roots".toList 1 fun roots => do
    CProg.initializeCells roots [.ptr input.atom]
    let captured ← operations.capture (frame + offsets.environment) input.environment roots 1
    if !captured then do
      operations.retireFrame frame
      pure (.finished (.returned input.locals (some (.ptr none))))
    else do
      CProg.store (frame + offsets.environmentInitialized) (.bool true)
      pure (.finished (.returned input.locals (some (.ptr (some frame)))))

theorem constructor_operations_restore_caller_locals
    (operations : ConstructorOperations) (offsets : FrameLayout) (input : ConstructorInputs)
    (lawful : StatementBlock.AutomaticRegion.PureReadoutLaw operations.automatic) :
    constructorOperations operations offsets input =
      constructorWithCallerLocals operations offsets input := by
  unfold constructorOperations constructorWithCallerLocals
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext frame
  let environment := Function.update input.locals "frame".toList (some (.ptr (some frame)))
  let readout := fun result => ReadBlock.restore "frame".toList (input.locals "frame".toList)
    (ReadBlock.restore "roots".toList (environment "roots".toList) result)
  have fusion := lawful "roots".toList 1
    (fun roots => do
      CProg.initializeCells roots [.ptr input.atom]
      let captured ← operations.capture (frame + offsets.environment) input.environment roots 1
      let localEnvironment := Function.update environment "roots".toList (some (.ptr (some roots)))
      if !captured then do
        operations.retireFrame frame
        pure (.finished (.returned localEnvironment (some (.ptr none))))
      else do
        CProg.store (frame + offsets.environmentInitialized) (.bool true)
        pure (.finished (.returned localEnvironment (some (.ptr (some frame)))))) readout
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq] at fusion
  rw [fusion]
  iterate 8 (congr 1; funext ignored)
  congr 1
  funext roots
  congr 1
  funext ignored
  congr 1
  funext captured
  have exit (last : CProg CVal Unit) (value : Option CVal) :
      ((last >>= fun _ => pure (ReadBlock.Result.finished
        (ReadBlock.Flow.returned
          (Function.update environment "roots".toList (some (.ptr (some roots)))) value))) >>=
        fun result => pure (readout result)) =
          (last >>= fun _ => pure (ReadBlock.Result.finished (ReadBlock.Flow.returned input.locals value))) := by
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
    congr 1
    funext ignored
    apply congrArg Prog.ret
    exact ReadBlock.returned_nested_declarations_restore_scope input.locals
      "frame".toList "roots".toList (some (.ptr (some frame))) (some (.ptr (some roots))) value
  cases captured with
  | false => exact exit (operations.retireFrame frame) (some (.ptr none))
  | true =>
      exact exit (CProg.store (frame + offsets.environmentInitialized) (.bool true))
        (some (.ptr (some frame)))

theorem original_constructor_restores_caller_locals
    (operations : ConstructorOperations) (offsets : FrameLayout) (input : ConstructorInputs)
    (lawful : StatementBlock.AutomaticRegion.PureReadoutLaw operations.automatic) :
    interpretedConstructor operations offsets input =
      constructorWithCallerLocals operations offsets input := by
  rw [original_constructor_executes_declared_operations]
  exact constructor_operations_restore_caller_locals operations offsets input lawful

/-- Parsing and executing the pinned source retains the caller's local scope
under the same proved pure-readout contract. Storage lifetime and native byte
layout remain separate from local-name restoration. -/
theorem original_source_restores_caller_locals
    (operations : ConstructorOperations) (offsets : FrameLayout) (input : ConstructorInputs)
    (lawful : StatementBlock.AutomaticRegion.PureReadoutLaw operations.automatic) :
    (Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.declaratorFunctionText? names source.toList).map (fun parsed =>
      StatementBlock.executeWith operations.profile
        (StatementBlock.fieldAssignment (ReadExpressions.expressionWith operations.values))
        offsets.fields 0 13 input.locals parsed.body) =
        some (constructorWithCallerLocals operations offsets input) := by
  rw [original_source_executes_declared_operations]
  exact congrArg some (constructor_operations_restore_caller_locals operations offsets input lawful)

/-- The entry/body/exit construction supplies the readout premise; arbitrary
entry and exit effects keep their order. It does not infer the native lifetime
contract merely from the supplied services' types. -/
theorem bracket_constructor_restores_caller_locals
    (operations : ConstructorOperations) (offsets : FrameLayout) (input : ConstructorInputs)
    (enter : GSLT.LanguageDef.NativeOps.NativeC.Name → Nat → CProg CVal Ptr)
    (leave : GSLT.LanguageDef.NativeOps.NativeC.Name → Ptr → Nat → CProg CVal Unit) :
    interpretedConstructor { operations with automatic := StatementBlock.AutomaticRegion.bracket enter leave }
        offsets input =
      constructorWithCallerLocals { operations with automatic := StatementBlock.AutomaticRegion.bracket enter leave }
        offsets input :=
  original_constructor_restores_caller_locals _ offsets input
    (StatementBlock.AutomaticRegion.bracket_pure_readout enter leave)

end Mettapedia.Languages.MeTTa.CeTTaNativeCost.NormalizeAtomConstructor

namespace Mettapedia.Languages.MeTTa.CeTTaNativeCost.Scheduling

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

/-- CALL extends the common constructor request with its actual type,
preservation, strict-index and optional seed arguments. -/
structure CallInputs extends NormalizeAtomConstructor.ConstructorInputs where
  expectedType : Option Ptr
  preserve : Bool
  strictIndex : Int32
  seed : Option Ptr

def names : TypeNames := NormalizeAtomConstructor.names ++ ["bool".toList]
def ident (name : String) : CExpr := .identifier name.toList

def callSyntax : CDeclaratorFunction :=
  ⟨⟨"bool".toList, 0⟩, "prime_eval_stack_schedule_call".toList,
   [⟨⟨"Space".toList, false, [false]⟩, "s".toList⟩,
    ⟨⟨"Arena".toList, false, [false]⟩, "a".toList⟩,
    ⟨⟨"Atom".toList, false, [false]⟩, "atom".toList⟩,
    ⟨⟨"Atom".toList, false, [false]⟩, "etype".toList⟩,
    ⟨⟨"int".toList, false, []⟩, "fuel".toList⟩,
    ⟨⟨"bool".toList, false, []⟩, "preserve_bindings".toList⟩,
    ⟨⟨"int".toList, false, []⟩, "strict_ready_argument".toList⟩,
    ⟨⟨"Bindings".toList, true, [false]⟩, "dynamic_env".toList⟩,
    ⟨⟨"Bindings".toList, true, [false]⟩, "seed_env".toList⟩,
    ⟨⟨"uint64_t".toList, false, []⟩, "evaluator_id".toList⟩,
    ⟨⟨"OutcomeSet".toList, false, [false]⟩, "target".toList⟩],
   [.return (some (.call "prime_eval_stack_set_task".toList
     [ident "PRIME_EVAL_STACK_TASK_CALL", ident "s", ident "a", ident "atom",
      ident "etype", ident "fuel", ident "preserve_bindings", ident "strict_ready_argument",
      ident "target", ident "dynamic_env", ident "seed_env", ident "evaluator_id"]))]⟩

def callSource : String := "static bool prime_eval_stack_schedule_call(\n    Space *s, Arena *a, Atom *atom, Atom *etype, int fuel,\n    bool preserve_bindings, int strict_ready_argument,\n    const Bindings *dynamic_env, const Bindings *seed_env,\n    uint64_t evaluator_id, OutcomeSet *target) {\n    return prime_eval_stack_set_task(\n        PRIME_EVAL_STACK_TASK_CALL, s, a, atom, etype, fuel,\n        preserve_bindings, strict_ready_argument, target,\n        dynamic_env, seed_env, evaluator_id);\n}"

def callCharacters : List Char := native_c_characters% "static bool prime_eval_stack_schedule_call(\n    Space *s, Arena *a, Atom *atom, Atom *etype, int fuel,\n    bool preserve_bindings, int strict_ready_argument,\n    const Bindings *dynamic_env, const Bindings *seed_env,\n    uint64_t evaluator_id, OutcomeSet *target) {\n    return prime_eval_stack_set_task(\n        PRIME_EVAL_STACK_TASK_CALL, s, a, atom, etype, fuel,\n        preserve_bindings, strict_ready_argument, target,\n        dynamic_env, seed_env, evaluator_id);\n}"

theorem call_characters_are_source : callSource.toList = callCharacters := by
  native_c_character_reflexivity

theorem original_call_parses : declaratorFunctionText? names callCharacters = some callSyntax := by
  native_c_parser_reflexivity

theorem original_call_source_recognized :
    declaratorFunctionText? names callSource.toList = some callSyntax := by
  rw [call_characters_are_source]
  exact original_call_parses

def CallInputs.locals (input : CallInputs) : ReadExpressions.Environment := fun name =>
  if name = "s".toList then some (.ptr input.space)
  else if name = "a".toList then some (.ptr input.arena)
  else if name = "atom".toList then some (.ptr input.atom)
  else if name = "etype".toList then some (.ptr input.expectedType)
  else if name = "fuel".toList then some (.i32 input.fuel)
  else if name = "preserve_bindings".toList then some (.bool input.preserve)
  else if name = "strict_ready_argument".toList then some (.i32 input.strictIndex)
  else if name = "target".toList then some (.ptr input.target)
  else if name = "dynamic_env".toList then some (.ptr input.environment)
  else if name = "seed_env".toList then some (.ptr input.seed)
  else if name = "evaluator_id".toList then some (.u64 input.evaluator)
  else if name = "PRIME_EVAL_STACK_TASK_CALL".toList then some (.i32 1)
  else none

/-- Independent typed forwarding specification, including the target-before-
environments position and every supplied signed/nullable argument. -/
def CallInputs.arguments (input : CallInputs) : List CVal :=
  [.i32 1, .ptr input.space, .ptr input.arena, .ptr input.atom, .ptr input.expectedType,
   .i32 input.fuel, .bool input.preserve, .i32 input.strictIndex, .ptr input.target,
   .ptr input.environment, .ptr input.seed, .u64 input.evaluator]

abbrev SetTask := List CVal → CProg CVal Bool

def taskCalls (setTask : SetTask) : ReadExpressions.Calls := fun name arguments =>
  if name = "prime_eval_stack_set_task".toList then
    setTask arguments >>= fun result => pure (.bool result)
  else CProg.undefined

def taskServices (setTask : SetTask) : StatementBlock.Services where
  read := ReadExpressions.expressionWith (taskCalls setTask)

def interpretedCall (setTask : SetTask) (input : CallInputs) : CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith (taskServices setTask) (fun _ _ _ => CProg.undefined)
    (fun _ => none) 0 1 input.locals callSyntax.body

/-- The common source interpreter preserves the complete named service
operation and its reply; this does not supply set_task's inner denotation. -/
theorem call_forwards_complete_arguments (setTask : SetTask) (input : CallInputs) :
    interpretedCall setTask input =
      (setTask input.arguments >>= fun accepted =>
        pure (.finished (.returned input.locals (some (.bool accepted))))) := by
  simp [interpretedCall, callSyntax, StatementBlock.executeWith_equation, taskServices,
    ReadExpressions.expressionWith_equation, ReadExpressions.argumentsWith_equation, ident,
    ReadExpressions.resolved, CallInputs.locals, taskCalls, CallInputs.arguments,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

theorem original_call_executes_complete_arguments (setTask : SetTask) (input : CallInputs) :
    (declaratorFunctionText? names callSource.toList).map
      (fun function => StatementBlock.executeWith (taskServices setTask)
        (fun _ _ _ => CProg.undefined) (fun _ => none) 0 1 input.locals function.body) =
      some (setTask input.arguments >>= fun accepted =>
        pure (.finished (.returned input.locals (some (.bool accepted))))) := by
  rw [original_call_source_recognized, Option.map_some]
  exact congrArg some (call_forwards_complete_arguments setTask input)

namespace Controls

def input : CallInputs :=
  { space := none, arena := some ⟨2, 0⟩, atom := some ⟨3, 0⟩,
    environment := some ⟨4, 0⟩, target := some ⟨5, 0⟩,
    fuel := -2147483648, evaluator := 4294967303,
    expectedType := none, preserve := false, strictIndex := -7, seed := some ⟨6, 0⟩ }

theorem exact_signed_nullable_wide_arguments : input.arguments =
    [.i32 1, .ptr none, .ptr (some ⟨2, 0⟩), .ptr (some ⟨3, 0⟩), .ptr none,
     .i32 (-2147483648), .bool false, .i32 (-7), .ptr (some ⟨5, 0⟩),
     .ptr (some ⟨4, 0⟩), .ptr (some ⟨6, 0⟩), .u64 4294967303] := rfl

theorem narrowing_evaluator_changes_request :
    input.arguments ≠ { input with evaluator := 7 }.arguments := by decide +kernel

theorem replacing_signed_strict_index_changes_request :
    input.arguments ≠ { input with strictIndex := 0 }.arguments := by decide +kernel

theorem seed_is_not_dynamic_environment :
    input.arguments[9]? ≠ input.arguments[10]? := by decide +kernel

end Controls

abbrev NormalizeInputs := NormalizeAtomConstructor.ConstructorInputs

def normalizeSyntax : CDeclaratorFunction :=
  ⟨⟨"bool".toList, 0⟩, "prime_eval_stack_schedule_normalize".toList,
   [⟨⟨"Space".toList, false, [false]⟩, "s".toList⟩,
    ⟨⟨"Arena".toList, false, [false]⟩, "a".toList⟩,
    ⟨⟨"Atom".toList, false, [false]⟩, "atom".toList⟩,
    ⟨⟨"int".toList, false, []⟩, "fuel".toList⟩,
    ⟨⟨"Bindings".toList, true, [false]⟩, "dynamic_env".toList⟩,
    ⟨⟨"uint64_t".toList, false, []⟩, "evaluator_id".toList⟩,
    ⟨⟨"OutcomeSet".toList, false, [false]⟩, "target".toList⟩],
   [.return (some (.call "prime_eval_stack_set_task".toList
     [ident "PRIME_EVAL_STACK_TASK_NORMALIZE", ident "s", ident "a", ident "atom",
      .null, ident "fuel", .bool true, .unary .negate (.decimal 1), ident "target",
      ident "dynamic_env", .null, ident "evaluator_id"]))]⟩

def normalizeSource : String := "static bool prime_eval_stack_schedule_normalize(\n    Space *s, Arena *a, Atom *atom, int fuel,\n    const Bindings *dynamic_env, uint64_t evaluator_id,\n    OutcomeSet *target) {\n    return prime_eval_stack_set_task(\n        PRIME_EVAL_STACK_TASK_NORMALIZE, s, a, atom, NULL, fuel,\n        true, -1, target, dynamic_env, NULL, evaluator_id);\n}"

def normalizeCharacters : List Char := native_c_characters% "static bool prime_eval_stack_schedule_normalize(\n    Space *s, Arena *a, Atom *atom, int fuel,\n    const Bindings *dynamic_env, uint64_t evaluator_id,\n    OutcomeSet *target) {\n    return prime_eval_stack_set_task(\n        PRIME_EVAL_STACK_TASK_NORMALIZE, s, a, atom, NULL, fuel,\n        true, -1, target, dynamic_env, NULL, evaluator_id);\n}"

theorem normalize_characters_are_source : normalizeSource.toList = normalizeCharacters := by
  native_c_character_reflexivity

theorem original_normalize_parses :
    declaratorFunctionText? names normalizeCharacters = some normalizeSyntax := by
  native_c_parser_reflexivity

theorem original_normalize_source_recognized :
    declaratorFunctionText? names normalizeSource.toList = some normalizeSyntax := by
  rw [normalize_characters_are_source]
  exact original_normalize_parses

def normalizeLocals (input : NormalizeInputs) : ReadExpressions.Environment := fun name =>
  if name = "s".toList then some (.ptr input.space)
  else if name = "a".toList then some (.ptr input.arena)
  else if name = "atom".toList then some (.ptr input.atom)
  else if name = "fuel".toList then some (.i32 input.fuel)
  else if name = "target".toList then some (.ptr input.target)
  else if name = "dynamic_env".toList then some (.ptr input.environment)
  else if name = "evaluator_id".toList then some (.u64 input.evaluator)
  else if name = "PRIME_EVAL_STACK_TASK_NORMALIZE".toList then some (.i32 2)
  else none

/-- NORMALIZE supplies its declared kind, absent expected type and seed,
true preservation and the signed strict-index sentinel; other arguments remain
caller-supplied. -/
def normalizeArguments (input : NormalizeInputs) : List CVal :=
  [.i32 2, .ptr input.space, .ptr input.arena, .ptr input.atom, .ptr none,
   .i32 input.fuel, .bool true, .i32 (-1), .ptr input.target,
   .ptr input.environment, .ptr none, .u64 input.evaluator]

def interpretedNormalize (setTask : SetTask) (input : NormalizeInputs) : CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith (taskServices setTask) (fun _ _ _ => CProg.undefined)
    (fun _ => none) 0 1 (normalizeLocals input) normalizeSyntax.body

theorem normalize_forwards_complete_arguments (setTask : SetTask) (input : NormalizeInputs) :
    interpretedNormalize setTask input =
      (setTask (normalizeArguments input) >>= fun accepted =>
        pure (.finished (.returned (normalizeLocals input) (some (.bool accepted))))) := by
  have oneNotMinimum : (1 : Int32) ≠ Int32.minValue := by decide +kernel
  simp [oneNotMinimum, interpretedNormalize, normalizeSyntax, StatementBlock.executeWith_equation, taskServices,
    ReadExpressions.expressionWith_equation, ReadExpressions.argumentsWith_equation, ident,
    ReadExpressions.resolved, normalizeLocals, taskCalls, normalizeArguments,
    ReadExpressions.negate, ReadExpressions.scalar, ReadExpressions.cell?,
    ScalarRead.signedDecimal?, ScalarRead.numericNegation?,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

theorem original_normalize_executes_complete_arguments (setTask : SetTask) (input : NormalizeInputs) :
    (declaratorFunctionText? names normalizeSource.toList).map
      (fun function => StatementBlock.executeWith (taskServices setTask)
        (fun _ _ _ => CProg.undefined) (fun _ => none) 0 1 (normalizeLocals input) function.body) =
      some (setTask (normalizeArguments input) >>= fun accepted =>
        pure (.finished (.returned (normalizeLocals input) (some (.bool accepted))))) := by
  rw [original_normalize_source_recognized, Option.map_some]
  exact congrArg some (normalize_forwards_complete_arguments setTask input)

namespace Controls

theorem normalize_request_keeps_wide_and_signed_inputs : normalizeArguments input.toConstructorInputs =
    [.i32 2, .ptr none, .ptr (some ⟨2, 0⟩), .ptr (some ⟨3, 0⟩), .ptr none,
     .i32 (-2147483648), .bool true, .i32 (-1), .ptr (some ⟨5, 0⟩),
     .ptr (some ⟨4, 0⟩), .ptr none, .u64 4294967303] := rfl

theorem call_and_normalize_are_not_interchangeable :
    input.arguments ≠ normalizeArguments input.toConstructorInputs := by decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.CeTTaNativeCost.Scheduling

namespace Mettapedia.Languages.MeTTa.CeTTaNativeCost.BindSchedule

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

structure BindOperations extends FrameOperations where
  targetOwned : Option Ptr → CProg CVal Bool
  captureDynamic : Ptr → Option Ptr → CProg CVal Bool
  setTask : Scheduling.SetTask
  push : Ptr → CProg CVal Unit
  pop : CProg CVal Unit
  assertion : Bool → CProg CVal Unit

structure BindLayout where
  frame : NormalizeAtomConstructor.FrameLayout
  currentDriver : Ptr
  top : Nat

def BindLayout.fields (layout : BindLayout) : ReadExpressions.Layout := fun name =>
  if name = "top".toList then some ⟨layout.top, .pointer⟩ else layout.frame.fields name

def BindLayout.names (layout : BindLayout) (environment : ReadExpressions.Environment) :
    ReadExpressions.NameReads :=
  ReadExpressions.localOrLocated environment (fun _ => false) fun name =>
    if name = "g_prime_eval_stack_driver".toList then some (layout.currentDriver, .pointer)
    else none

def inputs (input : NormalizeAtomConstructor.ConstructorInputs) : ReadExpressions.Environment :=
  Function.update (Function.update (Function.update input.locals
    "dynamic_env".toList (some (.ptr input.environment)))
    "PRIME_EVAL_STACK_FRAME_BIND_FINISH".toList (some (.i32 0)))
    "PRIME_EVAL_STACK_TASK_BIND".toList (some (.i32 0))

def ident (name : String) : CExpr := .identifier name.toList
def finishField (name : String) : CExpr := .field (ident "finish") name.toList true

def bindSyntax : CDeclaratorFunction :=
  ⟨⟨"bool".toList, 0⟩, "prime_eval_stack_schedule_bind".toList,
   [⟨⟨"Space".toList, false, [false]⟩, "s".toList⟩,
    ⟨⟨"Arena".toList, false, [false]⟩, "a".toList⟩,
    ⟨⟨"Atom".toList, false, [false]⟩, "atom".toList⟩,
    ⟨⟨"int".toList, false, []⟩, "fuel".toList⟩,
    ⟨⟨"Bindings".toList, true, [false]⟩, "dynamic_env".toList⟩,
    ⟨⟨"uint64_t".toList, false, []⟩, "evaluator_id".toList⟩,
    ⟨⟨"OutcomeSet".toList, false, [false]⟩, "target".toList⟩],
   [.branch (.unary .not (.call "prime_eval_stack_target_is_owned".toList [ident "target"]))
      [.return (some (.bool false))] [],
    .declare ⟨"PrimeEvalStackFrame".toList, 1⟩ "finish".toList
      (.call "prime_eval_stack_frame_new".toList [ident "PRIME_EVAL_STACK_FRAME_BIND_FINISH"]),
    .assign (finishField "space") (ident "s"),
    .assign (finishField "arena") (ident "a"),
    .assign (finishField "target") (ident "target"),
    .assign (finishField "atom") (ident "atom"),
    .assign (finishField "fuel") (ident "fuel"),
    .assign (finishField "evaluator_id") (ident "evaluator_id"),
    .effect (.call "outcome_set_init".toList [.unary .address (finishField "child")]),
    .assign (finishField "child_initialized") (.bool true),
    .branch (.unary .not (.call "prime_eval_stack_capture_dynamic_env".toList
      [.unary .address (finishField "env"), ident "dynamic_env"]))
      [.effect (.call "prime_eval_stack_frame_free".toList [ident "finish"]),
       .return (some (.bool false))] [],
    .assign (finishField "env_initialized") (.bool true),
    .effect (.call "prime_eval_stack_push".toList [ident "finish"]),
    .branch (.unary .not (.call "prime_eval_stack_set_task".toList
      [ident "PRIME_EVAL_STACK_TASK_BIND", ident "s", ident "a", ident "atom", .null,
       ident "fuel", .bool true, .unary .negate (.decimal 1),
       .unary .address (finishField "child"), .unary .address (finishField "env"), .null,
       ident "evaluator_id"]))
      [.effect (.call "assert".toList
        [.binary .eq (.field (ident "g_prime_eval_stack_driver") "top".toList true)
          (ident "finish")]),
       .effect (.call "prime_eval_stack_pop".toList []),
       .return (some (.bool false))] [],
    .return (some (.bool true))]⟩

def names : TypeNames := NormalizeAtomConstructor.names ++ ["bool".toList]
def source : String := "static bool prime_eval_stack_schedule_bind(\n    Space *s, Arena *a, Atom *atom, int fuel,\n    const Bindings *dynamic_env, uint64_t evaluator_id,\n    OutcomeSet *target) {\n    if (!prime_eval_stack_target_is_owned(target))\n        return false;\n    PrimeEvalStackFrame *finish =\n        prime_eval_stack_frame_new(PRIME_EVAL_STACK_FRAME_BIND_FINISH);\n    finish->space = s;\n    finish->arena = a;\n    finish->target = target;\n    finish->atom = atom;\n    finish->fuel = fuel;\n    finish->evaluator_id = evaluator_id;\n    outcome_set_init(&finish->child);\n    finish->child_initialized = true;\n    if (!prime_eval_stack_capture_dynamic_env(\n            &finish->env, dynamic_env)) {\n        prime_eval_stack_frame_free(finish);\n        return false;\n    }\n    finish->env_initialized = true;\n    prime_eval_stack_push(finish);\n    if (!prime_eval_stack_set_task(\n            PRIME_EVAL_STACK_TASK_BIND, s, a, atom, NULL, fuel,\n            true, -1, &finish->child, &finish->env, NULL,\n            evaluator_id)) {\n        assert(g_prime_eval_stack_driver->top == finish);\n        prime_eval_stack_pop();\n        return false;\n    }\n    return true;\n}"
def characters : List Char := native_c_characters% "static bool prime_eval_stack_schedule_bind(\n    Space *s, Arena *a, Atom *atom, int fuel,\n    const Bindings *dynamic_env, uint64_t evaluator_id,\n    OutcomeSet *target) {\n    if (!prime_eval_stack_target_is_owned(target))\n        return false;\n    PrimeEvalStackFrame *finish =\n        prime_eval_stack_frame_new(PRIME_EVAL_STACK_FRAME_BIND_FINISH);\n    finish->space = s;\n    finish->arena = a;\n    finish->target = target;\n    finish->atom = atom;\n    finish->fuel = fuel;\n    finish->evaluator_id = evaluator_id;\n    outcome_set_init(&finish->child);\n    finish->child_initialized = true;\n    if (!prime_eval_stack_capture_dynamic_env(\n            &finish->env, dynamic_env)) {\n        prime_eval_stack_frame_free(finish);\n        return false;\n    }\n    finish->env_initialized = true;\n    prime_eval_stack_push(finish);\n    if (!prime_eval_stack_set_task(\n            PRIME_EVAL_STACK_TASK_BIND, s, a, atom, NULL, fuel,\n            true, -1, &finish->child, &finish->env, NULL,\n            evaluator_id)) {\n        assert(g_prime_eval_stack_driver->top == finish);\n        prime_eval_stack_pop();\n        return false;\n    }\n    return true;\n}"

theorem characters_are_actual_source : source.toList = characters := by
  native_c_character_reflexivity

private def lexCharacters0 : List Char := native_c_characters% "static bool prime_eval_stack_schedule_bind(\n"
private def lexTokens0 : List Token := [.identifier (native_c_characters% "static"), .identifier (native_c_characters% "bool"), .identifier (native_c_characters% "prime_eval_stack_schedule_bind"), .punctuation (native_c_characters% "(")]
private theorem lexPiece0 : lexCharacters0.foldl step initial = completed lexTokens0 := by
  native_c_parser_reflexivity

private def lexCharacters1 : List Char := native_c_characters% "    Space *s, Arena *a, Atom *atom, int fuel,\n"
private def lexTokens1 : List Token := [.identifier (native_c_characters% "Space"), .punctuation (native_c_characters% "*"), .identifier (native_c_characters% "s"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "Arena"), .punctuation (native_c_characters% "*"), .identifier (native_c_characters% "a"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "Atom"), .punctuation (native_c_characters% "*"), .identifier (native_c_characters% "atom"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "int"), .identifier (native_c_characters% "fuel"), .punctuation (native_c_characters% ",")]
private theorem lexPiece1 : lexCharacters1.foldl step initial = completed lexTokens1 := by
  native_c_parser_reflexivity

private def lexCharacters2 : List Char := native_c_characters% "    const Bindings *dynamic_env, uint64_t evaluator_id,\n"
private def lexTokens2 : List Token := [.identifier (native_c_characters% "const"), .identifier (native_c_characters% "Bindings"), .punctuation (native_c_characters% "*"), .identifier (native_c_characters% "dynamic_env"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "uint64_t"), .identifier (native_c_characters% "evaluator_id"), .punctuation (native_c_characters% ",")]
private theorem lexPiece2 : lexCharacters2.foldl step initial = completed lexTokens2 := by
  native_c_parser_reflexivity

private def lexCharacters3 : List Char := native_c_characters% "    OutcomeSet *target) {\n"
private def lexTokens3 : List Token := [.identifier (native_c_characters% "OutcomeSet"), .punctuation (native_c_characters% "*"), .identifier (native_c_characters% "target"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% "{")]
private theorem lexPiece3 : lexCharacters3.foldl step initial = completed lexTokens3 := by
  native_c_parser_reflexivity

private def lexCharacters4 : List Char := native_c_characters% "    if (!prime_eval_stack_target_is_owned(target))\n"
private def lexTokens4 : List Token := [.identifier (native_c_characters% "if"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "!"), .identifier (native_c_characters% "prime_eval_stack_target_is_owned"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "target"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ")")]
private theorem lexPiece4 : lexCharacters4.foldl step initial = completed lexTokens4 := by
  native_c_parser_reflexivity

private def lexCharacters5 : List Char := native_c_characters% "        return false;\n"
private def lexTokens5 : List Token := [.identifier (native_c_characters% "return"), .identifier (native_c_characters% "false"), .punctuation (native_c_characters% ";")]
private theorem lexPiece5 : lexCharacters5.foldl step initial = completed lexTokens5 := by
  native_c_parser_reflexivity

private def lexCharacters6 : List Char := native_c_characters% "    PrimeEvalStackFrame *finish =\n"
private def lexTokens6 : List Token := [.identifier (native_c_characters% "PrimeEvalStackFrame"), .punctuation (native_c_characters% "*"), .identifier (native_c_characters% "finish"), .punctuation (native_c_characters% "=")]
private theorem lexPiece6 : lexCharacters6.foldl step initial = completed lexTokens6 := by
  native_c_parser_reflexivity

private def lexCharacters7 : List Char := native_c_characters% "        prime_eval_stack_frame_new(PRIME_EVAL_STACK_FRAME_BIND_FINISH);\n"
private def lexTokens7 : List Token := [.identifier (native_c_characters% "prime_eval_stack_frame_new"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "PRIME_EVAL_STACK_FRAME_BIND_FINISH"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece7 : lexCharacters7.foldl step initial = completed lexTokens7 := by
  native_c_parser_reflexivity

private def lexCharacters8 : List Char := native_c_characters% "    finish->space = s;\n"
private def lexTokens8 : List Token := [.identifier (native_c_characters% "finish"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "space"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "s"), .punctuation (native_c_characters% ";")]
private theorem lexPiece8 : lexCharacters8.foldl step initial = completed lexTokens8 := by
  native_c_parser_reflexivity

private def lexCharacters9 : List Char := native_c_characters% "    finish->arena = a;\n"
private def lexTokens9 : List Token := [.identifier (native_c_characters% "finish"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "arena"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "a"), .punctuation (native_c_characters% ";")]
private theorem lexPiece9 : lexCharacters9.foldl step initial = completed lexTokens9 := by
  native_c_parser_reflexivity

private def lexCharacters10 : List Char := native_c_characters% "    finish->target = target;\n"
private def lexTokens10 : List Token := [.identifier (native_c_characters% "finish"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "target"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "target"), .punctuation (native_c_characters% ";")]
private theorem lexPiece10 : lexCharacters10.foldl step initial = completed lexTokens10 := by
  native_c_parser_reflexivity

private def lexCharacters11 : List Char := native_c_characters% "    finish->atom = atom;\n"
private def lexTokens11 : List Token := [.identifier (native_c_characters% "finish"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "atom"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "atom"), .punctuation (native_c_characters% ";")]
private theorem lexPiece11 : lexCharacters11.foldl step initial = completed lexTokens11 := by
  native_c_parser_reflexivity

private def lexCharacters12 : List Char := native_c_characters% "    finish->fuel = fuel;\n"
private def lexTokens12 : List Token := [.identifier (native_c_characters% "finish"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "fuel"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "fuel"), .punctuation (native_c_characters% ";")]
private theorem lexPiece12 : lexCharacters12.foldl step initial = completed lexTokens12 := by
  native_c_parser_reflexivity

private def lexCharacters13 : List Char := native_c_characters% "    finish->evaluator_id = evaluator_id;\n"
private def lexTokens13 : List Token := [.identifier (native_c_characters% "finish"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "evaluator_id"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "evaluator_id"), .punctuation (native_c_characters% ";")]
private theorem lexPiece13 : lexCharacters13.foldl step initial = completed lexTokens13 := by
  native_c_parser_reflexivity

private def lexCharacters14 : List Char := native_c_characters% "    outcome_set_init(&finish->child);\n"
private def lexTokens14 : List Token := [.identifier (native_c_characters% "outcome_set_init"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "&"), .identifier (native_c_characters% "finish"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "child"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece14 : lexCharacters14.foldl step initial = completed lexTokens14 := by
  native_c_parser_reflexivity

private def lexCharacters15 : List Char := native_c_characters% "    finish->child_initialized = true;\n"
private def lexTokens15 : List Token := [.identifier (native_c_characters% "finish"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "child_initialized"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "true"), .punctuation (native_c_characters% ";")]
private theorem lexPiece15 : lexCharacters15.foldl step initial = completed lexTokens15 := by
  native_c_parser_reflexivity

private def lexCharacters16 : List Char := native_c_characters% "    if (!prime_eval_stack_capture_dynamic_env(\n"
private def lexTokens16 : List Token := [.identifier (native_c_characters% "if"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "!"), .identifier (native_c_characters% "prime_eval_stack_capture_dynamic_env"), .punctuation (native_c_characters% "(")]
private theorem lexPiece16 : lexCharacters16.foldl step initial = completed lexTokens16 := by
  native_c_parser_reflexivity

private def lexCharacters17 : List Char := native_c_characters% "            &finish->env, dynamic_env)) {\n"
private def lexTokens17 : List Token := [.punctuation (native_c_characters% "&"), .identifier (native_c_characters% "finish"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "env"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "dynamic_env"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% "{")]
private theorem lexPiece17 : lexCharacters17.foldl step initial = completed lexTokens17 := by
  native_c_parser_reflexivity

private def lexCharacters18 : List Char := native_c_characters% "        prime_eval_stack_frame_free(finish);\n"
private def lexTokens18 : List Token := [.identifier (native_c_characters% "prime_eval_stack_frame_free"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "finish"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece18 : lexCharacters18.foldl step initial = completed lexTokens18 := by
  native_c_parser_reflexivity

private def lexCharacters19 : List Char := native_c_characters% "        return false;\n"
private def lexTokens19 : List Token := [.identifier (native_c_characters% "return"), .identifier (native_c_characters% "false"), .punctuation (native_c_characters% ";")]
private theorem lexPiece19 : lexCharacters19.foldl step initial = completed lexTokens19 := by
  native_c_parser_reflexivity

private def lexCharacters20 : List Char := native_c_characters% "    }\n"
private def lexTokens20 : List Token := [.punctuation (native_c_characters% "}")]
private theorem lexPiece20 : lexCharacters20.foldl step initial = completed lexTokens20 := by
  native_c_parser_reflexivity

private def lexCharacters21 : List Char := native_c_characters% "    finish->env_initialized = true;\n"
private def lexTokens21 : List Token := [.identifier (native_c_characters% "finish"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "env_initialized"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "true"), .punctuation (native_c_characters% ";")]
private theorem lexPiece21 : lexCharacters21.foldl step initial = completed lexTokens21 := by
  native_c_parser_reflexivity

private def lexCharacters22 : List Char := native_c_characters% "    prime_eval_stack_push(finish);\n"
private def lexTokens22 : List Token := [.identifier (native_c_characters% "prime_eval_stack_push"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "finish"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece22 : lexCharacters22.foldl step initial = completed lexTokens22 := by
  native_c_parser_reflexivity

private def lexCharacters23 : List Char := native_c_characters% "    if (!prime_eval_stack_set_task(\n"
private def lexTokens23 : List Token := [.identifier (native_c_characters% "if"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "!"), .identifier (native_c_characters% "prime_eval_stack_set_task"), .punctuation (native_c_characters% "(")]
private theorem lexPiece23 : lexCharacters23.foldl step initial = completed lexTokens23 := by
  native_c_parser_reflexivity

private def lexCharacters24 : List Char := native_c_characters% "            PRIME_EVAL_STACK_TASK_BIND, s, a, atom, NULL, fuel,\n"
private def lexTokens24 : List Token := [.identifier (native_c_characters% "PRIME_EVAL_STACK_TASK_BIND"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "s"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "a"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "atom"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "NULL"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "fuel"), .punctuation (native_c_characters% ",")]
private theorem lexPiece24 : lexCharacters24.foldl step initial = completed lexTokens24 := by
  native_c_parser_reflexivity

private def lexCharacters25 : List Char := native_c_characters% "            true, -1, &finish->child, &finish->env, NULL,\n"
private def lexTokens25 : List Token := [.identifier (native_c_characters% "true"), .punctuation (native_c_characters% ","), .punctuation (native_c_characters% "-"), .number (native_c_characters% "1"), .punctuation (native_c_characters% ","), .punctuation (native_c_characters% "&"), .identifier (native_c_characters% "finish"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "child"), .punctuation (native_c_characters% ","), .punctuation (native_c_characters% "&"), .identifier (native_c_characters% "finish"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "env"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "NULL"), .punctuation (native_c_characters% ",")]
private theorem lexPiece25 : lexCharacters25.foldl step initial = completed lexTokens25 := by
  native_c_parser_reflexivity

private def lexCharacters26 : List Char := native_c_characters% "            evaluator_id)) {\n"
private def lexTokens26 : List Token := [.identifier (native_c_characters% "evaluator_id"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% "{")]
private theorem lexPiece26 : lexCharacters26.foldl step initial = completed lexTokens26 := by
  native_c_parser_reflexivity

private def lexCharacters27 : List Char := native_c_characters% "        assert(g_prime_eval_stack_driver->top == finish);\n"
private def lexTokens27 : List Token := [.identifier (native_c_characters% "assert"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "g_prime_eval_stack_driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "top"), .punctuation (native_c_characters% "=="), .identifier (native_c_characters% "finish"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece27 : lexCharacters27.foldl step initial = completed lexTokens27 := by
  native_c_parser_reflexivity

private def lexCharacters28 : List Char := native_c_characters% "        prime_eval_stack_pop();\n"
private def lexTokens28 : List Token := [.identifier (native_c_characters% "prime_eval_stack_pop"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece28 : lexCharacters28.foldl step initial = completed lexTokens28 := by
  native_c_parser_reflexivity

private def lexCharacters29 : List Char := native_c_characters% "        return false;\n"
private def lexTokens29 : List Token := [.identifier (native_c_characters% "return"), .identifier (native_c_characters% "false"), .punctuation (native_c_characters% ";")]
private theorem lexPiece29 : lexCharacters29.foldl step initial = completed lexTokens29 := by
  native_c_parser_reflexivity

private def lexCharacters30 : List Char := native_c_characters% "    }\n"
private def lexTokens30 : List Token := [.punctuation (native_c_characters% "}")]
private theorem lexPiece30 : lexCharacters30.foldl step initial = completed lexTokens30 := by
  native_c_parser_reflexivity

private def lexCharacters31 : List Char := native_c_characters% "    return true;\n"
private def lexTokens31 : List Token := [.identifier (native_c_characters% "return"), .identifier (native_c_characters% "true"), .punctuation (native_c_characters% ";")]
private theorem lexPiece31 : lexCharacters31.foldl step initial = completed lexTokens31 := by
  native_c_parser_reflexivity

private def lexCharacters32 : List Char := native_c_characters% "}"
private def lexTokens32 : List Token := [.punctuation (native_c_characters% "}")]
private theorem lexPiece32 : lexCharacters32.foldl step initial = completed lexTokens32 := by
  native_c_parser_reflexivity

private def sourcePieces : List (List Char × List Token) := [(lexCharacters0, lexTokens0), (lexCharacters1, lexTokens1), (lexCharacters2, lexTokens2), (lexCharacters3, lexTokens3), (lexCharacters4, lexTokens4), (lexCharacters5, lexTokens5), (lexCharacters6, lexTokens6), (lexCharacters7, lexTokens7), (lexCharacters8, lexTokens8), (lexCharacters9, lexTokens9), (lexCharacters10, lexTokens10), (lexCharacters11, lexTokens11), (lexCharacters12, lexTokens12), (lexCharacters13, lexTokens13), (lexCharacters14, lexTokens14), (lexCharacters15, lexTokens15), (lexCharacters16, lexTokens16), (lexCharacters17, lexTokens17), (lexCharacters18, lexTokens18), (lexCharacters19, lexTokens19), (lexCharacters20, lexTokens20), (lexCharacters21, lexTokens21), (lexCharacters22, lexTokens22), (lexCharacters23, lexTokens23), (lexCharacters24, lexTokens24), (lexCharacters25, lexTokens25), (lexCharacters26, lexTokens26), (lexCharacters27, lexTokens27), (lexCharacters28, lexTokens28), (lexCharacters29, lexTokens29), (lexCharacters30, lexTokens30), (lexCharacters31, lexTokens31), (lexCharacters32, lexTokens32)]

private theorem characters_from_pieces : sourcePieces.flatMap Prod.fst = characters := by
  native_c_parser_reflexivity

def tokens : List Token := sourcePieces.flatMap Prod.snd

theorem actual_characters_lexed : lex characters = .ok tokens := by
  rw [← characters_from_pieces]
  apply lex_of_completed
  apply completed_pieces sourcePieces
  simp only [sourcePieces, List.forall_cons ]
  exact ⟨lexPiece0, lexPiece1, lexPiece2, lexPiece3, lexPiece4, lexPiece5, lexPiece6, lexPiece7, lexPiece8, lexPiece9, lexPiece10, lexPiece11, lexPiece12, lexPiece13, lexPiece14, lexPiece15, lexPiece16, lexPiece17, lexPiece18, lexPiece19, lexPiece20, lexPiece21, lexPiece22, lexPiece23, lexPiece24, lexPiece25, lexPiece26, lexPiece27, lexPiece28, lexPiece29, lexPiece30, lexPiece31, lexPiece32, by trivial⟩

theorem actual_tokens_parsed :
    functionUsing? (declaratorParameter? names) (2 * tokens.length + 4) names
      (ordinaryFunctionTokens tokens) = some (bindSyntax, []) := by
  native_c_parser_reflexivity

theorem actual_bind_parses : declaratorFunctionText? names characters = some bindSyntax :=
  function_text_using_of_parts (declaratorParameter? names) names characters tokens bindSyntax
    actual_characters_lexed actual_tokens_parsed

theorem original_source_recognized :
    declaratorFunctionText? names source.toList = some bindSyntax := by
  rw [characters_are_actual_source]
  exact actual_bind_parses


def BindOperations.values (operations : BindOperations) : ReadExpressions.Calls :=
  fun name arguments =>
    if name = "prime_eval_stack_target_is_owned".toList then match arguments with
      | [.ptr target] => operations.targetOwned target >>= fun accepted => pure (.bool accepted)
      | _ => CProg.undefined
    else if name = "prime_eval_stack_frame_new".toList then match arguments with
      | [.i32 kind] => operations.newFrame kind >>= fun frame => pure (.ptr (some frame))
      | _ => CProg.undefined
    else if name = "prime_eval_stack_capture_dynamic_env".toList then match arguments with
      | [.ptr (some destination), .ptr source] =>
          operations.captureDynamic destination source >>= fun captured => pure (.bool captured)
      | _ => CProg.undefined
    else Scheduling.taskCalls operations.setTask name arguments

def BindOperations.effects (operations : BindOperations) : ReadExpressions.CallService Unit :=
  fun name arguments =>
    if name = "outcome_set_init".toList then match arguments with
      | [.ptr (some child)] => operations.initializeChild child
      | _ => CProg.undefined
    else if name = "prime_eval_stack_frame_free".toList then match arguments with
      | [.ptr (some frame)] => operations.retireFrame frame
      | _ => CProg.undefined
    else if name = "prime_eval_stack_push".toList then match arguments with
      | [.ptr (some frame)] => operations.push frame
      | _ => CProg.undefined
    else if name = "prime_eval_stack_pop".toList then match arguments with
      | [] => operations.pop
      | _ => CProg.undefined
    else if name = "assert".toList then match arguments with
      | [.bool accepted] => operations.assertion accepted
      | _ => CProg.undefined
    else CProg.undefined

abbrev BindOperations.reader (operations : BindOperations) (layout : BindLayout) : StatementBlock.Reader :=
  fun fields environment operand =>
    ReadExpressions.expressionWithNames (layout.names environment) operations.values fields operand

def BindOperations.profile (operations : BindOperations) (layout : BindLayout) :
    StatementBlock.Services where
  read := operations.reader layout
  initialValue := StatementBlock.objectInitialValue
  effect := fun fields environment operand =>
    EffectStatements.invokeWithNames (layout.names environment) operations.values operations.effects fields operand

def interpretedBind (operations : BindOperations) (layout : BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) : CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith (operations.profile layout)
    (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 17
    (inputs input) bindSyntax.body

def finishEnvironment (input : NormalizeAtomConstructor.ConstructorInputs) (finish : Ptr) :
    ReadExpressions.Environment :=
  Function.update (inputs input) "finish".toList (some (.ptr (some finish)))

/-- The retained sequence uses the current named driver load after set_task's
reply. Allocation, admission, capture, push, assertion and pop remain named
services; their inner contracts and nonlocal outcomes are separate. -/
def bindOperations (operations : BindOperations) (layout : BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) : CProg CVal ReadBlock.Result := do
  let admitted ← operations.targetOwned input.target
  if !admitted then pure (.finished (.returned (inputs input) (some (.bool false)))) else do
    let finish ← operations.newFrame 0
    let environment := finishEnvironment input finish
    let result ← do
      CProg.store (finish + layout.frame.space) (.ptr input.space)
      CProg.store (finish + layout.frame.arena) (.ptr input.arena)
      CProg.store (finish + layout.frame.target) (.ptr input.target)
      CProg.store (finish + layout.frame.atom) (.ptr input.atom)
      CProg.store (finish + layout.frame.fuel) (.i32 input.fuel)
      CProg.store (finish + layout.frame.evaluator) (.u64 input.evaluator)
      operations.initializeChild (finish + layout.frame.child)
      CProg.store (finish + layout.frame.childInitialized) (.bool true)
      let captured ← operations.captureDynamic (finish + layout.frame.environment) input.environment
      if !captured then do
        operations.retireFrame finish
        pure (.finished (.returned environment (some (.bool false))))
      else do
        CProg.store (finish + layout.frame.environmentInitialized) (.bool true)
        operations.push finish
        let accepted ← operations.setTask
          [.i32 0, .ptr input.space, .ptr input.arena, .ptr input.atom, .ptr none,
           .i32 input.fuel, .bool true, .i32 (-1), .ptr (some (finish + layout.frame.child)),
           .ptr (some (finish + layout.frame.environment)), .ptr none, .u64 input.evaluator]
        if !accepted then do
          let driver ← CProg.loadPtr layout.currentDriver
          let top ← ReadExpressions.field (fun _ => some ⟨layout.top, .pointer⟩) (.ptr driver) "top".toList
          let agrees ← ReadExpressions.equal top (.ptr (some finish))
          operations.assertion agrees
          operations.pop
          pure (.finished (.returned environment (some (.bool false))))
        else pure (.finished (.returned environment (some (.bool true))))
    pure (ReadBlock.restore "finish".toList ((inputs input) "finish".toList) result)



theorem identifier_read (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment) (name : String) (value : CVal)
    (known : environment name.toList = some value) :
    ReadExpressions.expressionWithNames (layout.names environment) operations.values
      layout.fields (ident name) = pure value := by
  simp only [ident, ReadExpressions.expressionWithNames.eq_def,
    BindLayout.names, ReadExpressions.localOrLocated, known]

theorem field_address_read (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment) (finish : Ptr)
    (known : environment "finish".toList = some (.ptr (some finish)))
    (name : String) (offset : Nat) (kind : ReadExpressions.FieldKind)
    (selected : layout.fields name.toList = some ⟨offset, kind⟩) :
    ReadExpressions.expressionWithNames (layout.names environment) operations.values
      layout.fields (.unary .address (finishField name)) =
      pure (.ptr (some (finish + offset))) := by
  rw [ReadExpressions.expressionWithNames.eq_def]
  dsimp only [finishField]
  rw [identifier_read operations layout environment "finish" _ known]
  simp only [Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  rw [ReadExpressions.default_owner_field_layout_is_unchanged]
  rw [ReadExpressions.field_address_retains_offset layout.fields finish name.toList offset kind selected]
  rfl

theorem field_assignment (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment) (finish : Ptr)
    (known : environment "finish".toList = some (.ptr (some finish)))
    (name : String) (offset : Nat) (rhs : CExpr) (value : CVal)
    (selected : layout.fields name.toList = some ⟨offset, ReadExpressions.valueKind value⟩)
    (actual : operations.reader layout layout.fields environment rhs = pure value) :
    StatementBlock.fieldAssignment (operations.reader layout) layout.fields environment
      (.assign (finishField name) rhs) =
        (CProg.store (finish + offset) value >>= fun _ => pure environment) := by
  change ReadExpressions.expressionWithNames (layout.names environment) operations.values
    layout.fields rhs = pure value at actual
  simp only [StatementBlock.fieldAssignment, finishField, BindOperations.reader,
    identifier_read operations layout environment "finish" _ known,
    actual, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  rw [ReadExpressions.field_store_retains_actual_value layout.fields finish name.toList offset value selected]

theorem store_then_suffix (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment) (finish : Ptr)
    (known : environment "finish".toList = some (.ptr (some finish)))
    (name : String) (offset : Nat) (rhs : CExpr) (value : CVal)
    (selected : layout.fields name.toList = some ⟨offset, ReadExpressions.valueKind value⟩)
    (actual : operations.reader layout layout.fields environment rhs = pure value)
    (fuel : Nat) (rest : List CStatement) :
    StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 (fuel + 1)
      environment (.assign (finishField name) rhs :: rest) =
    (CProg.store (finish + offset) value >>= fun _ =>
      StatementBlock.executeWith (operations.profile layout)
        (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 fuel
        environment rest) := by
  rw [StatementBlock.executeWith_equation]
  dsimp only
  rw [field_assignment operations layout environment finish known name offset rhs value selected actual]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]

theorem finish_lookup (input : NormalizeAtomConstructor.ConstructorInputs) (finish : Ptr) :
    finishEnvironment input finish "finish".toList = some (.ptr (some finish)) := by
  rw [finishEnvironment, Function.update_self]

theorem six_fields_keep_actual_inputs (operations : BindOperations) (layout : BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) (finish : Ptr) :
    StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 15
      (finishEnvironment input finish) (bindSyntax.body.drop 2) =
    (CProg.store (finish + layout.frame.space) (.ptr input.space) >>= fun _ =>
      CProg.store (finish + layout.frame.arena) (.ptr input.arena) >>= fun _ =>
      CProg.store (finish + layout.frame.target) (.ptr input.target) >>= fun _ =>
      CProg.store (finish + layout.frame.atom) (.ptr input.atom) >>= fun _ =>
      CProg.store (finish + layout.frame.fuel) (.i32 input.fuel) >>= fun _ =>
      CProg.store (finish + layout.frame.evaluator) (.u64 input.evaluator) >>= fun _ =>
      StatementBlock.executeWith (operations.profile layout)
        (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 9
        (finishEnvironment input finish) (bindSyntax.body.drop 8)) := by
  change StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 15
      (finishEnvironment input finish)
      (.assign (finishField "space") (ident "s") ::
       .assign (finishField "arena") (ident "a") ::
       .assign (finishField "target") (ident "target") ::
       .assign (finishField "atom") (ident "atom") ::
       .assign (finishField "fuel") (ident "fuel") ::
       .assign (finishField "evaluator_id") (ident "evaluator_id") :: bindSyntax.body.drop 8) = _
  rw [store_then_suffix operations layout (finishEnvironment input finish) finish
    (finish_lookup input finish) "space" layout.frame.space (ident "s") (.ptr input.space) (by rfl)
    (identifier_read operations layout (finishEnvironment input finish) "s" (.ptr input.space) (by rfl)) 14 _]
  rw [store_then_suffix operations layout (finishEnvironment input finish) finish
    (finish_lookup input finish) "arena" layout.frame.arena (ident "a") (.ptr input.arena) (by rfl)
    (identifier_read operations layout (finishEnvironment input finish) "a" (.ptr input.arena) (by rfl)) 13 _]
  rw [store_then_suffix operations layout (finishEnvironment input finish) finish
    (finish_lookup input finish) "target" layout.frame.target (ident "target") (.ptr input.target) (by rfl)
    (identifier_read operations layout (finishEnvironment input finish) "target" (.ptr input.target) (by rfl)) 12 _]
  rw [store_then_suffix operations layout (finishEnvironment input finish) finish
    (finish_lookup input finish) "atom" layout.frame.atom (ident "atom") (.ptr input.atom) (by rfl)
    (identifier_read operations layout (finishEnvironment input finish) "atom" (.ptr input.atom) (by rfl)) 11 _]
  rw [store_then_suffix operations layout (finishEnvironment input finish) finish
    (finish_lookup input finish) "fuel" layout.frame.fuel (ident "fuel") (.i32 input.fuel) (by rfl)
    (identifier_read operations layout (finishEnvironment input finish) "fuel" (.i32 input.fuel) (by rfl)) 10 _]
  rw [store_then_suffix operations layout (finishEnvironment input finish) finish
    (finish_lookup input finish) "evaluator_id" layout.frame.evaluator (ident "evaluator_id") (.u64 input.evaluator) (by rfl)
    (identifier_read operations layout (finishEnvironment input finish) "evaluator_id" (.u64 input.evaluator) (by rfl)) 9 _]


theorem one_argument_effect (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment) (name : String) (operand : CExpr)
    (value : CVal) (program : CProg CVal Unit)
    (actual : operations.reader layout layout.fields environment operand = pure value)
    (supplied : operations.effects name.toList [value] = program) :
    (operations.profile layout).effect layout.fields environment (.call name.toList [operand]) =
      program := by
  change EffectStatements.invokeWithNames (layout.names environment) operations.values
    operations.effects layout.fields (.call name.toList [operand]) = _
  rw [EffectStatements.named_void_call_keeps_actual_arguments]
  simp only [ReadExpressions.argumentsWithNames.eq_def]
  change ReadExpressions.expressionWithNames (layout.names environment) operations.values
    layout.fields operand = pure value at actual
  rw [actual]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  exact supplied

theorem capture_keeps_actual_slots (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment) (finish : Ptr) (source : Option Ptr)
    (knownFinish : environment "finish".toList = some (.ptr (some finish)))
    (knownSource : environment "dynamic_env".toList = some (.ptr source)) :
    operations.reader layout layout.fields environment
      (.call "prime_eval_stack_capture_dynamic_env".toList
        [.unary .address (finishField "env"), ident "dynamic_env"]) =
      (operations.captureDynamic (finish + layout.frame.environment) source >>= fun captured =>
        pure (.bool captured)) := by
  change ReadExpressions.expressionWithNames (layout.names environment) operations.values layout.fields
    (.call "prime_eval_stack_capture_dynamic_env".toList
      [.unary .address (finishField "env"), ident "dynamic_env"]) = _
  rw [ReadExpressions.expressionWithNames.eq_def]
  simp only [ReadExpressions.argumentsWithNames.eq_def]
  rw [field_address_read operations layout environment finish knownFinish "env"
    layout.frame.environment .embedded (by rfl),
    identifier_read operations layout environment "dynamic_env" _ knownSource]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rfl

def taskArguments (input : NormalizeAtomConstructor.ConstructorInputs) (layout : BindLayout)
    (finish : Ptr) : List CVal :=
  [.i32 0, .ptr input.space, .ptr input.arena, .ptr input.atom, .ptr none,
   .i32 input.fuel, .bool true, .i32 (-1), .ptr (some (finish + layout.frame.child)),
   .ptr (some (finish + layout.frame.environment)), .ptr none, .u64 input.evaluator]

def taskExpression : CExpr := .call "prime_eval_stack_set_task".toList
  [ident "PRIME_EVAL_STACK_TASK_BIND", ident "s", ident "a", ident "atom", .null,
   ident "fuel", .bool true, .unary .negate (.decimal 1), .unary .address (finishField "child"),
   .unary .address (finishField "env"), .null, ident "evaluator_id"]

theorem minus_one_read (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment) :
    ReadExpressions.expressionWithNames (layout.names environment) operations.values
      layout.fields (.unary .negate (.decimal 1)) = pure (.i32 (-1)) := by
  have oneNotMinimum : (1 : Int32) ≠ Int32.minValue := by decide +kernel
  simp [oneNotMinimum, ReadExpressions.expressionWithNames.eq_def,
    ReadExpressions.resolved, ReadExpressions.negate, ReadExpressions.scalar, ReadExpressions.cell?,
    ScalarRead.signedDecimal?, ScalarRead.numericNegation?,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

theorem task_call_keeps_complete_request (operations : BindOperations) (layout : BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) (finish : Ptr) :
    operations.reader layout layout.fields (finishEnvironment input finish) taskExpression =
      (operations.setTask (taskArguments input layout finish) >>= fun accepted => pure (.bool accepted)) := by
  change ReadExpressions.expressionWithNames (layout.names (finishEnvironment input finish))
      operations.values layout.fields taskExpression = _
  rw [taskExpression, ReadExpressions.expressionWithNames.eq_def]
  simp only [ReadExpressions.argumentsWithNames.eq_def]
  rw [identifier_read operations layout (finishEnvironment input finish) "PRIME_EVAL_STACK_TASK_BIND" (.i32 0) (by rfl)]
  rw [identifier_read operations layout (finishEnvironment input finish) "s" (.ptr input.space) (by rfl)]
  rw [identifier_read operations layout (finishEnvironment input finish) "a" (.ptr input.arena) (by rfl)]
  rw [identifier_read operations layout (finishEnvironment input finish) "atom" (.ptr input.atom) (by rfl)]
  rw [identifier_read operations layout (finishEnvironment input finish) "fuel" (.i32 input.fuel) (by rfl)]
  rw [identifier_read operations layout (finishEnvironment input finish) "evaluator_id" (.u64 input.evaluator) (by rfl)]
  rw [minus_one_read operations layout (finishEnvironment input finish)]
  rw [field_address_read operations layout (finishEnvironment input finish) finish (finish_lookup input finish)
    "child" layout.frame.child .embedded (by rfl),
    field_address_read operations layout (finishEnvironment input finish) finish (finish_lookup input finish)
      "env" layout.frame.environment .embedded (by rfl)]
  simp only [ReadExpressions.expressionWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rfl


theorem current_driver_is_loaded (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment)
    (outside : environment "g_prime_eval_stack_driver".toList = none) :
    ReadExpressions.expressionWithNames (layout.names environment) operations.values
      layout.fields (ident "g_prime_eval_stack_driver") =
      (CProg.loadPtr layout.currentDriver >>= fun value => pure (.ptr value)) := by
  have zero : layout.currentDriver + 0 = layout.currentDriver := by cases layout.currentDriver; rfl
  rw [ReadExpressions.expressionWithNames.eq_def]
  change layout.names environment "g_prime_eval_stack_driver".toList = _
  unfold BindLayout.names ReadExpressions.localOrLocated
  rw [outside]
  change (CProg.loadPtr (layout.currentDriver + 0) >>= fun value => pure (CVal.ptr value)) = _
  rw [zero]

def assertionExpression : CExpr := .call "assert".toList
  [.binary .eq (.field (ident "g_prime_eval_stack_driver") "top".toList true) (ident "finish")]

def assertCurrent (operations : BindOperations) (layout : BindLayout) (finish : Ptr) : CProg CVal Unit := do
  let driver ← CProg.loadPtr layout.currentDriver
  let top ← ReadExpressions.field (fun _ => some ⟨layout.top, .pointer⟩) (.ptr driver) "top".toList
  let same ← ReadExpressions.equal top (.ptr (some finish))
  operations.assertion same

theorem assertion_reads_after_task_reply (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment) (finish : Ptr)
    (knownFinish : environment "finish".toList = some (.ptr (some finish)))
    (outside : environment "g_prime_eval_stack_driver".toList = none) :
    (operations.profile layout).effect layout.fields environment assertionExpression =
      assertCurrent operations layout finish := by
  change EffectStatements.invokeWithNames (layout.names environment) operations.values
    operations.effects layout.fields assertionExpression = _
  rw [assertionExpression, EffectStatements.named_void_call_keeps_actual_arguments]
  simp only [ReadExpressions.argumentsWithNames.eq_def]
  rw [ReadExpressions.expressionWithNames.eq_def]
  dsimp only
  rw [ReadExpressions.expressionWithNames.eq_def]
  dsimp only
  rw [current_driver_is_loaded operations layout environment outside,
    identifier_read operations layout environment "finish" _ knownFinish]
  simp only [ReadExpressions.binary, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  unfold assertCurrent
  congr 1


theorem effect_then_suffix (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment) (operand : CExpr) (program : CProg CVal Unit)
    (actual : (operations.profile layout).effect layout.fields environment operand = program)
    (fuel : Nat) (rest : List CStatement) :
    StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 (fuel + 1)
      environment (.effect operand :: rest) =
      (program >>= fun _ => StatementBlock.executeWith (operations.profile layout)
        (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 fuel environment rest) := by
  rw [StatementBlock.executeWith_equation]
  dsimp only
  rw [actual]

theorem negate_boolean_action (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment) (operand : CExpr) (program : CProg CVal Bool)
    (actual : ReadExpressions.expressionWithNames (layout.names environment) operations.values
      layout.fields operand = (program >>= fun value => pure (.bool value))) :
    ReadExpressions.expressionWithNames (layout.names environment) operations.values layout.fields
      (.unary .not operand) = (program >>= fun value => pure (.bool (!value))) := by
  rw [ReadExpressions.expressionWithNames.eq_def]
  dsimp only
  rw [actual]
  simp only [ReadExpressions.truth, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]

theorem branch_using_action (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment) (condition : CExpr) (program : CProg CVal Bool)
    (actual : (operations.profile layout).read layout.fields environment condition =
      (program >>= fun value => pure (.bool value)))
    (fuel : Nat) (yes no rest : List CStatement) :
    StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 (fuel + 1)
      environment (.branch condition yes no :: rest) =
      (program >>= fun selected => do
        let result ← StatementBlock.executeWith (operations.profile layout)
          (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 fuel
          environment (if selected then yes else no)
        ReadBlock.resume (fun updated => StatementBlock.executeWith (operations.profile layout)
          (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 fuel updated rest) result) := by
  rw [StatementBlock.executeWith_equation]
  dsimp only
  rw [actual]
  simp only [ReadExpressions.truth, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]

theorem return_boolean_stops (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment) (value : Bool) (fuel : Nat) (rest : List CStatement) :
    StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 (fuel + 1)
      environment (.return (some (.bool value)) :: rest) =
      pure (.finished (.returned environment (some (.bool value)))) := by
  rw [StatementBlock.executeWith_equation]
  change (ReadExpressions.expressionWithNames (layout.names environment) operations.values
    layout.fields (.bool value) >>= fun actual => pure (ReadBlock.Result.finished (.returned environment (some actual)))) = _
  rw [ReadExpressions.expressionWithNames.eq_def]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]



theorem nullary_effect (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment) (name : String) (program : CProg CVal Unit)
    (supplied : operations.effects name.toList [] = program) :
    (operations.profile layout).effect layout.fields environment (.call name.toList []) = program := by
  change EffectStatements.invokeWithNames (layout.names environment) operations.values
    operations.effects layout.fields (.call name.toList []) = _
  rw [EffectStatements.named_void_call_keeps_actual_arguments]
  simp only [ReadExpressions.argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  exact supplied

def failedTaskBody : List CStatement :=
  [.effect assertionExpression, .effect (.call "prime_eval_stack_pop".toList []),
   .return (some (.bool false))]

def returned (environment : ReadExpressions.Environment) (value : Bool) : ReadBlock.Result :=
  .finished (.returned environment (some (.bool value)))

theorem failed_task_keeps_current_assertion_then_pop (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment) (finish : Ptr)
    (knownFinish : environment "finish".toList = some (.ptr (some finish)))
    (outside : environment "g_prime_eval_stack_driver".toList = none) :
    StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 3
      environment failedTaskBody =
      (assertCurrent operations layout finish >>= fun _ => operations.pop >>= fun _ =>
        pure (returned environment false)) := by
  rw [failedTaskBody, effect_then_suffix operations layout environment assertionExpression
    (assertCurrent operations layout finish)
    (assertion_reads_after_task_reply operations layout environment finish knownFinish outside) 2 _]
  rw [effect_then_suffix operations layout environment (.call "prime_eval_stack_pop".toList [])
    operations.pop (nullary_effect operations layout environment "prime_eval_stack_pop" operations.pop (by rfl)) 1 _]
  rw [return_boolean_stops operations layout environment false 0 []]
  rfl

def taskTail (operations : BindOperations) (layout : BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) (finish : Ptr) : CProg CVal ReadBlock.Result := do
  let accepted ← operations.setTask (taskArguments input layout finish)
  if !accepted then do
    assertCurrent operations layout finish
    operations.pop
    pure (returned (finishEnvironment input finish) false)
  else pure (returned (finishEnvironment input finish) true)


theorem negated_branch_with_empty_else (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment) (condition : CExpr) (program : CProg CVal Bool)
    (actual : (operations.profile layout).read layout.fields environment (.unary .not condition) =
      (program >>= fun value => pure (.bool (!value))))
    (fuel : Nat) (yes rest : List CStatement) :
    StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 (fuel + 1)
      environment (.branch (.unary .not condition) yes [] :: rest) =
      (program >>= fun accepted => if !accepted then do
        let result ← StatementBlock.executeWith (operations.profile layout)
          (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 fuel environment yes
        ReadBlock.resume (fun updated => StatementBlock.executeWith (operations.profile layout)
          (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 fuel updated rest) result
      else StatementBlock.executeWith (operations.profile layout)
        (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 fuel environment rest) := by
  rw [branch_using_action operations layout environment (.unary .not condition)
    (program >>= fun value => pure (!value))
    (by simpa only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind] using actual)
    fuel yes [] rest]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext accepted
  cases accepted
  · simp only [Bool.not_false, if_true]
  · simp only [Bool.not_true, Bool.false_eq_true, if_false]
    rw [StatementBlock.executeWith_equation]
    simp only [Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]

theorem finish_has_no_cached_driver (input : NormalizeAtomConstructor.ConstructorInputs) (finish : Ptr) :
    finishEnvironment input finish "g_prime_eval_stack_driver".toList = none := by
  rfl

theorem task_suffix_keeps_both_replies (operations : BindOperations) (layout : BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) (finish : Ptr) :
    StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 4
      (finishEnvironment input finish) (bindSyntax.body.drop 13) =
      taskTail operations layout input finish := by
  change StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 4
      (finishEnvironment input finish)
      [.branch (.unary .not taskExpression) failedTaskBody [], .return (some (.bool true))] = _
  have actual := negate_boolean_action operations layout (finishEnvironment input finish)
    taskExpression (operations.setTask (taskArguments input layout finish))
    (task_call_keeps_complete_request operations layout input finish)
  have sourceRead : (operations.profile layout).read layout.fields (finishEnvironment input finish)
      (.unary .not taskExpression) =
      (operations.setTask (taskArguments input layout finish) >>= fun accepted => pure (.bool (!accepted))) := actual
  rw [negated_branch_with_empty_else operations layout (finishEnvironment input finish)
    taskExpression (operations.setTask (taskArguments input layout finish)) sourceRead
    3 failedTaskBody [.return (some (.bool true))]]
  rw [failed_task_keeps_current_assertion_then_pop operations layout (finishEnvironment input finish)
    finish (finish_lookup input finish) (finish_has_no_cached_driver input finish)]
  simp only [return_boolean_stops, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
    returned, ReadBlock.resume]
  rfl



theorem environment_flag_precedes_push_and_task (operations : BindOperations) (layout : BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) (finish : Ptr) :
    StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 6
      (finishEnvironment input finish) (bindSyntax.body.drop 11) =
      (CProg.store (finish + layout.frame.environmentInitialized) (.bool true) >>= fun _ =>
        operations.push finish >>= fun _ => taskTail operations layout input finish) := by
  change StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 6
      (finishEnvironment input finish)
      (.assign (finishField "env_initialized") (.bool true) ::
       .effect (.call "prime_eval_stack_push".toList [ident "finish"]) :: bindSyntax.body.drop 13) = _
  rw [store_then_suffix operations layout (finishEnvironment input finish) finish
    (finish_lookup input finish) "env_initialized" layout.frame.environmentInitialized
    (.bool true) (.bool true) (by rfl) (by rfl) 5 _]
  rw [effect_then_suffix operations layout (finishEnvironment input finish)
    (.call "prime_eval_stack_push".toList [ident "finish"]) (operations.push finish)
    (one_argument_effect operations layout (finishEnvironment input finish) "prime_eval_stack_push"
      (ident "finish") (.ptr (some finish)) (operations.push finish)
      (identifier_read operations layout (finishEnvironment input finish) "finish" _ (finish_lookup input finish)) (by rfl)) 4 _]
  rw [task_suffix_keeps_both_replies operations layout input finish]

def captureExpression : CExpr := .call "prime_eval_stack_capture_dynamic_env".toList
  [.unary .address (finishField "env"), ident "dynamic_env"]

def failedCaptureBody : List CStatement :=
  [.effect (.call "prime_eval_stack_frame_free".toList [ident "finish"]), .return (some (.bool false))]

theorem failed_capture_retires_actual_frame (operations : BindOperations) (layout : BindLayout)
    (environment : ReadExpressions.Environment) (finish : Ptr)
    (knownFinish : environment "finish".toList = some (.ptr (some finish))) (fuel : Nat) :
    StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 (fuel + 2)
      environment failedCaptureBody =
      (operations.retireFrame finish >>= fun _ => pure (returned environment false)) := by
  rw [failedCaptureBody, effect_then_suffix operations layout environment
    (.call "prime_eval_stack_frame_free".toList [ident "finish"]) (operations.retireFrame finish)
    (one_argument_effect operations layout environment "prime_eval_stack_frame_free" (ident "finish")
      (.ptr (some finish)) (operations.retireFrame finish)
      (identifier_read operations layout environment "finish" _ knownFinish) (by rfl)) (fuel + 1) _]
  rw [return_boolean_stops operations layout environment false fuel []]
  rfl

def captureTail (operations : BindOperations) (layout : BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) (finish : Ptr) : CProg CVal ReadBlock.Result := do
  let captured ← operations.captureDynamic (finish + layout.frame.environment) input.environment
  if !captured then do
    operations.retireFrame finish
    pure (returned (finishEnvironment input finish) false)
  else do
    CProg.store (finish + layout.frame.environmentInitialized) (.bool true)
    operations.push finish
    taskTail operations layout input finish

theorem capture_suffix_keeps_refusal_and_success (operations : BindOperations) (layout : BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) (finish : Ptr) :
    StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 7
      (finishEnvironment input finish) (bindSyntax.body.drop 10) =
      captureTail operations layout input finish := by
  change StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 7
      (finishEnvironment input finish)
      (.branch (.unary .not captureExpression) failedCaptureBody [] :: bindSyntax.body.drop 11) = _
  have actual := negate_boolean_action operations layout (finishEnvironment input finish)
    captureExpression (operations.captureDynamic (finish + layout.frame.environment) input.environment)
    (capture_keeps_actual_slots operations layout (finishEnvironment input finish) finish input.environment
      (finish_lookup input finish) (by rfl))
  have sourceRead : (operations.profile layout).read layout.fields (finishEnvironment input finish)
      (.unary .not captureExpression) =
      (operations.captureDynamic (finish + layout.frame.environment) input.environment >>= fun captured =>
        pure (.bool (!captured))) := actual
  rw [negated_branch_with_empty_else operations layout (finishEnvironment input finish)
    captureExpression (operations.captureDynamic (finish + layout.frame.environment) input.environment)
    sourceRead 6 failedCaptureBody (bindSyntax.body.drop 11)]
  rw [failed_capture_retires_actual_frame operations layout (finishEnvironment input finish) finish
    (finish_lookup input finish) 4]
  rw [environment_flag_precedes_push_and_task operations layout input finish]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, returned, ReadBlock.resume]
  rfl

theorem child_initialization_then_capture (operations : BindOperations) (layout : BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) (finish : Ptr) :
    StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 9
      (finishEnvironment input finish) (bindSyntax.body.drop 8) =
      (operations.initializeChild (finish + layout.frame.child) >>= fun _ =>
        CProg.store (finish + layout.frame.childInitialized) (.bool true) >>= fun _ =>
        captureTail operations layout input finish) := by
  change StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 9
      (finishEnvironment input finish)
      (.effect (.call "outcome_set_init".toList [.unary .address (finishField "child")]) ::
       .assign (finishField "child_initialized") (.bool true) :: bindSyntax.body.drop 10) = _
  rw [effect_then_suffix operations layout (finishEnvironment input finish)
    (.call "outcome_set_init".toList [.unary .address (finishField "child")])
    (operations.initializeChild (finish + layout.frame.child))
    (one_argument_effect operations layout (finishEnvironment input finish) "outcome_set_init"
      (.unary .address (finishField "child")) (.ptr (some (finish + layout.frame.child)))
      (operations.initializeChild (finish + layout.frame.child))
      (field_address_read operations layout (finishEnvironment input finish) finish (finish_lookup input finish)
        "child" layout.frame.child .embedded (by rfl)) (by rfl)) 8 _]
  rw [store_then_suffix operations layout (finishEnvironment input finish) finish
    (finish_lookup input finish) "child_initialized" layout.frame.childInitialized
    (.bool true) (.bool true) (by rfl) (by rfl) 7 _]
  rw [capture_suffix_keeps_refusal_and_success operations layout input finish]



theorem new_frame_keeps_bind_kind (operations : BindOperations) (layout : BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) :
    (operations.profile layout).read layout.fields (inputs input)
      (.call "prime_eval_stack_frame_new".toList [ident "PRIME_EVAL_STACK_FRAME_BIND_FINISH"]) =
      (operations.newFrame 0 >>= fun finish => pure (.ptr (some finish))) := by
  change ReadExpressions.expressionWithNames (layout.names (inputs input)) operations.values
      layout.fields (.call "prime_eval_stack_frame_new".toList [ident "PRIME_EVAL_STACK_FRAME_BIND_FINISH"]) = _
  rw [ReadExpressions.expressionWithNames.eq_def]
  simp only [ReadExpressions.argumentsWithNames.eq_def]
  rw [identifier_read operations layout (inputs input) "PRIME_EVAL_STACK_FRAME_BIND_FINISH" (.i32 0) (by rfl)]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rfl

theorem frame_pointer_initialization (operations : BindOperations) (layout : BindLayout) (finish : Ptr) :
    (operations.profile layout).initialValue ⟨"PrimeEvalStackFrame".toList, 1⟩ (.ptr (some finish)) =
      pure (.ptr (some finish)) := rfl

def allocatedTail (operations : BindOperations) (layout : BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) : CProg CVal ReadBlock.Result := do
  let finish ← operations.newFrame 0
  let result ← do
    CProg.store (finish + layout.frame.space) (.ptr input.space)
    CProg.store (finish + layout.frame.arena) (.ptr input.arena)
    CProg.store (finish + layout.frame.target) (.ptr input.target)
    CProg.store (finish + layout.frame.atom) (.ptr input.atom)
    CProg.store (finish + layout.frame.fuel) (.i32 input.fuel)
    CProg.store (finish + layout.frame.evaluator) (.u64 input.evaluator)
    operations.initializeChild (finish + layout.frame.child)
    CProg.store (finish + layout.frame.childInitialized) (.bool true)
    captureTail operations layout input finish
  pure (ReadBlock.restore "finish".toList ((inputs input) "finish".toList) result)

theorem allocation_suffix_preserves_actual_sequence (operations : BindOperations) (layout : BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) :
    StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 16
      (inputs input) (bindSyntax.body.drop 1) = allocatedTail operations layout input := by
  change StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 16
      (inputs input)
      (.declare ⟨"PrimeEvalStackFrame".toList, 1⟩ "finish".toList
        (.call "prime_eval_stack_frame_new".toList [ident "PRIME_EVAL_STACK_FRAME_BIND_FINISH"]) ::
        bindSyntax.body.drop 2) = _
  rw [StatementBlock.executeWith_equation]
  dsimp only
  rw [new_frame_keeps_bind_kind operations layout input]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  unfold allocatedTail
  congr 1
  funext finish
  rw [frame_pointer_initialization operations layout finish]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  change (StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 15
      (finishEnvironment input finish) (bindSyntax.body.drop 2) >>= fun result =>
        pure (ReadBlock.restore "finish".toList ((inputs input) "finish".toList) result)) = _
  rw [six_fields_keep_actual_inputs operations layout input finish,
    child_initialization_then_capture operations layout input finish]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq]

theorem ownership_call_uses_actual_target (operations : BindOperations) (layout : BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) :
    (operations.profile layout).read layout.fields (inputs input)
      (.call "prime_eval_stack_target_is_owned".toList [ident "target"]) =
      (operations.targetOwned input.target >>= fun admitted => pure (.bool admitted)) := by
  change ReadExpressions.expressionWithNames (layout.names (inputs input)) operations.values
    layout.fields (.call "prime_eval_stack_target_is_owned".toList [ident "target"]) = _
  rw [ReadExpressions.expressionWithNames.eq_def]
  simp only [ReadExpressions.argumentsWithNames.eq_def]
  rw [identifier_read operations layout (inputs input) "target" (.ptr input.target) (by rfl)]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rfl

theorem bind_boolean_choice {Answer Result : Type} (selected : Bool)
    (yes no : CProg CVal Answer) (continuation : Answer → CProg CVal Result) :
    Prog.bind (if selected then yes else no) continuation =
      (if selected then Prog.bind yes continuation else Prog.bind no continuation) := by
  cases selected <;> rfl

/-- Equality retains all services, typed stores and current driver reads,
including both refusal paths and lexical scope restoration. It is a source
interpreter comparison, not compiled-code or arbitrary callback verification. -/
theorem interpreted_bind_is_complete_operations (operations : BindOperations) (layout : BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) :
    interpretedBind operations layout input = bindOperations operations layout input := by
  unfold interpretedBind
  change StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 17
      (inputs input)
      (.branch (.unary .not (.call "prime_eval_stack_target_is_owned".toList [ident "target"]))
        [.return (some (.bool false))] [] :: bindSyntax.body.drop 1) = _
  have actual := negate_boolean_action operations layout (inputs input)
    (.call "prime_eval_stack_target_is_owned".toList [ident "target"])
    (operations.targetOwned input.target) (ownership_call_uses_actual_target operations layout input)
  have sourceRead : (operations.profile layout).read layout.fields (inputs input)
      (.unary .not (.call "prime_eval_stack_target_is_owned".toList [ident "target"])) =
      (operations.targetOwned input.target >>= fun admitted => pure (.bool (!admitted))) := actual
  rw [negated_branch_with_empty_else operations layout (inputs input)
    (.call "prime_eval_stack_target_is_owned".toList [ident "target"])
    (operations.targetOwned input.target) sourceRead 16 [.return (some (.bool false))]
    (bindSyntax.body.drop 1)]
  simp only [return_boolean_stops, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
  rw [allocation_suffix_preserves_actual_sequence operations layout input]
  simp only [bindOperations, allocatedTail, captureTail, taskTail, taskArguments, assertCurrent,
    returned, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, bind_boolean_choice]



/-- Admission is from the byte-retained body through the shared lexer and
parser. The entire body uses the named-current reader and existing block
interpreter; service internals, native ABI and nonlocal exits remain obligations. -/
theorem original_body_executes_complete_bind (operations : BindOperations) (layout : BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) :
    StatementBlock.executeParsedBody
      (fun body => StatementBlock.executeWith (operations.profile layout)
        (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 17
        (inputs input) body)
      (declaratorFunctionText? names source.toList) = bindOperations operations layout input := by
  rw [original_source_recognized, StatementBlock.execute_parsed_body_some]
  exact interpreted_bind_is_complete_operations operations layout input


namespace Controls

/-- The admitted operation catalogue does not manufacture a destination
for a malformed capture request. Native conversion and callback contracts
remain separate from this source-service signature. -/
theorem missing_capture_destination_rejected (operations : BindOperations)
    (source : Option Ptr) :
    operations.values "prime_eval_stack_capture_dynamic_env".toList
      [.ptr none, .ptr source] = CProg.undefined := rfl

theorem extra_capture_operand_rejected (operations : BindOperations)
    (destination extra : Ptr) (source : Option Ptr) :
    operations.values "prime_eval_stack_capture_dynamic_env".toList
      [.ptr (some destination), .ptr source, .ptr (some extra)] = CProg.undefined := rfl

theorem unsigned_frame_kind_rejected (operations : BindOperations) :
    operations.values "prime_eval_stack_frame_new".toList [.u32 0] = CProg.undefined := rfl

theorem extra_pop_operand_rejected (operations : BindOperations) (extra : Ptr) :
    operations.effects "prime_eval_stack_pop".toList [.ptr (some extra)] = CProg.undefined := rfl

theorem non_boolean_assertion_rejected (operations : BindOperations) :
    operations.effects "assert".toList [.i32 1] = CProg.undefined := rfl

/-- An ownership refusal stops before frame allocation, typed stores,
capture and publication, regardless of those services' definitions. -/
theorem ownership_refusal_precedes_frame_operations (operations : BindOperations)
    (layout : BindLayout) (input : NormalizeAtomConstructor.ConstructorInputs) :
    interpretedBind { operations with targetOwned := fun _ => pure false } layout input =
      pure (returned (inputs input) false) := by
  rw [interpreted_bind_is_complete_operations]
  simp only [bindOperations, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Bool.not_false, if_true,
    returned]

/-- Statement-interpreter fuel is not native execution fuel. A short
failure-body bound retains the assertion and pop but reports exhaustion
before the return, rather than silently claiming a false result. -/
theorem insufficient_failure_body_bound_keeps_effects (operations : BindOperations)
    (layout : BindLayout) (environment : ReadExpressions.Environment) (finish : Ptr)
    (knownFinish : environment "finish".toList = some (.ptr (some finish)))
    (outside : environment "g_prime_eval_stack_driver".toList = none) :
    StatementBlock.executeWith (operations.profile layout)
      (StatementBlock.fieldAssignment (operations.reader layout)) layout.fields 0 2
      environment failedTaskBody =
      (assertCurrent operations layout finish >>= fun _ => operations.pop >>= fun _ =>
        pure .exhausted) := by
  rw [failedTaskBody, effect_then_suffix operations layout environment assertionExpression
    (assertCurrent operations layout finish)
    (assertion_reads_after_task_reply operations layout environment finish knownFinish outside) 1 _]
  rw [effect_then_suffix operations layout environment (.call "prime_eval_stack_pop".toList [])
    operations.pop (nullary_effect operations layout environment "prime_eval_stack_pop" operations.pop (by rfl)) 0 _]
  rw [StatementBlock.executeWith_equation]

theorem exhaustion_is_not_refusal (environment : ReadExpressions.Environment) :
    ReadBlock.Result.exhausted ≠ returned environment false := by
  intro impossible
  cases impossible

/-- The complete BIND request retains signed fuel, the actual embedded
addresses and the wide evaluator identity. It is not NORMALIZE's request. -/
theorem request_keeps_signed_wide_and_embedded_inputs (layout : BindLayout) (finish : Ptr) :
    taskArguments Scheduling.Controls.input.toConstructorInputs layout finish =
      [.i32 0, .ptr none, .ptr (some ⟨2, 0⟩), .ptr (some ⟨3, 0⟩), .ptr none,
       .i32 (-2147483648), .bool true, .i32 (-1), .ptr (some (finish + layout.frame.child)),
       .ptr (some (finish + layout.frame.environment)), .ptr none, .u64 4294967303] := rfl

theorem request_has_twelve_arguments (input : NormalizeAtomConstructor.ConstructorInputs)
    (layout : BindLayout) (finish : Ptr) :
    (taskArguments input layout finish).length = 12 := rfl

end Controls

end Mettapedia.Languages.MeTTa.CeTTaNativeCost.BindSchedule

namespace Mettapedia.Languages.MeTTa.CeTTaNativeCost.TaskAdmission

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ReadExpressions
open ReadBlock (Result Flow resume)
open StatementBlock (AutomaticRegion)
open StatementBlock.ObjectBindings (Context Binding)

def ident (name : String) : CExpr := .identifier name.toList
def taskField (name : String) : CExpr := .field (ident "task") name.toList false
def driverField (name : String) : CExpr := .field (ident "driver") name.toList true

def names : TypeNames := ["bool".toList, "PrimeEvalStackTaskKind".toList,
  "Space".toList, "Arena".toList, "Atom".toList, "int".toList, "OutcomeSet".toList,
  "Bindings".toList, "uint64_t".toList, "PrimeEvalStackDriver".toList,
  "PrimeEvalStackTask".toList]

def failureBody : List CStatement :=
  [.effect (.call "prime_eval_stack_task_free".toList [.unary .address (ident "task")]),
   .return (some (.bool false))]

/-- The expected syntax is specified independently of the parser result.
It retains the automatic object, all field writes, the captured driver,
both capture refusals and both publication paths. -/
def taskSyntax : CDeclaratorFunction :=
  ⟨⟨"bool".toList, 0⟩, "prime_eval_stack_set_task".toList,
   [⟨⟨"PrimeEvalStackTaskKind".toList, false, []⟩, "kind".toList⟩,
    ⟨⟨"Space".toList, false, [false]⟩, "s".toList⟩,
    ⟨⟨"Arena".toList, false, [false]⟩, "a".toList⟩,
    ⟨⟨"Atom".toList, false, [false]⟩, "atom".toList⟩,
    ⟨⟨"Atom".toList, false, [false]⟩, "etype".toList⟩,
    ⟨⟨"int".toList, false, []⟩, "fuel".toList⟩,
    ⟨⟨"bool".toList, false, []⟩, "preserve_bindings".toList⟩,
    ⟨⟨"int".toList, false, []⟩, "strict_ready_argument".toList⟩,
    ⟨⟨"OutcomeSet".toList, false, [false]⟩, "target".toList⟩,
    ⟨⟨"Bindings".toList, true, [false]⟩, "dynamic_env".toList⟩,
    ⟨⟨"Bindings".toList, true, [false]⟩, "seed_env".toList⟩,
    ⟨⟨"uint64_t".toList, false, []⟩, "evaluator_id".toList⟩],
   [.declare ⟨"PrimeEvalStackDriver".toList, 1⟩ "driver".toList
      (ident "g_prime_eval_stack_driver"),
    .branch (.binary .or
      (.binary .or (.unary .not (ident "driver")) (driverField "task_ready"))
      (.unary .not (.call "prime_eval_stack_target_is_owned".toList [ident "target"])))
      [.return (some (.bool false))] [],
    .declareUninitialized ⟨"PrimeEvalStackTask".toList, 0⟩ "task".toList,
    .effect (.call "memset".toList
      [.unary .address (ident "task"), .decimal 0, .sizeOfExpr (ident "task")]),
    .assign (taskField "kind") (ident "kind"),
    .assign (taskField "pure_authority") (driverField "pure_authority"),
    .assign (taskField "space") (ident "s"),
    .assign (taskField "arena") (ident "a"),
    .assign (taskField "atom") (ident "atom"),
    .assign (taskField "etype") (ident "etype"),
    .assign (taskField "fuel") (ident "fuel"),
    .assign (taskField "preserve_bindings") (ident "preserve_bindings"),
    .assign (taskField "strict_ready_argument") (ident "strict_ready_argument"),
    .assign (taskField "target") (ident "target"),
    .assign (taskField "evaluator_id") (ident "evaluator_id"),
    .branch (.unary .not (.call "prime_eval_stack_capture_dynamic_env".toList
      [.unary .address (taskField "dynamic_env"), ident "dynamic_env"])) failureBody [],
    .assign (taskField "dynamic_env_initialized") (.bool true),
    .branch (ident "seed_env")
      [.branch (.unary .not (.call "bindings_clone".toList
        [.unary .address (taskField "seed_env"), ident "seed_env"])) failureBody [],
       .assign (taskField "seed_env_initialized") (.bool true)] [],
    .branch (driverField "control")
      [.branch (.unary .not (.call "prime_native_control_enqueue_task".toList
        [driverField "control", .unary .address (ident "task"), driverField "top"])) failureBody [],
       .effect (.postIncrement (driverField "continuation_generation")),
       .return (some (.bool true))] [],
    .assign (driverField "task") (ident "task"),
    .assign (driverField "task_ready") (.bool true),
    .effect (.postIncrement (driverField "continuation_generation")),
    .return (some (.bool true))]⟩

def source : String := "static bool prime_eval_stack_set_task(\n    PrimeEvalStackTaskKind kind, Space *s, Arena *a,\n    Atom *atom, Atom *etype, int fuel, bool preserve_bindings,\n    int strict_ready_argument, OutcomeSet *target,\n    const Bindings *dynamic_env, const Bindings *seed_env,\n    uint64_t evaluator_id) {\n    PrimeEvalStackDriver *driver = g_prime_eval_stack_driver;\n    if (!driver || driver->task_ready ||\n        !prime_eval_stack_target_is_owned(target))\n        return false;\n    PrimeEvalStackTask task;\n    memset(&task, 0, sizeof(task));\n    task.kind = kind;\n    task.pure_authority = driver->pure_authority;\n    task.space = s;\n    task.arena = a;\n    task.atom = atom;\n    task.etype = etype;\n    task.fuel = fuel;\n    task.preserve_bindings = preserve_bindings;\n    task.strict_ready_argument = strict_ready_argument;\n    task.target = target;\n    task.evaluator_id = evaluator_id;\n    if (!prime_eval_stack_capture_dynamic_env(\n            &task.dynamic_env, dynamic_env)) {\n        prime_eval_stack_task_free(&task);\n        return false;\n    }\n    task.dynamic_env_initialized = true;\n    if (seed_env) {\n        if (!bindings_clone(&task.seed_env, seed_env)) {\n            prime_eval_stack_task_free(&task);\n            return false;\n        }\n        task.seed_env_initialized = true;\n    }\n    if (driver->control) {\n        if (!prime_native_control_enqueue_task(\n                driver->control, &task, driver->top)) {\n            prime_eval_stack_task_free(&task);\n            return false;\n        }\n        driver->continuation_generation++;\n        return true;\n    }\n    driver->task = task;\n    driver->task_ready = true;\n    driver->continuation_generation++;\n    return true;\n}"
def characters : List Char := native_c_characters% "static bool prime_eval_stack_set_task(\n    PrimeEvalStackTaskKind kind, Space *s, Arena *a,\n    Atom *atom, Atom *etype, int fuel, bool preserve_bindings,\n    int strict_ready_argument, OutcomeSet *target,\n    const Bindings *dynamic_env, const Bindings *seed_env,\n    uint64_t evaluator_id) {\n    PrimeEvalStackDriver *driver = g_prime_eval_stack_driver;\n    if (!driver || driver->task_ready ||\n        !prime_eval_stack_target_is_owned(target))\n        return false;\n    PrimeEvalStackTask task;\n    memset(&task, 0, sizeof(task));\n    task.kind = kind;\n    task.pure_authority = driver->pure_authority;\n    task.space = s;\n    task.arena = a;\n    task.atom = atom;\n    task.etype = etype;\n    task.fuel = fuel;\n    task.preserve_bindings = preserve_bindings;\n    task.strict_ready_argument = strict_ready_argument;\n    task.target = target;\n    task.evaluator_id = evaluator_id;\n    if (!prime_eval_stack_capture_dynamic_env(\n            &task.dynamic_env, dynamic_env)) {\n        prime_eval_stack_task_free(&task);\n        return false;\n    }\n    task.dynamic_env_initialized = true;\n    if (seed_env) {\n        if (!bindings_clone(&task.seed_env, seed_env)) {\n            prime_eval_stack_task_free(&task);\n            return false;\n        }\n        task.seed_env_initialized = true;\n    }\n    if (driver->control) {\n        if (!prime_native_control_enqueue_task(\n                driver->control, &task, driver->top)) {\n            prime_eval_stack_task_free(&task);\n            return false;\n        }\n        driver->continuation_generation++;\n        return true;\n    }\n    driver->task = task;\n    driver->task_ready = true;\n    driver->continuation_generation++;\n    return true;\n}"

theorem characters_are_actual_source : source.toList = characters := by
  native_c_character_reflexivity

private def lexCharacters0 : List Char := native_c_characters% "static bool prime_eval_stack_set_task(\n"
private def lexTokens0 : List Token := [.identifier (native_c_characters% "static"), .identifier (native_c_characters% "bool"), .identifier (native_c_characters% "prime_eval_stack_set_task"), .punctuation (native_c_characters% "(")]
private theorem lexPiece0 : lexCharacters0.foldl step initial = completed lexTokens0 := by
  native_c_parser_reflexivity

private def lexCharacters1 : List Char := native_c_characters% "    PrimeEvalStackTaskKind kind, Space *s, Arena *a,\n"
private def lexTokens1 : List Token := [.identifier (native_c_characters% "PrimeEvalStackTaskKind"), .identifier (native_c_characters% "kind"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "Space"), .punctuation (native_c_characters% "*"), .identifier (native_c_characters% "s"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "Arena"), .punctuation (native_c_characters% "*"), .identifier (native_c_characters% "a"), .punctuation (native_c_characters% ",")]
private theorem lexPiece1 : lexCharacters1.foldl step initial = completed lexTokens1 := by
  native_c_parser_reflexivity

private def lexCharacters2 : List Char := native_c_characters% "    Atom *atom, Atom *etype, int fuel, bool preserve_bindings,\n"
private def lexTokens2 : List Token := [.identifier (native_c_characters% "Atom"), .punctuation (native_c_characters% "*"), .identifier (native_c_characters% "atom"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "Atom"), .punctuation (native_c_characters% "*"), .identifier (native_c_characters% "etype"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "int"), .identifier (native_c_characters% "fuel"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "bool"), .identifier (native_c_characters% "preserve_bindings"), .punctuation (native_c_characters% ",")]
private theorem lexPiece2 : lexCharacters2.foldl step initial = completed lexTokens2 := by
  native_c_parser_reflexivity

private def lexCharacters3 : List Char := native_c_characters% "    int strict_ready_argument, OutcomeSet *target,\n"
private def lexTokens3 : List Token := [.identifier (native_c_characters% "int"), .identifier (native_c_characters% "strict_ready_argument"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "OutcomeSet"), .punctuation (native_c_characters% "*"), .identifier (native_c_characters% "target"), .punctuation (native_c_characters% ",")]
private theorem lexPiece3 : lexCharacters3.foldl step initial = completed lexTokens3 := by
  native_c_parser_reflexivity

private def lexCharacters4 : List Char := native_c_characters% "    const Bindings *dynamic_env, const Bindings *seed_env,\n"
private def lexTokens4 : List Token := [.identifier (native_c_characters% "const"), .identifier (native_c_characters% "Bindings"), .punctuation (native_c_characters% "*"), .identifier (native_c_characters% "dynamic_env"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "const"), .identifier (native_c_characters% "Bindings"), .punctuation (native_c_characters% "*"), .identifier (native_c_characters% "seed_env"), .punctuation (native_c_characters% ",")]
private theorem lexPiece4 : lexCharacters4.foldl step initial = completed lexTokens4 := by
  native_c_parser_reflexivity

private def lexCharacters5 : List Char := native_c_characters% "    uint64_t evaluator_id) {\n"
private def lexTokens5 : List Token := [.identifier (native_c_characters% "uint64_t"), .identifier (native_c_characters% "evaluator_id"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% "{")]
private theorem lexPiece5 : lexCharacters5.foldl step initial = completed lexTokens5 := by
  native_c_parser_reflexivity

private def lexCharacters6 : List Char := native_c_characters% "    PrimeEvalStackDriver *driver = g_prime_eval_stack_driver;\n"
private def lexTokens6 : List Token := [.identifier (native_c_characters% "PrimeEvalStackDriver"), .punctuation (native_c_characters% "*"), .identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "g_prime_eval_stack_driver"), .punctuation (native_c_characters% ";")]
private theorem lexPiece6 : lexCharacters6.foldl step initial = completed lexTokens6 := by
  native_c_parser_reflexivity

private def lexCharacters7 : List Char := native_c_characters% "    if (!driver || driver->task_ready ||\n"
private def lexTokens7 : List Token := [.identifier (native_c_characters% "if"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "!"), .identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "||"), .identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "task_ready"), .punctuation (native_c_characters% "||")]
private theorem lexPiece7 : lexCharacters7.foldl step initial = completed lexTokens7 := by
  native_c_parser_reflexivity

private def lexCharacters8 : List Char := native_c_characters% "        !prime_eval_stack_target_is_owned(target))\n"
private def lexTokens8 : List Token := [.punctuation (native_c_characters% "!"), .identifier (native_c_characters% "prime_eval_stack_target_is_owned"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "target"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ")")]
private theorem lexPiece8 : lexCharacters8.foldl step initial = completed lexTokens8 := by
  native_c_parser_reflexivity

private def lexCharacters9 : List Char := native_c_characters% "        return false;\n"
private def lexTokens9 : List Token := [.identifier (native_c_characters% "return"), .identifier (native_c_characters% "false"), .punctuation (native_c_characters% ";")]
private theorem lexPiece9 : lexCharacters9.foldl step initial = completed lexTokens9 := by
  native_c_parser_reflexivity

private def lexCharacters10 : List Char := native_c_characters% "    PrimeEvalStackTask task;\n"
private def lexTokens10 : List Token := [.identifier (native_c_characters% "PrimeEvalStackTask"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% ";")]
private theorem lexPiece10 : lexCharacters10.foldl step initial = completed lexTokens10 := by
  native_c_parser_reflexivity

private def lexCharacters11 : List Char := native_c_characters% "    memset(&task, 0, sizeof(task));\n"
private def lexTokens11 : List Token := [.identifier (native_c_characters% "memset"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "&"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% ","), .number (native_c_characters% "0"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "sizeof"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece11 : lexCharacters11.foldl step initial = completed lexTokens11 := by
  native_c_parser_reflexivity

private def lexCharacters12 : List Char := native_c_characters% "    task.kind = kind;\n"
private def lexTokens12 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "kind"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "kind"), .punctuation (native_c_characters% ";")]
private theorem lexPiece12 : lexCharacters12.foldl step initial = completed lexTokens12 := by
  native_c_parser_reflexivity

private def lexCharacters13 : List Char := native_c_characters% "    task.pure_authority = driver->pure_authority;\n"
private def lexTokens13 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "pure_authority"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "pure_authority"), .punctuation (native_c_characters% ";")]
private theorem lexPiece13 : lexCharacters13.foldl step initial = completed lexTokens13 := by
  native_c_parser_reflexivity

private def lexCharacters14 : List Char := native_c_characters% "    task.space = s;\n"
private def lexTokens14 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "space"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "s"), .punctuation (native_c_characters% ";")]
private theorem lexPiece14 : lexCharacters14.foldl step initial = completed lexTokens14 := by
  native_c_parser_reflexivity

private def lexCharacters15 : List Char := native_c_characters% "    task.arena = a;\n"
private def lexTokens15 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "arena"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "a"), .punctuation (native_c_characters% ";")]
private theorem lexPiece15 : lexCharacters15.foldl step initial = completed lexTokens15 := by
  native_c_parser_reflexivity

private def lexCharacters16 : List Char := native_c_characters% "    task.atom = atom;\n"
private def lexTokens16 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "atom"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "atom"), .punctuation (native_c_characters% ";")]
private theorem lexPiece16 : lexCharacters16.foldl step initial = completed lexTokens16 := by
  native_c_parser_reflexivity

private def lexCharacters17 : List Char := native_c_characters% "    task.etype = etype;\n"
private def lexTokens17 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "etype"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "etype"), .punctuation (native_c_characters% ";")]
private theorem lexPiece17 : lexCharacters17.foldl step initial = completed lexTokens17 := by
  native_c_parser_reflexivity

private def lexCharacters18 : List Char := native_c_characters% "    task.fuel = fuel;\n"
private def lexTokens18 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "fuel"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "fuel"), .punctuation (native_c_characters% ";")]
private theorem lexPiece18 : lexCharacters18.foldl step initial = completed lexTokens18 := by
  native_c_parser_reflexivity

private def lexCharacters19 : List Char := native_c_characters% "    task.preserve_bindings = preserve_bindings;\n"
private def lexTokens19 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "preserve_bindings"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "preserve_bindings"), .punctuation (native_c_characters% ";")]
private theorem lexPiece19 : lexCharacters19.foldl step initial = completed lexTokens19 := by
  native_c_parser_reflexivity

private def lexCharacters20 : List Char := native_c_characters% "    task.strict_ready_argument = strict_ready_argument;\n"
private def lexTokens20 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "strict_ready_argument"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "strict_ready_argument"), .punctuation (native_c_characters% ";")]
private theorem lexPiece20 : lexCharacters20.foldl step initial = completed lexTokens20 := by
  native_c_parser_reflexivity

private def lexCharacters21 : List Char := native_c_characters% "    task.target = target;\n"
private def lexTokens21 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "target"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "target"), .punctuation (native_c_characters% ";")]
private theorem lexPiece21 : lexCharacters21.foldl step initial = completed lexTokens21 := by
  native_c_parser_reflexivity

private def lexCharacters22 : List Char := native_c_characters% "    task.evaluator_id = evaluator_id;\n"
private def lexTokens22 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "evaluator_id"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "evaluator_id"), .punctuation (native_c_characters% ";")]
private theorem lexPiece22 : lexCharacters22.foldl step initial = completed lexTokens22 := by
  native_c_parser_reflexivity

private def lexCharacters23 : List Char := native_c_characters% "    if (!prime_eval_stack_capture_dynamic_env(\n"
private def lexTokens23 : List Token := [.identifier (native_c_characters% "if"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "!"), .identifier (native_c_characters% "prime_eval_stack_capture_dynamic_env"), .punctuation (native_c_characters% "(")]
private theorem lexPiece23 : lexCharacters23.foldl step initial = completed lexTokens23 := by
  native_c_parser_reflexivity

private def lexCharacters24 : List Char := native_c_characters% "            &task.dynamic_env, dynamic_env)) {\n"
private def lexTokens24 : List Token := [.punctuation (native_c_characters% "&"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "dynamic_env"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "dynamic_env"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% "{")]
private theorem lexPiece24 : lexCharacters24.foldl step initial = completed lexTokens24 := by
  native_c_parser_reflexivity

private def lexCharacters25 : List Char := native_c_characters% "        prime_eval_stack_task_free(&task);\n"
private def lexTokens25 : List Token := [.identifier (native_c_characters% "prime_eval_stack_task_free"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "&"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece25 : lexCharacters25.foldl step initial = completed lexTokens25 := by
  native_c_parser_reflexivity

private def lexCharacters26 : List Char := native_c_characters% "        return false;\n"
private def lexTokens26 : List Token := [.identifier (native_c_characters% "return"), .identifier (native_c_characters% "false"), .punctuation (native_c_characters% ";")]
private theorem lexPiece26 : lexCharacters26.foldl step initial = completed lexTokens26 := by
  native_c_parser_reflexivity

private def lexCharacters27 : List Char := native_c_characters% "    }\n"
private def lexTokens27 : List Token := [.punctuation (native_c_characters% "}")]
private theorem lexPiece27 : lexCharacters27.foldl step initial = completed lexTokens27 := by
  native_c_parser_reflexivity

private def lexCharacters28 : List Char := native_c_characters% "    task.dynamic_env_initialized = true;\n"
private def lexTokens28 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "dynamic_env_initialized"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "true"), .punctuation (native_c_characters% ";")]
private theorem lexPiece28 : lexCharacters28.foldl step initial = completed lexTokens28 := by
  native_c_parser_reflexivity

private def lexCharacters29 : List Char := native_c_characters% "    if (seed_env) {\n"
private def lexTokens29 : List Token := [.identifier (native_c_characters% "if"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "seed_env"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% "{")]
private theorem lexPiece29 : lexCharacters29.foldl step initial = completed lexTokens29 := by
  native_c_parser_reflexivity

private def lexCharacters30 : List Char := native_c_characters% "        if (!bindings_clone(&task.seed_env, seed_env)) {\n"
private def lexTokens30 : List Token := [.identifier (native_c_characters% "if"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "!"), .identifier (native_c_characters% "bindings_clone"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "&"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "seed_env"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "seed_env"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% "{")]
private theorem lexPiece30 : lexCharacters30.foldl step initial = completed lexTokens30 := by
  native_c_parser_reflexivity

private def lexCharacters31 : List Char := native_c_characters% "            prime_eval_stack_task_free(&task);\n"
private def lexTokens31 : List Token := [.identifier (native_c_characters% "prime_eval_stack_task_free"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "&"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece31 : lexCharacters31.foldl step initial = completed lexTokens31 := by
  native_c_parser_reflexivity

private def lexCharacters32 : List Char := native_c_characters% "            return false;\n"
private def lexTokens32 : List Token := [.identifier (native_c_characters% "return"), .identifier (native_c_characters% "false"), .punctuation (native_c_characters% ";")]
private theorem lexPiece32 : lexCharacters32.foldl step initial = completed lexTokens32 := by
  native_c_parser_reflexivity

private def lexCharacters33 : List Char := native_c_characters% "        }\n"
private def lexTokens33 : List Token := [.punctuation (native_c_characters% "}")]
private theorem lexPiece33 : lexCharacters33.foldl step initial = completed lexTokens33 := by
  native_c_parser_reflexivity

private def lexCharacters34 : List Char := native_c_characters% "        task.seed_env_initialized = true;\n"
private def lexTokens34 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "seed_env_initialized"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "true"), .punctuation (native_c_characters% ";")]
private theorem lexPiece34 : lexCharacters34.foldl step initial = completed lexTokens34 := by
  native_c_parser_reflexivity

private def lexCharacters35 : List Char := native_c_characters% "    }\n"
private def lexTokens35 : List Token := [.punctuation (native_c_characters% "}")]
private theorem lexPiece35 : lexCharacters35.foldl step initial = completed lexTokens35 := by
  native_c_parser_reflexivity

private def lexCharacters36 : List Char := native_c_characters% "    if (driver->control) {\n"
private def lexTokens36 : List Token := [.identifier (native_c_characters% "if"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "control"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% "{")]
private theorem lexPiece36 : lexCharacters36.foldl step initial = completed lexTokens36 := by
  native_c_parser_reflexivity

private def lexCharacters37 : List Char := native_c_characters% "        if (!prime_native_control_enqueue_task(\n"
private def lexTokens37 : List Token := [.identifier (native_c_characters% "if"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "!"), .identifier (native_c_characters% "prime_native_control_enqueue_task"), .punctuation (native_c_characters% "(")]
private theorem lexPiece37 : lexCharacters37.foldl step initial = completed lexTokens37 := by
  native_c_parser_reflexivity

private def lexCharacters38 : List Char := native_c_characters% "                driver->control, &task, driver->top)) {\n"
private def lexTokens38 : List Token := [.identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "control"), .punctuation (native_c_characters% ","), .punctuation (native_c_characters% "&"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "top"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% "{")]
private theorem lexPiece38 : lexCharacters38.foldl step initial = completed lexTokens38 := by
  native_c_parser_reflexivity

private def lexCharacters39 : List Char := native_c_characters% "            prime_eval_stack_task_free(&task);\n"
private def lexTokens39 : List Token := [.identifier (native_c_characters% "prime_eval_stack_task_free"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "&"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece39 : lexCharacters39.foldl step initial = completed lexTokens39 := by
  native_c_parser_reflexivity

private def lexCharacters40 : List Char := native_c_characters% "            return false;\n"
private def lexTokens40 : List Token := [.identifier (native_c_characters% "return"), .identifier (native_c_characters% "false"), .punctuation (native_c_characters% ";")]
private theorem lexPiece40 : lexCharacters40.foldl step initial = completed lexTokens40 := by
  native_c_parser_reflexivity

private def lexCharacters41 : List Char := native_c_characters% "        }\n"
private def lexTokens41 : List Token := [.punctuation (native_c_characters% "}")]
private theorem lexPiece41 : lexCharacters41.foldl step initial = completed lexTokens41 := by
  native_c_parser_reflexivity

private def lexCharacters42 : List Char := native_c_characters% "        driver->continuation_generation++;\n"
private def lexTokens42 : List Token := [.identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "continuation_generation"), .punctuation (native_c_characters% "++"), .punctuation (native_c_characters% ";")]
private theorem lexPiece42 : lexCharacters42.foldl step initial = completed lexTokens42 := by
  native_c_parser_reflexivity

private def lexCharacters43 : List Char := native_c_characters% "        return true;\n"
private def lexTokens43 : List Token := [.identifier (native_c_characters% "return"), .identifier (native_c_characters% "true"), .punctuation (native_c_characters% ";")]
private theorem lexPiece43 : lexCharacters43.foldl step initial = completed lexTokens43 := by
  native_c_parser_reflexivity

private def lexCharacters44 : List Char := native_c_characters% "    }\n"
private def lexTokens44 : List Token := [.punctuation (native_c_characters% "}")]
private theorem lexPiece44 : lexCharacters44.foldl step initial = completed lexTokens44 := by
  native_c_parser_reflexivity

private def lexCharacters45 : List Char := native_c_characters% "    driver->task = task;\n"
private def lexTokens45 : List Token := [.identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% ";")]
private theorem lexPiece45 : lexCharacters45.foldl step initial = completed lexTokens45 := by
  native_c_parser_reflexivity

private def lexCharacters46 : List Char := native_c_characters% "    driver->task_ready = true;\n"
private def lexTokens46 : List Token := [.identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "task_ready"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "true"), .punctuation (native_c_characters% ";")]
private theorem lexPiece46 : lexCharacters46.foldl step initial = completed lexTokens46 := by
  native_c_parser_reflexivity

private def lexCharacters47 : List Char := native_c_characters% "    driver->continuation_generation++;\n"
private def lexTokens47 : List Token := [.identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "continuation_generation"), .punctuation (native_c_characters% "++"), .punctuation (native_c_characters% ";")]
private theorem lexPiece47 : lexCharacters47.foldl step initial = completed lexTokens47 := by
  native_c_parser_reflexivity

private def lexCharacters48 : List Char := native_c_characters% "    return true;\n"
private def lexTokens48 : List Token := [.identifier (native_c_characters% "return"), .identifier (native_c_characters% "true"), .punctuation (native_c_characters% ";")]
private theorem lexPiece48 : lexCharacters48.foldl step initial = completed lexTokens48 := by
  native_c_parser_reflexivity

private def lexCharacters49 : List Char := native_c_characters% "}"
private def lexTokens49 : List Token := [.punctuation (native_c_characters% "}")]
private theorem lexPiece49 : lexCharacters49.foldl step initial = completed lexTokens49 := by
  native_c_parser_reflexivity

private def sourcePieces : List (List Char × List Token) := [(lexCharacters0, lexTokens0), (lexCharacters1, lexTokens1), (lexCharacters2, lexTokens2), (lexCharacters3, lexTokens3), (lexCharacters4, lexTokens4), (lexCharacters5, lexTokens5), (lexCharacters6, lexTokens6), (lexCharacters7, lexTokens7), (lexCharacters8, lexTokens8), (lexCharacters9, lexTokens9), (lexCharacters10, lexTokens10), (lexCharacters11, lexTokens11), (lexCharacters12, lexTokens12), (lexCharacters13, lexTokens13), (lexCharacters14, lexTokens14), (lexCharacters15, lexTokens15), (lexCharacters16, lexTokens16), (lexCharacters17, lexTokens17), (lexCharacters18, lexTokens18), (lexCharacters19, lexTokens19), (lexCharacters20, lexTokens20), (lexCharacters21, lexTokens21), (lexCharacters22, lexTokens22), (lexCharacters23, lexTokens23), (lexCharacters24, lexTokens24), (lexCharacters25, lexTokens25), (lexCharacters26, lexTokens26), (lexCharacters27, lexTokens27), (lexCharacters28, lexTokens28), (lexCharacters29, lexTokens29), (lexCharacters30, lexTokens30), (lexCharacters31, lexTokens31), (lexCharacters32, lexTokens32), (lexCharacters33, lexTokens33), (lexCharacters34, lexTokens34), (lexCharacters35, lexTokens35), (lexCharacters36, lexTokens36), (lexCharacters37, lexTokens37), (lexCharacters38, lexTokens38), (lexCharacters39, lexTokens39), (lexCharacters40, lexTokens40), (lexCharacters41, lexTokens41), (lexCharacters42, lexTokens42), (lexCharacters43, lexTokens43), (lexCharacters44, lexTokens44), (lexCharacters45, lexTokens45), (lexCharacters46, lexTokens46), (lexCharacters47, lexTokens47), (lexCharacters48, lexTokens48), (lexCharacters49, lexTokens49)]

private theorem characters_from_pieces : sourcePieces.flatMap Prod.fst = characters := by
  native_c_parser_reflexivity

def tokens : List Token := sourcePieces.flatMap Prod.snd

theorem actual_characters_lexed : lex characters = .ok tokens := by
  rw [← characters_from_pieces]
  apply lex_of_completed
  apply completed_pieces sourcePieces
  simp only [sourcePieces, List.forall_cons]
  exact ⟨lexPiece0, lexPiece1, lexPiece2, lexPiece3, lexPiece4, lexPiece5, lexPiece6, lexPiece7, lexPiece8, lexPiece9, lexPiece10, lexPiece11, lexPiece12, lexPiece13, lexPiece14, lexPiece15, lexPiece16, lexPiece17, lexPiece18, lexPiece19, lexPiece20, lexPiece21, lexPiece22, lexPiece23, lexPiece24, lexPiece25, lexPiece26, lexPiece27, lexPiece28, lexPiece29, lexPiece30, lexPiece31, lexPiece32, lexPiece33, lexPiece34, lexPiece35, lexPiece36, lexPiece37, lexPiece38, lexPiece39, lexPiece40, lexPiece41, lexPiece42, lexPiece43, lexPiece44, lexPiece45, lexPiece46, lexPiece47, lexPiece48, lexPiece49, by trivial⟩

theorem actual_tokens_parsed :
    functionUsing? (declaratorParameter? names) (2 * tokens.length + 4) names
      (ordinaryFunctionTokens tokens) = some (taskSyntax, []) := by
  native_c_parser_reflexivity

theorem actual_task_parses : declaratorFunctionText? names characters = some taskSyntax :=
  function_text_using_of_parts (declaratorParameter? names) names characters tokens taskSyntax
    actual_characters_lexed actual_tokens_parsed

theorem original_source_recognized :
    declaratorFunctionText? names source.toList = some taskSyntax := by
  rw [characters_are_actual_source]
  exact actual_task_parses

private def type (name : String) (depth : Nat := 0) : CType := ⟨name.toList, depth⟩

/-- Logical cell offsets and native byte extent have separate meanings.
The physical realization supplies ownership, alignment and encoding laws. -/
structure TaskLayout where
  currentDriver : Ptr
  taskOffset : Name → Nat
  driverOffset : Name → Nat
  taskCells : Nat
  taskBytes : Nat
  taskBytesBound : taskBytes < 2 ^ 64

def taskFields (layout : TaskLayout) : Layout := fun name =>
  if name = "kind".toList then some ⟨layout.taskOffset name, .word⟩ else
  if name = "pure_authority".toList then some ⟨layout.taskOffset name, .boolean⟩ else
  if name = "space".toList then some ⟨layout.taskOffset name, .pointer⟩ else
  if name = "arena".toList then some ⟨layout.taskOffset name, .pointer⟩ else
  if name = "atom".toList then some ⟨layout.taskOffset name, .pointer⟩ else
  if name = "etype".toList then some ⟨layout.taskOffset name, .pointer⟩ else
  if name = "fuel".toList then some ⟨layout.taskOffset name, .signedWord⟩ else
  if name = "preserve_bindings".toList then some ⟨layout.taskOffset name, .boolean⟩ else
  if name = "strict_ready_argument".toList then some ⟨layout.taskOffset name, .signedWord⟩ else
  if name = "target".toList then some ⟨layout.taskOffset name, .pointer⟩ else
  if name = "dynamic_env".toList then some ⟨layout.taskOffset name, .embedded⟩ else
  if name = "dynamic_env_initialized".toList then some ⟨layout.taskOffset name, .boolean⟩ else
  if name = "seed_env".toList then some ⟨layout.taskOffset name, .embedded⟩ else
  if name = "seed_env_initialized".toList then some ⟨layout.taskOffset name, .boolean⟩ else
  if name = "evaluator_id".toList then some ⟨layout.taskOffset name, .word64⟩ else
  if name = "control_key".toList then some ⟨layout.taskOffset name, .pointer⟩ else
  if name = "control_scoring".toList then some ⟨layout.taskOffset name, .boolean⟩ else
  none

def driverFields (layout : TaskLayout) : Layout := fun name =>
  if name = "task_ready".toList then some ⟨layout.driverOffset name, .boolean⟩ else
  if name = "pure_authority".toList then some ⟨layout.driverOffset name, .boolean⟩ else
  if name = "task".toList then some ⟨layout.driverOffset name, .embedded⟩ else
  if name = "control".toList then some ⟨layout.driverOffset name, .pointer⟩ else
  if name = "top".toList then some ⟨layout.driverOffset name, .pointer⟩ else
  if name = "continuation_generation".toList then some ⟨layout.driverOffset name, .word64⟩ else
  none

def fieldTypes : ScalarBytes.FieldTypes := fun owner name =>
  if owner = type "PrimeEvalStackTask" then
    if name = "kind".toList then some (type "PrimeEvalStackTaskKind" 0) else
    if name = "pure_authority".toList then some (type "bool" 0) else
    if name = "space".toList then some (type "Space" 1) else
    if name = "arena".toList then some (type "Arena" 1) else
    if name = "atom".toList then some (type "Atom" 1) else
    if name = "etype".toList then some (type "Atom" 1) else
    if name = "fuel".toList then some (type "int" 0) else
    if name = "preserve_bindings".toList then some (type "bool" 0) else
    if name = "strict_ready_argument".toList then some (type "int" 0) else
    if name = "target".toList then some (type "OutcomeSet" 1) else
    if name = "dynamic_env".toList then some (type "Bindings" 0) else
    if name = "dynamic_env_initialized".toList then some (type "bool" 0) else
    if name = "seed_env".toList then some (type "Bindings" 0) else
    if name = "seed_env_initialized".toList then some (type "bool" 0) else
    if name = "evaluator_id".toList then some (type "uint64_t" 0) else
    if name = "control_key".toList then some (type "Atom" 1) else
    if name = "control_scoring".toList then some (type "bool" 0) else
    none
  else
  if owner = type "PrimeEvalStackDriver" then
    if name = "task_ready".toList then some (type "bool" 0) else
    if name = "pure_authority".toList then some (type "bool" 0) else
    if name = "task".toList then some (type "PrimeEvalStackTask" 0) else
    if name = "control".toList then some (type "PrimeNativeControl" 1) else
    if name = "top".toList then some (type "PrimeEvalStackFrame" 1) else
    if name = "continuation_generation".toList then some (type "uint64_t" 0) else
    none
  else
    none

/-- The enum input uses the explicitly admitted native unsigned representation.
Caller conversion to this type is a separate source-composition obligation. -/
structure TaskInputs where
  kind : UInt32
  s : Option Ptr
  a : Option Ptr
  atom : Option Ptr
  etype : Option Ptr
  fuel : Int32
  preserve_bindings : Bool
  strict_ready_argument : Int32
  target : Option Ptr
  dynamic_env : Option Ptr
  seed_env : Option Ptr
  evaluator_id : UInt64

def inputContext (input : TaskInputs) : Context := fun name =>
  if name = "kind".toList then
    some (.scalar (type "PrimeEvalStackTaskKind" 0) (some (.u32 input.kind))) else
  if name = "s".toList then
    some (.scalar (type "Space" 1) (some (.ptr input.s))) else
  if name = "a".toList then
    some (.scalar (type "Arena" 1) (some (.ptr input.a))) else
  if name = "atom".toList then
    some (.scalar (type "Atom" 1) (some (.ptr input.atom))) else
  if name = "etype".toList then
    some (.scalar (type "Atom" 1) (some (.ptr input.etype))) else
  if name = "fuel".toList then
    some (.scalar (type "int" 0) (some (.i32 input.fuel))) else
  if name = "preserve_bindings".toList then
    some (.scalar (type "bool" 0) (some (.bool input.preserve_bindings))) else
  if name = "strict_ready_argument".toList then
    some (.scalar (type "int" 0) (some (.i32 input.strict_ready_argument))) else
  if name = "target".toList then
    some (.scalar (type "OutcomeSet" 1) (some (.ptr input.target))) else
  if name = "dynamic_env".toList then
    some (.scalar (type "Bindings" 1) (some (.ptr input.dynamic_env))) else
  if name = "seed_env".toList then
    some (.scalar (type "Bindings" 1) (some (.ptr input.seed_env))) else
  if name = "evaluator_id".toList then
    some (.scalar (type "uint64_t" 0) (some (.u64 input.evaluator_id))) else
  none

/-- Inner providers retain actual nullable references and their complete state
transitions. No whole-constructor service or successful-result assumption is
substituted for the original control flow. -/
structure TaskOperations where
  targetOwned : Option Ptr → CProg CVal Bool
  captureDynamic : Ptr → Option Ptr → CProg CVal Bool
  cloneBindings : Ptr → Option Ptr → CProg CVal Bool
  enqueue : Option Ptr → Ptr → Option Ptr → CProg CVal Bool
  zeroTask : Ptr → UInt64 → CProg CVal Unit
  releaseTask : Ptr → CProg CVal Unit
  region : AutomaticRegion Context

private def boolResult (operation : CProg CVal Bool) : CProg CVal CVal :=
  operation >>= fun accepted => pure (.bool accepted)

def calls (operations : TaskOperations) : Calls := fun name arguments =>
  if name = "prime_eval_stack_target_is_owned".toList then match arguments with
    | [.ptr target] => boolResult (operations.targetOwned target)
    | _ => CProg.undefined
  else if name = "prime_eval_stack_capture_dynamic_env".toList then match arguments with
    | [.ptr (some destination), .ptr source] => boolResult (operations.captureDynamic destination source)
    | _ => CProg.undefined
  else if name = "bindings_clone".toList then match arguments with
    | [.ptr (some destination), .ptr source] => boolResult (operations.cloneBindings destination source)
    | _ => CProg.undefined
  else if name = "prime_native_control_enqueue_task".toList then match arguments with
    | [.ptr control, .ptr (some task), .ptr top] => boolResult (operations.enqueue control task top)
    | _ => CProg.undefined
  else CProg.undefined

def effects (operations : TaskOperations) : CallService Unit := fun name arguments =>
  if name = "memset".toList then match arguments with
    | [.ptr (some task), .i32 zero, .u64 bytes] =>
        if zero = 0 then operations.zeroTask task bytes else CProg.undefined
    | _ => CProg.undefined
  else if name = "prime_eval_stack_task_free".toList then match arguments with
    | [.ptr (some task)] => operations.releaseTask task
    | _ => CProg.undefined
  else CProg.undefined

private def recordLayouts (layout : TaskLayout) : CType → Layout := fun record =>
  if record = type "PrimeEvalStackTask" then taskFields layout
  else if record = type "PrimeEvalStackDriver" then driverFields layout
  else fun _ => none

def profile (operations : TaskOperations) (layout : TaskLayout) : StatementBlock.ObjectBindings.Profile where
  values := calls operations
  locations := fun name => if name = "g_prime_eval_stack_driver".toList then
    some (layout.currentDriver, .pointer) else none
  outsideTypes := fun name => if name = "g_prime_eval_stack_driver".toList then
    some (type "PrimeEvalStackDriver" 1) else none
  outsidePlaces := fun _ => none
  fieldTypes := fieldTypes
  cellExtent := fun record => if record = type "PrimeEvalStackTask" then some layout.taskCells else none
  byteExtent := fun record => if record = type "PrimeEvalStackTask" then some layout.taskBytes else none
  sizeWidth := .bits64
  recordFields := some (recordLayouts layout)

def services (operations : TaskOperations) (layout : TaskLayout) : StatementBlock.ScopedServices Context :=
  StatementBlock.ObjectBindings.services (profile operations layout) operations.region
    (EffectStatements.withObjects (profile operations layout) (effects operations))

private def bindDriver (context : Context) (driver : Option Ptr) : Context :=
  Function.update context "driver".toList
    (some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver))))

private def bindTask (context : Context) (task : Ptr) : Context :=
  Function.update context "task".toList (some (.object (type "PrimeEvalStackTask") task))

private def returned (context : Context) (accepted : Bool) : CProg CVal (Result Context) :=
  pure (.finished (.returned context (some (.bool accepted))))

private def driverRead (layout : TaskLayout) (driver : Option Ptr) (name : String) : CProg CVal CVal :=
  field (driverFields layout) (.ptr driver) name.toList

private def driverPlace (layout : TaskLayout) (driver : Option Ptr) (name : String) : CProg CVal Ptr :=
  fieldAddress (driverFields layout) (.ptr driver) name.toList

private def taskStore (layout : TaskLayout) (task : Ptr) (name : String) (value : CVal) : CProg CVal Unit :=
  CProg.store (task + layout.taskOffset name.toList) value

private def cleanup (operations : TaskOperations) (context : Context) (task : Ptr) :
    CProg CVal (Result Context) := do
  operations.releaseTask task
  returned context false

private def publishUnmanaged (layout : TaskLayout) (context : Context)
    (driver : Option Ptr) (task : Ptr) : CProg CVal (Result Context) := do
  let destination ← driverPlace layout driver "task"
  CProg.copyCells task destination layout.taskCells
  let ready ← driverPlace layout driver "task_ready"
  CProg.store ready (.bool true)
  let generation ← driverPlace layout driver "continuation_generation"
  CProg.incrementU64 generation
  returned context true

/-- The publication specification is independent of the statement interpreter.
It retains a second control read for the enqueue operands, the complete record
snapshot on the unmanaged path, and the sequential generation read/store. -/
def publish (operations : TaskOperations) (layout : TaskLayout) (context : Context)
    (driver : Option Ptr) (task : Ptr) : CProg CVal (Result Context) := do
  let controlValue ← driverRead layout driver "control"
  let managed ← truth controlValue
  if managed then do
    let controlValue ← driverRead layout driver "control"
    let topValue ← driverRead layout driver "top"
    let control ← pointer controlValue
    let top ← pointer topValue
    let accepted ← operations.enqueue control task top
    if !accepted then cleanup operations context task
    else do
      let generation ← driverPlace layout driver "continuation_generation"
      CProg.incrementU64 generation
      returned context true
  else publishUnmanaged layout context driver task

/-- A seed reference is tested at its actual use. Successful capture changes
only its declared flag before publication; refusal retains cleanup and return. -/
def seedAndPublish (operations : TaskOperations) (layout : TaskLayout) (input : TaskInputs)
    (context : Context) (driver : Option Ptr) (task : Ptr) : CProg CVal (Result Context) := do
  let present ← truth (.ptr input.seed_env)
  if present then do
    let accepted ← operations.cloneBindings (task + layout.taskOffset "seed_env".toList) input.seed_env
    if !accepted then cleanup operations context task
    else do
      taskStore layout task "seed_env_initialized" (.bool true)
      publish operations layout context driver task
  else publish operations layout context driver task

private def initializationAfterFuel (operations : TaskOperations) (layout : TaskLayout)
    (input : TaskInputs) (context : Context) (driver : Option Ptr) (task : Ptr) : CProg CVal (Result Context) := do
  taskStore layout task "preserve_bindings" (.bool input.preserve_bindings)
  taskStore layout task "strict_ready_argument" (.i32 input.strict_ready_argument)
  taskStore layout task "target" (.ptr input.target)
  taskStore layout task "evaluator_id" (.u64 input.evaluator_id)
  let captured ← operations.captureDynamic (task + layout.taskOffset "dynamic_env".toList) input.dynamic_env
  if !captured then cleanup operations context task
  else do
    taskStore layout task "dynamic_env_initialized" (.bool true)
    seedAndPublish operations layout input context driver task

private def initializationAfterAuthority (operations : TaskOperations) (layout : TaskLayout)
    (input : TaskInputs) (context : Context) (driver : Option Ptr) (task : Ptr) : CProg CVal (Result Context) := do
  taskStore layout task "space" (.ptr input.s)
  taskStore layout task "arena" (.ptr input.a)
  taskStore layout task "atom" (.ptr input.atom)
  taskStore layout task "etype" (.ptr input.etype)
  taskStore layout task "fuel" (.i32 input.fuel)
  initializationAfterFuel operations layout input context driver task

/-- The initialization tree retains each scalar write, the authoritative
Boolean read from the captured driver and the actual dynamic capture. -/
def initializeTask (operations : TaskOperations) (layout : TaskLayout) (input : TaskInputs)
    (context : Context) (driver : Option Ptr) (task : Ptr) : CProg CVal (Result Context) := do
  operations.zeroTask task (UInt64.ofNat layout.taskBytes)
  taskStore layout task "kind" (.u32 input.kind)
  let pureAuthority ← driverRead layout driver "pure_authority"
  taskStore layout task "pure_authority" pureAuthority
  initializationAfterAuthority operations layout input context driver task

/-- The guard follows the exact left-to-right short circuit. It keeps the
live pointer comparison, readiness load and ownership service; no allocation
or capture is performed before admission. -/
def rejected (operations : TaskOperations) (layout : TaskLayout) (input : TaskInputs)
    (driver : Option Ptr) : CProg CVal Bool := do
  let present ← truth (.ptr driver)
  if !present then pure true else do
    let readiness ← driverRead layout driver "task_ready"
    let ready ← truth readiness
    if ready then pure true else do
      let owned ← operations.targetOwned input.target
      pure (!owned)

/-- The whole independent operation tree snapshots the driver once, retains
region entry/body/exit, and restores both lexical bindings after their actual
returned flows. The region may inspect those flows before restoration. -/
def taskOperations (operations : TaskOperations) (layout : TaskLayout) (input : TaskInputs) :
    CProg CVal (Result Context) := do
  let driver ← CProg.loadPtr layout.currentDriver
  let outer := inputContext input
  let withDriver := bindDriver outer driver
  let result ← do
    let refused ← rejected operations layout input driver
    if refused then returned withDriver false
    else do
      let flow ← operations.region "task".toList layout.taskCells (fun task =>
        initializeTask operations layout input (bindTask withDriver task) driver task)
      pure (StatementBlock.ObjectBindings.restore "task".toList (withDriver "task".toList) flow)
  pure (StatementBlock.ObjectBindings.restore "driver".toList (outer "driver".toList) result)


private def emptyLayout : Layout := fun _ => none

private def read (operations : TaskOperations) (layout : TaskLayout) (context : Context)
    (operand : CExpr) : CProg CVal CVal :=
  (services operations layout).read emptyLayout context operand

private theorem local_read (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (name : Name) (localType : CType) (value : CVal)
    (known : context name = some (.scalar localType (some value))) :
    read operations layout context (.identifier name) = pure value := by
  exact StatementBlock.ObjectBindings.initialized_local_keeps_its_value
    (profile operations layout) emptyLayout context name localType value known


private theorem driver_field_layout (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (driver : Option Ptr)
    (known : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver)))) :
    (StatementBlock.ObjectBindings.objects (profile operations layout) context).fieldLayout
      emptyLayout (.identifier "driver".toList) true = driverFields layout := by
  exact StatementBlock.ObjectBindings.local_pointer_keeps_field_inventory
    (profile operations layout) emptyLayout context (recordLayouts layout)
    "driver".toList "PrimeEvalStackDriver".toList 0 driver (by rfl) known


private theorem task_field_layout (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (task : Ptr)
    (known : context "task".toList = some (.object (type "PrimeEvalStackTask") task)) :
    (StatementBlock.ObjectBindings.objects (profile operations layout) context).fieldLayout
      emptyLayout (.identifier "task".toList) false = taskFields layout := by
  exact StatementBlock.ObjectBindings.local_object_keeps_field_inventory
    (profile operations layout) emptyLayout context (recordLayouts layout)
    "task".toList (type "PrimeEvalStackTask") task (by rfl) known


private theorem driver_field_read (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (driver : Option Ptr) (name : String)
    (known : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver)))) :
    read operations layout context (.field (.identifier "driver".toList) name.toList true) =
      driverRead layout driver name := by
  exact StatementBlock.ObjectBindings.local_pointer_field_keeps_reference_and_inventory
    (profile operations layout) emptyLayout context (recordLayouts layout)
    "driver".toList name.toList "PrimeEvalStackDriver".toList 0 driver (by rfl) known


private theorem task_identifier_place (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (task : Ptr)
    (known : context "task".toList = some (.object (type "PrimeEvalStackTask") task)) :
    StatementBlock.ObjectBindings.place (profile operations layout) emptyLayout context
      (.identifier "task".toList) = pure task := by
  exact StatementBlock.ObjectBindings.local_object_keeps_place
    (profile operations layout) emptyLayout context "task".toList (type "PrimeEvalStackTask") task known


private theorem task_field_place (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (task : Ptr) (name : String) (kind : FieldKind)
    (known : context "task".toList = some (.object (type "PrimeEvalStackTask") task))
    (selected : taskFields layout name.toList = some ⟨layout.taskOffset name.toList, kind⟩) :
    StatementBlock.ObjectBindings.place (profile operations layout) emptyLayout context
      (.field (.identifier "task".toList) name.toList false) =
      pure (task + layout.taskOffset name.toList) := by
  exact StatementBlock.ObjectBindings.local_object_field_keeps_address
    (profile operations layout) emptyLayout context (recordLayouts layout)
    "task".toList name.toList (type "PrimeEvalStackTask") task
    (layout.taskOffset name.toList) kind (by rfl) known selected


private theorem task_field_address (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (task : Ptr) (name : String) (kind : FieldKind)
    (known : context "task".toList = some (.object (type "PrimeEvalStackTask") task))
    (selected : taskFields layout name.toList = some ⟨layout.taskOffset name.toList, kind⟩) :
    read operations layout context
      (.unary .address (.field (.identifier "task".toList) name.toList false)) =
      pure (.ptr (some (task + layout.taskOffset name.toList))) := by
  change (StatementBlock.ObjectBindings.place (profile operations layout) emptyLayout context
    (.field (.identifier "task".toList) name.toList false) >>= fun address =>
      pure (CVal.ptr (some address))) = _
  rw [task_field_place operations layout context task name kind known selected]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]


private theorem driver_field_place (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (driver : Option Ptr) (name : String)
    (known : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver)))) :
    StatementBlock.ObjectBindings.place (profile operations layout) emptyLayout context
      (.field (.identifier "driver".toList) name.toList true) = driverPlace layout driver name := by
  exact StatementBlock.ObjectBindings.local_pointer_field_keeps_address
    (profile operations layout) emptyLayout context (recordLayouts layout)
    "driver".toList name.toList "PrimeEvalStackDriver".toList 0 driver (by rfl) known

private theorem task_field_type (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (task : Ptr) (name : String) (scalarType : CType)
    (known : context "task".toList = some (.object (type "PrimeEvalStackTask") task))
    (selected : fieldTypes (type "PrimeEvalStackTask") name.toList = some scalarType) :
    ScalarBytes.typeOf?
      (StatementBlock.ObjectBindings.types context (profile operations layout).outsideTypes)
      (.field (.identifier "task".toList) name.toList false)
      (profile operations layout).fieldTypes = some scalarType := by
  simp only [ScalarBytes.typeOf?, StatementBlock.ObjectBindings.types, known,
    bind, Option.bind_some, Bool.false_eq_true, if_false]
  exact selected

private theorem task_scalar_assignment (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (task : Ptr) (name : String) (scalarType : CType)
    (known : context "task".toList = some (.object (type "PrimeEvalStackTask") task))
    (typed : fieldTypes (type "PrimeEvalStackTask") name.toList = some scalarType)
    (scalarCell : (profile operations layout).cellExtent scalarType = none)
    (value : CVal) (rhs : CExpr)
    (selected : taskFields layout name.toList =
      some ⟨layout.taskOffset name.toList, valueKind value⟩)
    (actual : read operations layout context rhs = pure value) :
    StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout context
      (.assign (.field (.identifier "task".toList) name.toList false) rhs) =
      (taskStore layout task name value >>= fun _ => pure context) := by
  rw [StatementBlock.ObjectBindings.assignment,
    task_field_type operations layout context task name scalarType known typed]
  simp only [resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, scalarCell]
  change (read operations layout context rhs >>= fun value =>
    StatementBlock.ObjectBindings.writeValue (profile operations layout) emptyLayout context
      (.field (.identifier "task".toList) name.toList false) value) = _
  rw [actual]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rw [StatementBlock.ObjectBindings.scalar_field_write_keeps_place_and_value
    (profile operations layout) emptyLayout context (.identifier "task".toList)
    name.toList false value (layout.taskOffset name.toList)
    (by rw [task_field_layout operations layout context task known]; exact selected)]
  rw [task_field_place operations layout context task name _ known selected]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, taskStore]

private theorem task_size_is_unevaluated (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (task : Ptr)
    (known : context "task".toList = some (.object (type "PrimeEvalStackTask") task)) :
    read operations layout context (.sizeOfExpr (.identifier "task".toList)) =
      pure (.u64 (UInt64.ofNat layout.taskBytes)) := by
  change resolved (StatementBlock.ObjectBindings.size (profile operations layout) context
    (.sizeOfExpr (.identifier "task".toList))) = _
  have inferred : ScalarBytes.typeOf?
      (StatementBlock.ObjectBindings.types context (profile operations layout).outsideTypes)
      (.identifier "task".toList) (profile operations layout).fieldTypes =
      some (type "PrimeEvalStackTask") := by
    simp only [ScalarBytes.typeOf?, StatementBlock.ObjectBindings.types, known]
  simp only [StatementBlock.ObjectBindings.size, inferred, bind, Option.bind_some]
  change resolved (if layout.taskBytes < 2 ^ 64 then
    some (CVal.u64 (UInt64.ofNat layout.taskBytes)) else none) = _
  simp only [layout.taskBytesBound, ↓reduceIte, resolved]

private theorem global_driver_load (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (absent : context "g_prime_eval_stack_driver".toList = none) :
    read operations layout context (.identifier "g_prime_eval_stack_driver".toList) =
      (CProg.loadPtr layout.currentDriver >>= fun driver => pure (.ptr driver)) := by
  simp only [read, services, StatementBlock.ObjectBindings.services,
    StatementBlock.ObjectBindings.read, expressionWithNames.eq_def,
    localOrLocated, StatementBlock.ObjectBindings.values, StatementBlock.ObjectBindings.declared,
    absent, Option.isSome_none, Bool.false_eq_true, if_false]
  change field (fun _ => some ⟨0, .pointer⟩) (.ptr (some layout.currentDriver))
    "g_prime_eval_stack_driver".toList = _
  have zero : layout.currentDriver + 0 = layout.currentDriver := by cases layout.currentDriver; rfl
  simp only [field, pointer, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, zero]

private theorem read_negated (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (operand : CExpr) (program : CProg CVal Bool)
    (actual : read operations layout context operand =
      (program >>= fun value => pure (.bool value))) :
    read operations layout context (.unary .not operand) =
      (program >>= fun value => pure (.bool (!value))) := by
  change (read operations layout context operand >>= fun value =>
    truth value >>= fun selected => pure (CVal.bool (!selected))) = _
  rw [actual]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind, truth]

private theorem read_or (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (left right : CExpr) (program : CProg CVal Bool)
    (actual : read operations layout context left =
      (program >>= fun value => pure (.bool value))) :
    read operations layout context (.binary .or left right) =
      (program >>= fun value => if value then pure (.bool true) else do
        let actual ← read operations layout context right
        let selected ← truth actual
        pure (.bool selected)) := by
  change (read operations layout context left >>= fun value => truth value >>= fun selected =>
    if selected then pure (CVal.bool true) else do
      let second ← read operations layout context right
      let selectedSecond ← truth second
      pure (CVal.bool selectedSecond)) = _
  rw [actual]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind, truth]

private theorem read_pointer_not (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (name : Name) (localType : CType) (value : Option Ptr)
    (known : context name = some (.scalar localType (some (.ptr value)))) :
    read operations layout context (.unary .not (.identifier name)) =
      (truth (.ptr value) >>= fun present => pure (.bool (!present))) := by
  change (read operations layout context (.identifier name) >>= fun value =>
    truth value >>= fun selected => pure (CVal.bool (!selected))) = _
  rw [local_read operations layout context name localType _ known]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

private theorem read_ownership (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (target : Option Ptr)
    (known : context "target".toList =
      some (.scalar (type "OutcomeSet" 1) (some (.ptr target)))) :
    read operations layout context
      (.call "prime_eval_stack_target_is_owned".toList [.identifier "target".toList]) =
      (operations.targetOwned target >>= fun admitted => pure (.bool admitted)) := by
  change expressionWithNames
    (localOrLocated (StatementBlock.ObjectBindings.values context)
      (StatementBlock.ObjectBindings.declared context) (profile operations layout).locations)
    (profile operations layout).values emptyLayout
    (.call "prime_eval_stack_target_is_owned".toList [.identifier "target".toList])
    (StatementBlock.ObjectBindings.objects (profile operations layout) context) = _
  rw [expressionWithNames.eq_def]
  simp only [argumentsWithNames.eq_def]
  have localRead := local_read operations layout context "target".toList _ (.ptr target) known
  change expressionWithNames
    (localOrLocated (StatementBlock.ObjectBindings.values context)
      (StatementBlock.ObjectBindings.declared context) (profile operations layout).locations)
    (profile operations layout).values emptyLayout (.identifier "target".toList)
    (StatementBlock.ObjectBindings.objects (profile operations layout) context) = pure (.ptr target) at localRead
  rw [localRead]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rfl

private def guardExpression : CExpr :=
  .binary .or (.binary .or (.unary .not (.identifier "driver".toList))
    (.field (.identifier "driver".toList) "task_ready".toList true))
    (.unary .not (.call "prime_eval_stack_target_is_owned".toList [.identifier "target".toList]))

private theorem read_guard (operations : TaskOperations) (layout : TaskLayout)
    (input : TaskInputs) (driver : Option Ptr) :
    read operations layout (bindDriver (inputContext input) driver) guardExpression =
      (rejected operations layout input driver >>= fun refused => pure (.bool refused)) := by
  let context := bindDriver (inputContext input) driver
  have knownDriver : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver))) := by
    simp only [context, bindDriver, Function.update_self]
  have knownTarget : context "target".toList =
      some (.scalar (type "OutcomeSet" 1) (some (.ptr input.target))) := by rfl
  have first := read_pointer_not operations layout context "driver".toList _ driver knownDriver
  have owned := read_negated operations layout context
    (.call "prime_eval_stack_target_is_owned".toList [.identifier "target".toList])
    (operations.targetOwned input.target) (read_ownership operations layout context input.target knownTarget)
  have middle := read_or operations layout context
    (.unary .not (.identifier "driver".toList))
    (.field (.identifier "driver".toList) "task_ready".toList true)
    (truth (.ptr driver) >>= fun present => pure (!present)) (by
      rw [first]; simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc])
  change read operations layout context guardExpression = _
  unfold guardExpression
  change (read operations layout context
      (.binary .or (.unary .not (.identifier "driver".toList))
        (.field (.identifier "driver".toList) "task_ready".toList true)) >>=
    fun first => truth first >>= fun selected =>
      if selected then pure (CVal.bool true) else do
        let final ← read operations layout context
          (.unary .not (.call "prime_eval_stack_target_is_owned".toList [.identifier "target".toList]))
        let selectedFinal ← truth final
        pure (CVal.bool selectedFinal)) = _
  rw [middle, owned, driver_field_read operations layout context driver "task_ready" knownDriver]
  unfold rejected
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind,
    BindSchedule.bind_boolean_choice, truth]
  rfl


def interpretedTask (operations : TaskOperations) (layout : TaskLayout) (input : TaskInputs) :
    CProg CVal (Result Context) :=
  StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 64
    (inputContext input) taskSyntax.body

private theorem return_boolean (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (value : Bool) (fuel : Nat) (rest : List CStatement) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 1)
      context (.return (some (.bool value)) :: rest) = returned context value := rfl

private theorem driver_declaration_keeps_snapshot (operations : TaskOperations) (layout : TaskLayout)
    (input : TaskInputs) :
    interpretedTask operations layout input =
      (CProg.loadPtr layout.currentDriver >>= fun driver =>
        StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 63
          (bindDriver (inputContext input) driver) (taskSyntax.body.drop 1) >>= fun result =>
            pure (StatementBlock.ObjectBindings.restore "driver".toList
              ((inputContext input) "driver".toList) result)) := by
  unfold interpretedTask
  change StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 64
    (inputContext input)
    (.declare (type "PrimeEvalStackDriver" 1) "driver".toList
      (ident "g_prime_eval_stack_driver") :: taskSyntax.body.drop 1) = _
  rw [StatementBlock.executeScopedWith.eq_def]
  dsimp only
  change StatementBlock.ObjectBindings.declaration (profile operations layout) operations.region
    emptyLayout (inputContext input) (type "PrimeEvalStackDriver" 1) "driver".toList
    (some (ident "g_prime_eval_stack_driver"))
    (fun updated => StatementBlock.executeScopedWith (services operations layout)
      emptyLayout 0 63 updated (taskSyntax.body.drop 1)) = _
  unfold StatementBlock.ObjectBindings.declaration
  have scalarType : (profile operations layout).cellExtent (type "PrimeEvalStackDriver" 1) = none := rfl
  rw [scalarType]
  dsimp only
  have actual := global_driver_load operations layout (inputContext input) (by rfl)
  change read operations layout (inputContext input) (ident "g_prime_eval_stack_driver") = _ at actual
  change (read operations layout (inputContext input) (ident "g_prime_eval_stack_driver") >>=
    fun actual => StatementBlock.objectInitialValue (type "PrimeEvalStackDriver" 1) actual >>= fun value =>
      StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 63
        (Function.update (inputContext input) "driver".toList (some (.scalar (type "PrimeEvalStackDriver" 1) (some value))))
        (taskSyntax.body.drop 1) >>= fun result =>
          pure (StatementBlock.ObjectBindings.restore "driver".toList ((inputContext input) "driver".toList) result)) = _
  rw [actual]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind,
    StatementBlock.objectInitialValue, type, Nat.zero_lt_succ, ↓reduceIte, pointer, bindDriver]

private theorem guard_preserves_selected_continuation (operations : TaskOperations) (layout : TaskLayout)
    (input : TaskInputs) (driver : Option Ptr) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 63
      (bindDriver (inputContext input) driver) (taskSyntax.body.drop 1) =
      (rejected operations layout input driver >>= fun refused =>
        if refused then returned (bindDriver (inputContext input) driver) false
        else StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 62
          (bindDriver (inputContext input) driver) (taskSyntax.body.drop 2)) := by
  change StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 63
    (bindDriver (inputContext input) driver)
    (.branch guardExpression [.return (some (.bool false))] [] :: taskSyntax.body.drop 2) = _
  rw [StatementBlock.executeScopedWith.eq_def]
  change (read operations layout (bindDriver (inputContext input) driver) guardExpression >>=
    fun actual => truth actual >>= fun selected =>
      StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 62
        (bindDriver (inputContext input) driver) (if selected then [.return (some (.bool false))] else []) >>=
      resume (fun context => StatementBlock.executeScopedWith (services operations layout)
        emptyLayout 0 62 context (taskSyntax.body.drop 2))) = _
  rw [read_guard operations layout input driver]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind, truth]
  congr 1
  funext refused
  cases refused <;> rfl

private theorem driver_field_type (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (driver : Option Ptr) (name : String) (scalarType : CType)
    (known : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (selected : fieldTypes (type "PrimeEvalStackDriver") name.toList = some scalarType) :
    ScalarBytes.typeOf?
      (StatementBlock.ObjectBindings.types context (profile operations layout).outsideTypes)
      (.field (.identifier "driver".toList) name.toList true)
      (profile operations layout).fieldTypes = some scalarType := by
  simp only [ScalarBytes.typeOf?, StatementBlock.ObjectBindings.types, known,
    bind, Option.bind_some, type, ↓reduceIte]
  exact selected

private theorem driver_ready_assignment (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (driver : Option Ptr)
    (known : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver)))) :
    StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout context
      (.assign (driverField "task_ready") (.bool true)) =
      (driverPlace layout driver "task_ready" >>= fun ready =>
        CProg.store ready (.bool true) >>= fun _ => pure context) := by
  have inferred := driver_field_type operations layout context driver "task_ready" (type "bool")
    known (by rfl)
  dsimp only [driverField, ident]
  rw [StatementBlock.ObjectBindings.assignment, inferred]
  have scalarCell : (profile operations layout).cellExtent (type "bool") = none := rfl
  simp only [resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, scalarCell]
  change StatementBlock.ObjectBindings.writeValue (profile operations layout) emptyLayout context
    ((ident "driver").field "task_ready".toList true) (.bool true) = _
  rw [StatementBlock.ObjectBindings.scalar_field_write_keeps_place_and_value
    (profile operations layout) emptyLayout context (ident "driver") "task_ready".toList true
    (.bool true) (layout.driverOffset "task_ready".toList)
    (by change (StatementBlock.ObjectBindings.objects (profile operations layout) context).fieldLayout
          emptyLayout (.identifier "driver".toList) true "task_ready".toList = _
        rw [driver_field_layout operations layout context driver known]; rfl)]
  dsimp only [ident]
  rw [driver_field_place operations layout context driver "task_ready" known]
  simp only [Prog.bind_eq, Prog.pure_eq]

private theorem driver_task_assignment (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (driver : Option Ptr) (task : Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (type "PrimeEvalStackTask") task)) :
    StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout context
      (.assign (driverField "task") (ident "task")) =
      (driverPlace layout driver "task" >>= fun destination =>
        CProg.copyCells task destination layout.taskCells >>= fun _ => pure context) := by
  have inferred := driver_field_type operations layout context driver "task" (type "PrimeEvalStackTask")
    knownDriver (by rfl)
  have sourceType : ScalarBytes.typeOf?
      (StatementBlock.ObjectBindings.types context (profile operations layout).outsideTypes)
      (ident "task") (profile operations layout).fieldTypes = some (type "PrimeEvalStackTask") := by
    simp only [ident, ScalarBytes.typeOf?, StatementBlock.ObjectBindings.types, knownTask]
  rw [StatementBlock.ObjectBindings.record_assignment_retains_snapshot
    (profile operations layout) emptyLayout context (driverField "task") (ident "task")
    (type "PrimeEvalStackTask") layout.taskCells inferred sourceType (by rfl)]
  dsimp only [driverField, ident]
  rw [driver_field_place operations layout context driver "task" knownDriver,
    task_identifier_place operations layout context task knownTask]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

private theorem generation_effect_retains_read_store (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (driver : Option Ptr)
    (known : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver)))) :
    (services operations layout).effect emptyLayout context
      (.postIncrement (driverField "continuation_generation")) =
      (driverPlace layout driver "continuation_generation" >>= CProg.incrementU64) := by
  change EffectStatements.incrementField (profile operations layout) emptyLayout context
    (ident "driver") "continuation_generation".toList true = _
  rw [EffectStatements.discarded_wide_increment_resolves_place_once
    (profile operations layout) emptyLayout context (ident "driver") "continuation_generation".toList
    true (layout.driverOffset "continuation_generation".toList)
    (by change (StatementBlock.ObjectBindings.objects (profile operations layout) context).fieldLayout
          emptyLayout (.identifier "driver".toList) true "continuation_generation".toList = _
        rw [driver_field_layout operations layout context driver known]; rfl)]
  dsimp only [ident]
  rw [driver_field_place operations layout context driver "continuation_generation" known]

private theorem unmanaged_publication_retains_complete_copy (operations : TaskOperations)
    (layout : TaskLayout) (context : Context) (driver : Option Ptr) (task : Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (type "PrimeEvalStackTask") task)) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 45 context
      (taskSyntax.body.drop 19) = publishUnmanaged layout context driver task := by
  change StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 45 context
    [.assign (driverField "task") (ident "task"), .assign (driverField "task_ready") (.bool true),
     .effect (.postIncrement (driverField "continuation_generation")), .return (some (.bool true))] = _
  rw [StatementBlock.executeScopedWith.eq_def]
  change (StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout context
    (.assign (driverField "task") (ident "task")) >>= fun context =>
      StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 44 context
        [.assign (driverField "task_ready") (.bool true),
         .effect (.postIncrement (driverField "continuation_generation")), .return (some (.bool true))]) = _
  rw [driver_task_assignment operations layout context driver task knownDriver knownTask]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  unfold publishUnmanaged
  congr 1
  funext destination
  congr 1
  funext copied
  rw [StatementBlock.executeScopedWith.eq_def]
  change (StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout context
    (.assign (driverField "task_ready") (.bool true)) >>= fun context =>
      StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 43 context
        [.effect (.postIncrement (driverField "continuation_generation")), .return (some (.bool true))]) = _
  rw [driver_ready_assignment operations layout context driver knownDriver]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  congr 1
  funext ready
  congr 1
  funext stored
  rw [StatementBlock.executeScopedWith.eq_def]
  change ((services operations layout).effect emptyLayout context
    (.postIncrement (driverField "continuation_generation")) >>= fun _ =>
      StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 42 context
        [.return (some (.bool true))]) = _
  rw [generation_effect_retains_read_store operations layout context driver knownDriver,
    return_boolean operations layout context true 41 []]
  simp only [Prog.bind_eq, Prog.bind_assoc]


private theorem task_address_is_not_object_value (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (task : Ptr)
    (known : context "task".toList = some (.object (type "PrimeEvalStackTask") task)) :
    read operations layout context (.unary .address (ident "task")) = pure (.ptr (some task)) := by
  change (StatementBlock.ObjectBindings.place (profile operations layout) emptyLayout context
    (.identifier "task".toList) >>= fun address => pure (CVal.ptr (some address))) = _
  rw [task_identifier_place operations layout context task known]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

private theorem task_release_keeps_actual_address (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (task : Ptr)
    (known : context "task".toList = some (.object (type "PrimeEvalStackTask") task)) :
    (services operations layout).effect emptyLayout context
      (.call "prime_eval_stack_task_free".toList [.unary .address (ident "task")]) =
      operations.releaseTask task := by
  change EffectStatements.withObjects (profile operations layout) (effects operations)
    emptyLayout context (.call "prime_eval_stack_task_free".toList
      [.unary .address (ident "task")]) = _
  rw [EffectStatements.object_void_call_keeps_all_actual_arguments]
  simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  change (read operations layout context (.unary .address (ident "task")) >>= fun address =>
    effects operations "prime_eval_stack_task_free".toList [address]) = _
  rw [task_address_is_not_object_value operations layout context task known]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rfl

private theorem refusal_cleanup_retains_effect_and_return (operations : TaskOperations)
    (layout : TaskLayout) (context : Context) (task : Ptr) (fuel : Nat)
    (known : context "task".toList = some (.object (type "PrimeEvalStackTask") task)) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 2)
      context failureBody = cleanup operations context task := by
  unfold failureBody
  rw [StatementBlock.executeScopedWith.eq_def]
  change ((services operations layout).effect emptyLayout context
    (.call "prime_eval_stack_task_free".toList [.unary .address (ident "task")]) >>= fun _ =>
      StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 1)
        context [.return (some (.bool false))]) = _
  rw [task_release_keeps_actual_address operations layout context task known,
    return_boolean operations layout context false fuel []]
  rfl

private theorem enqueue_retains_second_control_and_top_reads (operations : TaskOperations)
    (layout : TaskLayout) (context : Context) (driver : Option Ptr) (task : Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (type "PrimeEvalStackTask") task)) :
    read operations layout context (.call "prime_native_control_enqueue_task".toList
      [driverField "control", .unary .address (ident "task"), driverField "top"]) =
      (driverRead layout driver "control" >>= fun controlValue =>
        driverRead layout driver "top" >>= fun topValue =>
          pointer controlValue >>= fun control => pointer topValue >>= fun top =>
            operations.enqueue control task top >>= fun accepted => pure (.bool accepted)) := by
  change expressionWithNames
    (localOrLocated (StatementBlock.ObjectBindings.values context)
      (StatementBlock.ObjectBindings.declared context) (profile operations layout).locations)
    (profile operations layout).values emptyLayout
    (.call "prime_native_control_enqueue_task".toList
      [driverField "control", .unary .address (ident "task"), driverField "top"])
    (StatementBlock.ObjectBindings.objects (profile operations layout) context) = _
  rw [expressionWithNames.eq_def]
  simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  change (read operations layout context (driverField "control") >>= fun controlValue =>
    read operations layout context (.unary .address (ident "task")) >>= fun taskValue =>
      read operations layout context (driverField "top") >>= fun topValue =>
        calls operations "prime_native_control_enqueue_task".toList [controlValue, taskValue, topValue]) = _
  have controlRead := driver_field_read operations layout context driver "control" knownDriver
  have topRead := driver_field_read operations layout context driver "top" knownDriver
  change read operations layout context (driverField "control") = _ at controlRead
  change read operations layout context (driverField "top") = _ at topRead
  rw [controlRead, topRead, task_address_is_not_object_value operations layout context task knownTask]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext controlValue
  congr 1
  funext topValue
  have notOwned : "prime_native_control_enqueue_task".toList ≠
      "prime_eval_stack_target_is_owned".toList := by decide
  have notCaptured : "prime_native_control_enqueue_task".toList ≠
      "prime_eval_stack_capture_dynamic_env".toList := by decide
  have notCloned : "prime_native_control_enqueue_task".toList ≠ "bindings_clone".toList := by decide
  simp only [calls, notOwned, notCaptured, notCloned, ↓reduceIte]
  cases controlValue <;> cases topValue <;>
    simp only [pointer, boolResult, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  all_goals rw [← Prog.bind_eq, undefined_bind]

private def enqueueOperation (operations : TaskOperations) (layout : TaskLayout)
    (driver : Option Ptr) (task : Ptr) : CProg CVal Bool := do
  let controlValue ← driverRead layout driver "control"
  let topValue ← driverRead layout driver "top"
  let control ← pointer controlValue
  let top ← pointer topValue
  operations.enqueue control task top

private def managedBody : List CStatement :=
  [.branch (.unary .not (.call "prime_native_control_enqueue_task".toList
    [driverField "control", .unary .address (ident "task"), driverField "top"])) failureBody [],
   .effect (.postIncrement (driverField "continuation_generation")),
   .return (some (.bool true))]

private theorem generation_and_return (operations : TaskOperations) (layout : TaskLayout)
    (context : Context) (driver : Option Ptr) (fuel : Nat)
    (known : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver)))) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 2) context
      [.effect (.postIncrement (driverField "continuation_generation")), .return (some (.bool true))] =
      (driverPlace layout driver "continuation_generation" >>= fun generation =>
        CProg.incrementU64 generation >>= fun _ => returned context true) := by
  rw [StatementBlock.executeScopedWith.eq_def]
  change ((services operations layout).effect emptyLayout context
    (.postIncrement (driverField "continuation_generation")) >>= fun _ =>
      StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 1) context
        [.return (some (.bool true))]) = _
  rw [generation_effect_retains_read_store operations layout context driver known,
    return_boolean operations layout context true fuel []]
  simp only [Prog.bind_eq, Prog.bind_assoc]

private theorem managed_publication_retains_refusal (operations : TaskOperations)
    (layout : TaskLayout) (context : Context) (driver : Option Ptr) (task : Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (type "PrimeEvalStackTask") task)) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 45 context managedBody =
      (enqueueOperation operations layout driver task >>= fun accepted =>
        if !accepted then cleanup operations context task else
          driverPlace layout driver "continuation_generation" >>= fun generation =>
            CProg.incrementU64 generation >>= fun _ => returned context true) := by
  have actual : read operations layout context (.call "prime_native_control_enqueue_task".toList
      [driverField "control", .unary .address (ident "task"), driverField "top"]) =
      (enqueueOperation operations layout driver task >>= fun accepted => pure (.bool accepted)) := by
    simpa only [enqueueOperation, Prog.bind_eq, Prog.bind_assoc] using
      enqueue_retains_second_control_and_top_reads operations layout context driver task knownDriver knownTask
  unfold managedBody
  rw [StatementBlock.executeScopedWith.eq_def]
  change (read operations layout context
    (.unary .not (.call "prime_native_control_enqueue_task".toList
      [driverField "control", .unary .address (ident "task"), driverField "top"])) >>= fun value =>
      truth value >>= fun refused =>
        StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 44 context
          (if refused then failureBody else []) >>=
        resume (fun updated => StatementBlock.executeScopedWith (services operations layout)
          emptyLayout 0 44 updated
          [.effect (.postIncrement (driverField "continuation_generation")), .return (some (.bool true))])) = _
  rw [read_negated operations layout context _ _ actual]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind, truth]
  congr 1
  funext accepted
  cases accepted with
  | false =>
      change (StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 44 context
        failureBody >>= resume (fun updated => StatementBlock.executeScopedWith (services operations layout)
          emptyLayout 0 44 updated
          [.effect (.postIncrement (driverField "continuation_generation")), .return (some (.bool true))])) =
        cleanup operations context task
      rw [refusal_cleanup_retains_effect_and_return operations layout context task 42 knownTask]
      simp only [cleanup, returned, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind, resume]
  | true =>
      change StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 44 context
        [.effect (.postIncrement (driverField "continuation_generation")), .return (some (.bool true))] = _
      exact generation_and_return operations layout context driver 42 knownDriver

private theorem managed_return_prevents_unmanaged_fallthrough (operations : TaskOperations)
    (layout : TaskLayout) (context : Context) (driver : Option Ptr) (task : Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (type "PrimeEvalStackTask") task))
    (continuation : Context → CProg CVal (Result Context)) :
    (StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 45 context managedBody
      >>= resume continuation) =
      (enqueueOperation operations layout driver task >>= fun accepted =>
        if !accepted then cleanup operations context task else
          driverPlace layout driver "continuation_generation" >>= fun generation =>
            CProg.incrementU64 generation >>= fun _ => returned context true) := by
  rw [managed_publication_retains_refusal operations layout context driver task knownDriver knownTask]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext accepted
  cases accepted with
  | false =>
      change (cleanup operations context task >>= resume continuation) = cleanup operations context task
      simp only [cleanup, returned, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind, resume]
  | true =>
      change ((driverPlace layout driver "continuation_generation" >>= fun generation =>
        CProg.incrementU64 generation >>= fun _ => returned context true) >>= resume continuation) =
          (driverPlace layout driver "continuation_generation" >>= fun generation =>
            CProg.incrementU64 generation >>= fun _ => returned context true)
      simp only [returned, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind, resume]

private theorem publication_retains_source_paths (operations : TaskOperations)
    (layout : TaskLayout) (context : Context) (driver : Option Ptr) (task : Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (type "PrimeEvalStackTask") task)) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 46 context
      (taskSyntax.body.drop 18) = publish operations layout context driver task := by
  change StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 46 context
    (.branch (driverField "control") managedBody [] :: taskSyntax.body.drop 19) = _
  rw [StatementBlock.executeScopedWith.eq_def]
  change (read operations layout context (driverField "control") >>= fun controlValue =>
    truth controlValue >>= fun managed =>
      StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 45 context
        (if managed then managedBody else []) >>=
      resume (fun updated => StatementBlock.executeScopedWith (services operations layout)
        emptyLayout 0 45 updated (taskSyntax.body.drop 19))) = _
  have actual := driver_field_read operations layout context driver "control" knownDriver
  change read operations layout context (driverField "control") = _ at actual
  rw [actual]
  unfold publish
  simp only [Prog.bind_eq]
  congr 1
  funext controlValue
  congr 1
  funext managed
  cases managed with
  | false =>
      change StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 45 context
        (taskSyntax.body.drop 19) = publishUnmanaged layout context driver task
      exact unmanaged_publication_retains_complete_copy operations layout context driver task knownDriver knownTask
  | true =>
      change (StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 45 context
        managedBody >>= resume (fun updated => StatementBlock.executeScopedWith (services operations layout)
          emptyLayout 0 45 updated (taskSyntax.body.drop 19))) = _
      rw [managed_return_prevents_unmanaged_fallthrough operations layout context driver task
        knownDriver knownTask]
      simp only [enqueueOperation, Prog.bind_eq, Prog.bind_assoc]
      rfl

private theorem embedded_capture_keeps_place_and_source (operations : TaskOperations)
    (layout : TaskLayout) (context : Context) (task : Ptr) (fieldName sourceName callee : String)
    (source : Option Ptr)
    (knownTask : context "task".toList = some (.object (type "PrimeEvalStackTask") task))
    (knownSource : context sourceName.toList =
      some (.scalar (type "Bindings" 1) (some (.ptr source))))
    (selected : taskFields layout fieldName.toList =
      some ⟨layout.taskOffset fieldName.toList, .embedded⟩) :
    read operations layout context (.call callee.toList
      [.unary .address (taskField fieldName), ident sourceName]) =
      calls operations callee.toList [.ptr (some (task + layout.taskOffset fieldName.toList)), .ptr source] := by
  change expressionWithNames
    (localOrLocated (StatementBlock.ObjectBindings.values context)
      (StatementBlock.ObjectBindings.declared context) (profile operations layout).locations)
    (profile operations layout).values emptyLayout
    (.call callee.toList [.unary .address (taskField fieldName), ident sourceName])
    (StatementBlock.ObjectBindings.objects (profile operations layout) context) = _
  rw [expressionWithNames.eq_def]
  simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  change (read operations layout context (.unary .address (taskField fieldName)) >>= fun destination =>
    read operations layout context (ident sourceName) >>= fun sourceValue =>
      calls operations callee.toList [destination, sourceValue]) = _
  have address := task_field_address operations layout context task fieldName .embedded knownTask selected
  change read operations layout context (.unary .address (taskField fieldName)) = _ at address
  have inputRead := local_read operations layout context sourceName.toList _ (.ptr source) knownSource
  change read operations layout context (ident sourceName) = _ at inputRead
  rw [address, inputRead]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

private theorem clone_read_keeps_embedded_destination (operations : TaskOperations)
    (layout : TaskLayout) (context : Context) (task : Ptr) (source : Option Ptr)
    (knownTask : context "task".toList = some (.object (type "PrimeEvalStackTask") task))
    (knownSource : context "seed_env".toList =
      some (.scalar (type "Bindings" 1) (some (.ptr source)))) :
    read operations layout context (.call "bindings_clone".toList
      [.unary .address (taskField "seed_env"), ident "seed_env"]) =
      (operations.cloneBindings (task + layout.taskOffset "seed_env".toList) source >>=
        fun accepted => pure (.bool accepted)) := by
  rw [embedded_capture_keeps_place_and_source operations layout context task "seed_env" "seed_env"
    "bindings_clone" source knownTask knownSource (by rfl)]
  rfl

private theorem dynamic_read_keeps_embedded_destination (operations : TaskOperations)
    (layout : TaskLayout) (context : Context) (task : Ptr) (source : Option Ptr)
    (knownTask : context "task".toList = some (.object (type "PrimeEvalStackTask") task))
    (knownSource : context "dynamic_env".toList =
      some (.scalar (type "Bindings" 1) (some (.ptr source)))) :
    read operations layout context (.call "prime_eval_stack_capture_dynamic_env".toList
      [.unary .address (taskField "dynamic_env"), ident "dynamic_env"]) =
      (operations.captureDynamic (task + layout.taskOffset "dynamic_env".toList) source >>=
        fun accepted => pure (.bool accepted)) := by
  rw [embedded_capture_keeps_place_and_source operations layout context task "dynamic_env" "dynamic_env"
    "prime_eval_stack_capture_dynamic_env" source knownTask knownSource (by rfl)]
  rfl

private theorem flag_assignment_keeps_store (operations : TaskOperations)
    (layout : TaskLayout) (context : Context) (task : Ptr) (name : String)
    (knownTask : context "task".toList = some (.object (type "PrimeEvalStackTask") task))
    (typed : fieldTypes (type "PrimeEvalStackTask") name.toList = some (type "bool"))
    (selected : taskFields layout name.toList = some ⟨layout.taskOffset name.toList, .boolean⟩) :
    StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout context
      (.assign (taskField name) (.bool true)) =
      (taskStore layout task name (.bool true) >>= fun _ => pure context) := by
  exact task_scalar_assignment operations layout context task name (type "bool")
    knownTask typed (by rfl) (.bool true) (.bool true) selected (by rfl)

private def seedBody : List CStatement :=
  [.branch (.unary .not (.call "bindings_clone".toList
    [.unary .address (taskField "seed_env"), ident "seed_env"])) failureBody [],
   .assign (taskField "seed_env_initialized") (.bool true)]

private theorem seed_body_resumes_publication (operations : TaskOperations)
    (layout : TaskLayout) (context : Context) (driver : Option Ptr) (task : Ptr) (source : Option Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (type "PrimeEvalStackTask") task))
    (knownSource : context "seed_env".toList =
      some (.scalar (type "Bindings" 1) (some (.ptr source)))) :
    (StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 46 context seedBody >>=
      resume (fun updated => StatementBlock.executeScopedWith (services operations layout)
        emptyLayout 0 46 updated (taskSyntax.body.drop 18))) =
      (operations.cloneBindings (task + layout.taskOffset "seed_env".toList) source >>= fun accepted =>
        if !accepted then cleanup operations context task else
          taskStore layout task "seed_env_initialized" (.bool true) >>= fun _ =>
            publish operations layout context driver task) := by
  have actual := clone_read_keeps_embedded_destination operations layout context task source knownTask knownSource
  unfold seedBody
  rw [StatementBlock.executeScopedWith.eq_def]
  change ((read operations layout context
    (.unary .not (.call "bindings_clone".toList
      [.unary .address (taskField "seed_env"), ident "seed_env"])) >>= fun value =>
      truth value >>= fun refused =>
        StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 45 context
          (if refused then failureBody else []) >>=
        resume (fun updated => StatementBlock.executeScopedWith (services operations layout)
          emptyLayout 0 45 updated [.assign (taskField "seed_env_initialized") (.bool true)])) >>=
      resume (fun updated => StatementBlock.executeScopedWith (services operations layout)
        emptyLayout 0 46 updated (taskSyntax.body.drop 18))) = _
  rw [read_negated operations layout context _ _ actual]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind, truth]
  congr 1
  funext accepted
  cases accepted with
  | false =>
      change (StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 45 context
        failureBody >>= fun result =>
          resume (fun updated => StatementBlock.executeScopedWith (services operations layout)
            emptyLayout 0 45 updated [.assign (taskField "seed_env_initialized") (.bool true)]) result >>=
          resume (fun updated => StatementBlock.executeScopedWith (services operations layout)
            emptyLayout 0 46 updated (taskSyntax.body.drop 18))) = cleanup operations context task
      rw [refusal_cleanup_retains_effect_and_return operations layout context task 43 knownTask]
      simp only [cleanup, returned, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind, resume]
  | true =>
      change (StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 45 context
        [.assign (taskField "seed_env_initialized") (.bool true)] >>=
        resume (fun updated => StatementBlock.executeScopedWith (services operations layout)
          emptyLayout 0 46 updated (taskSyntax.body.drop 18))) =
        (taskStore layout task "seed_env_initialized" (.bool true) >>= fun _ =>
          publish operations layout context driver task)
      rw [StatementBlock.executeScopedWith.eq_def]
      change ((StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout context
        (.assign (taskField "seed_env_initialized") (.bool true)) >>= fun updated =>
          StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 44 updated []) >>=
        resume (fun updated => StatementBlock.executeScopedWith (services operations layout)
          emptyLayout 0 46 updated (taskSyntax.body.drop 18))) = _
      rw [flag_assignment_keeps_store operations layout context task "seed_env_initialized" knownTask
        (by rfl) (by rfl)]
      simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
      change (taskStore layout task "seed_env_initialized" (.bool true) >>= fun _ =>
        StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 46 context
          (taskSyntax.body.drop 18)) = _
      rw [publication_retains_source_paths operations layout context driver task knownDriver knownTask]
      simp only [Prog.bind_eq]

private theorem seed_choice_retains_reference (operations : TaskOperations)
    (layout : TaskLayout) (input : TaskInputs) (context : Context) (driver : Option Ptr) (task : Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (type "PrimeEvalStackTask") task))
    (knownSource : context "seed_env".toList =
      some (.scalar (type "Bindings" 1) (some (.ptr input.seed_env)))) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 47 context
      (taskSyntax.body.drop 17) = seedAndPublish operations layout input context driver task := by
  change StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 47 context
    (.branch (ident "seed_env") seedBody [] :: taskSyntax.body.drop 18) = _
  rw [StatementBlock.executeScopedWith.eq_def]
  change (read operations layout context (ident "seed_env") >>= fun source => truth source >>= fun present =>
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 46 context
      (if present then seedBody else []) >>=
    resume (fun updated => StatementBlock.executeScopedWith (services operations layout)
      emptyLayout 0 46 updated (taskSyntax.body.drop 18))) = _
  have actual := local_read operations layout context "seed_env".toList _ (.ptr input.seed_env) knownSource
  change read operations layout context (ident "seed_env") = _ at actual
  rw [actual]
  unfold seedAndPublish
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext present
  cases present with
  | false =>
      change StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 46 context
        (taskSyntax.body.drop 18) = publish operations layout context driver task
      exact publication_retains_source_paths operations layout context driver task knownDriver knownTask
  | true =>
      change (StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 46 context seedBody >>=
        resume (fun updated => StatementBlock.executeScopedWith (services operations layout)
          emptyLayout 0 46 updated (taskSyntax.body.drop 18))) = _
      rw [seed_body_resumes_publication operations layout context driver task input.seed_env
        knownDriver knownTask knownSource]
      rfl

private theorem dynamic_choice_keeps_refusal_and_seed (operations : TaskOperations)
    (layout : TaskLayout) (input : TaskInputs) (context : Context) (driver : Option Ptr) (task : Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (type "PrimeEvalStackTask") task))
    (knownDynamic : context "dynamic_env".toList =
      some (.scalar (type "Bindings" 1) (some (.ptr input.dynamic_env))))
    (knownSeed : context "seed_env".toList =
      some (.scalar (type "Bindings" 1) (some (.ptr input.seed_env)))) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 49 context
      (taskSyntax.body.drop 15) =
      (operations.captureDynamic (task + layout.taskOffset "dynamic_env".toList) input.dynamic_env >>=
        fun accepted => if !accepted then cleanup operations context task else
          taskStore layout task "dynamic_env_initialized" (.bool true) >>= fun _ =>
            seedAndPublish operations layout input context driver task) := by
  have actual := dynamic_read_keeps_embedded_destination operations layout context task input.dynamic_env
    knownTask knownDynamic
  change StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 49 context
    (.branch (.unary .not (.call "prime_eval_stack_capture_dynamic_env".toList
      [.unary .address (taskField "dynamic_env"), ident "dynamic_env"])) failureBody [] ::
      taskSyntax.body.drop 16) = _
  rw [StatementBlock.executeScopedWith.eq_def]
  change (read operations layout context
    (.unary .not (.call "prime_eval_stack_capture_dynamic_env".toList
      [.unary .address (taskField "dynamic_env"), ident "dynamic_env"])) >>= fun value =>
      truth value >>= fun refused =>
        StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 48 context
          (if refused then failureBody else []) >>=
        resume (fun updated => StatementBlock.executeScopedWith (services operations layout)
          emptyLayout 0 48 updated (taskSyntax.body.drop 16))) = _
  rw [read_negated operations layout context _ _ actual]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc, truth]
  congr 1
  funext accepted
  cases accepted with
  | false =>
      change (StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 48 context
        failureBody >>= resume (fun updated => StatementBlock.executeScopedWith (services operations layout)
          emptyLayout 0 48 updated (taskSyntax.body.drop 16))) = cleanup operations context task
      rw [refusal_cleanup_retains_effect_and_return operations layout context task 46 knownTask]
      simp only [cleanup, returned, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc, resume]
  | true =>
      change StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 48 context
        (taskSyntax.body.drop 16) =
        (taskStore layout task "dynamic_env_initialized" (.bool true) >>= fun _ =>
          seedAndPublish operations layout input context driver task)
      change StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 48 context
        (.assign (taskField "dynamic_env_initialized") (.bool true) :: taskSyntax.body.drop 17) = _
      rw [StatementBlock.executeScopedWith.eq_def]
      change (StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout context
        (.assign (taskField "dynamic_env_initialized") (.bool true)) >>= fun updated =>
          StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 47 updated
            (taskSyntax.body.drop 17)) = _
      rw [flag_assignment_keeps_store operations layout context task "dynamic_env_initialized"
        knownTask (by rfl) (by rfl)]
      simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
      rw [seed_choice_retains_reference operations layout input context driver task knownDriver knownTask knownSeed]

private theorem memset_keeps_signed_zero_address_and_extent (operations : TaskOperations)
    (layout : TaskLayout) (context : Context) (task : Ptr)
    (knownTask : context "task".toList = some (.object (type "PrimeEvalStackTask") task)) :
    (services operations layout).effect emptyLayout context (.call "memset".toList
      [.unary .address (ident "task"), .decimal 0, .sizeOfExpr (ident "task")]) =
      operations.zeroTask task (UInt64.ofNat layout.taskBytes) := by
  change EffectStatements.withObjects (profile operations layout) (effects operations) emptyLayout context
    (.call "memset".toList [.unary .address (ident "task"), .decimal 0, .sizeOfExpr (ident "task")]) = _
  rw [EffectStatements.object_void_call_keeps_all_actual_arguments]
  simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  change (read operations layout context (.unary .address (ident "task")) >>= fun address =>
    read operations layout context (.decimal 0) >>= fun zero =>
      read operations layout context (.sizeOfExpr (ident "task")) >>= fun extent =>
        effects operations "memset".toList [address, zero, extent]) = _
  have decimal : read operations layout context (.decimal 0) = pure (.i32 0) := rfl
  have size := task_size_is_unevaluated operations layout context task knownTask
  change read operations layout context (.sizeOfExpr (ident "task")) = _ at size
  rw [task_address_is_not_object_value operations layout context task knownTask, decimal, size]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rfl

private def bodyContext (input : TaskInputs) (driver : Option Ptr) (task : Ptr) : Context :=
  bindTask (bindDriver (inputContext input) driver) task

private theorem task_authority_assignment_keeps_typed_load (operations : TaskOperations)
    (layout : TaskLayout) (context : Context) (driver : Option Ptr) (task : Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (type "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (type "PrimeEvalStackTask") task)) :
    StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout context
      (.assign (taskField "pure_authority") (driverField "pure_authority")) =
      (driverRead layout driver "pure_authority" >>= fun value =>
        taskStore layout task "pure_authority" value >>= fun _ => pure context) := by
  have inferred := task_field_type operations layout context task "pure_authority" (type "bool")
    knownTask (by rfl)
  dsimp only [taskField, ident]
  rw [StatementBlock.ObjectBindings.assignment, inferred]
  have scalarCell : (profile operations layout).cellExtent (type "bool") = none := rfl
  simp only [resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, scalarCell]
  change (read operations layout context (driverField "pure_authority") >>= fun value =>
    StatementBlock.ObjectBindings.writeValue (profile operations layout) emptyLayout context
      (.field (.identifier "task".toList) "pure_authority".toList false) value) = _
  have actual := driver_field_read operations layout context driver "pure_authority" knownDriver
  change read operations layout context (driverField "pure_authority") = _ at actual
  rw [actual]
  unfold driverRead
  cases driver with
  | none =>
      rw [null_owner_field_is_undefined]
      rw [← Prog.bind_eq, undefined_bind]
      rw [undefined_bind]
  | some owner =>
      rw [boolean_field_uses_actual_offset (driverFields layout) owner "pure_authority".toList
        (layout.driverOffset "pure_authority".toList) (by rfl)]
      simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
      congr 1
      funext authority
      rw [StatementBlock.ObjectBindings.scalar_field_write_keeps_place_and_value
        (profile operations layout) emptyLayout context (.identifier "task".toList)
        "pure_authority".toList false (.bool authority) (layout.taskOffset "pure_authority".toList)
        (by rw [task_field_layout operations layout context task knownTask]; rfl)]
      rw [task_field_place operations layout context task "pure_authority" .boolean knownTask (by rfl)]
      simp only [taskStore, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

private theorem initialize_kind_keeps_input (operations : TaskOperations) (layout : TaskLayout)
    (input : TaskInputs) (driver : Option Ptr) (task : Ptr) :
    StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout
      (bodyContext input driver task) (.assign (taskField "kind") (ident "kind")) =
      (taskStore layout task "kind" (.u32 input.kind) >>= fun _ =>
        pure (bodyContext input driver task)) := by
  exact task_scalar_assignment operations layout (bodyContext input driver task) task "kind"
    (type "PrimeEvalStackTaskKind" 0) (by rfl) (by rfl) (by rfl) (.u32 input.kind) (ident "kind")
    (by rfl) (local_read operations layout (bodyContext input driver task) "kind".toList
      (type "PrimeEvalStackTaskKind" 0) (.u32 input.kind) (by rfl))

private theorem initialize_space_keeps_input (operations : TaskOperations) (layout : TaskLayout)
    (input : TaskInputs) (driver : Option Ptr) (task : Ptr) :
    StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout
      (bodyContext input driver task) (.assign (taskField "space") (ident "s")) =
      (taskStore layout task "space" (.ptr input.s) >>= fun _ =>
        pure (bodyContext input driver task)) := by
  exact task_scalar_assignment operations layout (bodyContext input driver task) task "space"
    (type "Space" 1) (by rfl) (by rfl) (by rfl) (.ptr input.s) (ident "s")
    (by rfl) (local_read operations layout (bodyContext input driver task) "s".toList
      (type "Space" 1) (.ptr input.s) (by rfl))

private theorem initialize_arena_keeps_input (operations : TaskOperations) (layout : TaskLayout)
    (input : TaskInputs) (driver : Option Ptr) (task : Ptr) :
    StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout
      (bodyContext input driver task) (.assign (taskField "arena") (ident "a")) =
      (taskStore layout task "arena" (.ptr input.a) >>= fun _ =>
        pure (bodyContext input driver task)) := by
  exact task_scalar_assignment operations layout (bodyContext input driver task) task "arena"
    (type "Arena" 1) (by rfl) (by rfl) (by rfl) (.ptr input.a) (ident "a")
    (by rfl) (local_read operations layout (bodyContext input driver task) "a".toList
      (type "Arena" 1) (.ptr input.a) (by rfl))

private theorem initialize_atom_keeps_input (operations : TaskOperations) (layout : TaskLayout)
    (input : TaskInputs) (driver : Option Ptr) (task : Ptr) :
    StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout
      (bodyContext input driver task) (.assign (taskField "atom") (ident "atom")) =
      (taskStore layout task "atom" (.ptr input.atom) >>= fun _ =>
        pure (bodyContext input driver task)) := by
  exact task_scalar_assignment operations layout (bodyContext input driver task) task "atom"
    (type "Atom" 1) (by rfl) (by rfl) (by rfl) (.ptr input.atom) (ident "atom")
    (by rfl) (local_read operations layout (bodyContext input driver task) "atom".toList
      (type "Atom" 1) (.ptr input.atom) (by rfl))

private theorem initialize_etype_keeps_input (operations : TaskOperations) (layout : TaskLayout)
    (input : TaskInputs) (driver : Option Ptr) (task : Ptr) :
    StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout
      (bodyContext input driver task) (.assign (taskField "etype") (ident "etype")) =
      (taskStore layout task "etype" (.ptr input.etype) >>= fun _ =>
        pure (bodyContext input driver task)) := by
  exact task_scalar_assignment operations layout (bodyContext input driver task) task "etype"
    (type "Atom" 1) (by rfl) (by rfl) (by rfl) (.ptr input.etype) (ident "etype")
    (by rfl) (local_read operations layout (bodyContext input driver task) "etype".toList
      (type "Atom" 1) (.ptr input.etype) (by rfl))

private theorem initialize_fuel_keeps_input (operations : TaskOperations) (layout : TaskLayout)
    (input : TaskInputs) (driver : Option Ptr) (task : Ptr) :
    StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout
      (bodyContext input driver task) (.assign (taskField "fuel") (ident "fuel")) =
      (taskStore layout task "fuel" (.i32 input.fuel) >>= fun _ =>
        pure (bodyContext input driver task)) := by
  exact task_scalar_assignment operations layout (bodyContext input driver task) task "fuel"
    (type "int" 0) (by rfl) (by rfl) (by rfl) (.i32 input.fuel) (ident "fuel")
    (by rfl) (local_read operations layout (bodyContext input driver task) "fuel".toList
      (type "int" 0) (.i32 input.fuel) (by rfl))

private theorem initialize_preserve_bindings_keeps_input (operations : TaskOperations) (layout : TaskLayout)
    (input : TaskInputs) (driver : Option Ptr) (task : Ptr) :
    StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout
      (bodyContext input driver task) (.assign (taskField "preserve_bindings") (ident "preserve_bindings")) =
      (taskStore layout task "preserve_bindings" (.bool input.preserve_bindings) >>= fun _ =>
        pure (bodyContext input driver task)) := by
  exact task_scalar_assignment operations layout (bodyContext input driver task) task "preserve_bindings"
    (type "bool" 0) (by rfl) (by rfl) (by rfl) (.bool input.preserve_bindings) (ident "preserve_bindings")
    (by rfl) (local_read operations layout (bodyContext input driver task) "preserve_bindings".toList
      (type "bool" 0) (.bool input.preserve_bindings) (by rfl))

private theorem initialize_strict_ready_argument_keeps_input (operations : TaskOperations) (layout : TaskLayout)
    (input : TaskInputs) (driver : Option Ptr) (task : Ptr) :
    StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout
      (bodyContext input driver task) (.assign (taskField "strict_ready_argument") (ident "strict_ready_argument")) =
      (taskStore layout task "strict_ready_argument" (.i32 input.strict_ready_argument) >>= fun _ =>
        pure (bodyContext input driver task)) := by
  exact task_scalar_assignment operations layout (bodyContext input driver task) task "strict_ready_argument"
    (type "int" 0) (by rfl) (by rfl) (by rfl) (.i32 input.strict_ready_argument) (ident "strict_ready_argument")
    (by rfl) (local_read operations layout (bodyContext input driver task) "strict_ready_argument".toList
      (type "int" 0) (.i32 input.strict_ready_argument) (by rfl))

private theorem initialize_target_keeps_input (operations : TaskOperations) (layout : TaskLayout)
    (input : TaskInputs) (driver : Option Ptr) (task : Ptr) :
    StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout
      (bodyContext input driver task) (.assign (taskField "target") (ident "target")) =
      (taskStore layout task "target" (.ptr input.target) >>= fun _ =>
        pure (bodyContext input driver task)) := by
  exact task_scalar_assignment operations layout (bodyContext input driver task) task "target"
    (type "OutcomeSet" 1) (by rfl) (by rfl) (by rfl) (.ptr input.target) (ident "target")
    (by rfl) (local_read operations layout (bodyContext input driver task) "target".toList
      (type "OutcomeSet" 1) (.ptr input.target) (by rfl))

private theorem initialize_evaluator_id_keeps_input (operations : TaskOperations) (layout : TaskLayout)
    (input : TaskInputs) (driver : Option Ptr) (task : Ptr) :
    StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout
      (bodyContext input driver task) (.assign (taskField "evaluator_id") (ident "evaluator_id")) =
      (taskStore layout task "evaluator_id" (.u64 input.evaluator_id) >>= fun _ =>
        pure (bodyContext input driver task)) := by
  exact task_scalar_assignment operations layout (bodyContext input driver task) task "evaluator_id"
    (type "uint64_t" 0) (by rfl) (by rfl) (by rfl) (.u64 input.evaluator_id) (ident "evaluator_id")
    (by rfl) (local_read operations layout (bodyContext input driver task) "evaluator_id".toList
      (type "uint64_t" 0) (.u64 input.evaluator_id) (by rfl))

private theorem initialization_after_fuel (operations : TaskOperations)
    (layout : TaskLayout) (input : TaskInputs) (driver : Option Ptr) (task : Ptr) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 53
      (bodyContext input driver task) (taskSyntax.body.drop 11) =
      initializationAfterFuel operations layout input (bodyContext input driver task) driver task := by
  let entries : List ((CExpr × CExpr) × CProg CVal Unit) :=
    [((taskField "preserve_bindings", ident "preserve_bindings"), taskStore layout task "preserve_bindings" (.bool input.preserve_bindings)),
     ((taskField "strict_ready_argument", ident "strict_ready_argument"), taskStore layout task "strict_ready_argument" (.i32 input.strict_ready_argument)),
     ((taskField "target", ident "target"), taskStore layout task "target" (.ptr input.target)),
     ((taskField "evaluator_id", ident "evaluator_id"), taskStore layout task "evaluator_id" (.u64 input.evaluator_id))]
  have actual := StatementBlock.scoped_assignment_prefix_keeps_operations
    (services operations layout) emptyLayout 0 49 (bodyContext input driver task) entries
    (taskSyntax.body.drop 15) (by
      intro entry member
      simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact initialize_preserve_bindings_keeps_input operations layout input driver task
      · exact initialize_strict_ready_argument_keeps_input operations layout input driver task
      · exact initialize_target_keeps_input operations layout input driver task
      · exact initialize_evaluator_id_keeps_input operations layout input driver task)
  change StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 53
    (bodyContext input driver task) (taskSyntax.body.drop 11) = _ at actual
  rw [actual]
  rw [dynamic_choice_keeps_refusal_and_seed operations layout input (bodyContext input driver task)
    driver task (by rfl) (by rfl) (by rfl) (by rfl)]
  simp only [entries, List.foldr_cons, List.foldr_nil, initializationAfterFuel, Prog.bind_eq]

private theorem initialization_after_authority (operations : TaskOperations)
    (layout : TaskLayout) (input : TaskInputs) (driver : Option Ptr) (task : Ptr) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 58
      (bodyContext input driver task) (taskSyntax.body.drop 6) =
      initializationAfterAuthority operations layout input (bodyContext input driver task) driver task := by
  let entries : List ((CExpr × CExpr) × CProg CVal Unit) :=
    [((taskField "space", ident "s"), taskStore layout task "space" (.ptr input.s)),
     ((taskField "arena", ident "a"), taskStore layout task "arena" (.ptr input.a)),
     ((taskField "atom", ident "atom"), taskStore layout task "atom" (.ptr input.atom)),
     ((taskField "etype", ident "etype"), taskStore layout task "etype" (.ptr input.etype)),
     ((taskField "fuel", ident "fuel"), taskStore layout task "fuel" (.i32 input.fuel))]
  have actual := StatementBlock.scoped_assignment_prefix_keeps_operations
    (services operations layout) emptyLayout 0 53 (bodyContext input driver task) entries
    (taskSyntax.body.drop 11) (by
      intro entry member
      simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · exact initialize_space_keeps_input operations layout input driver task
      · exact initialize_arena_keeps_input operations layout input driver task
      · exact initialize_atom_keeps_input operations layout input driver task
      · exact initialize_etype_keeps_input operations layout input driver task
      · exact initialize_fuel_keeps_input operations layout input driver task)
  change StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 58
    (bodyContext input driver task) (taskSyntax.body.drop 6) = _ at actual
  rw [actual]
  rw [initialization_after_fuel]
  simp only [entries, List.foldr_cons, List.foldr_nil, initializationAfterAuthority, Prog.bind_eq]

private theorem initialization_retains_complete_sequence (operations : TaskOperations)
    (layout : TaskLayout) (input : TaskInputs) (driver : Option Ptr) (task : Ptr) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 61
      (bodyContext input driver task) (taskSyntax.body.drop 3) =
      initializeTask operations layout input (bodyContext input driver task) driver task := by
  let authority : CProg CVal Unit := do
    let value ← driverRead layout driver "pure_authority"
    taskStore layout task "pure_authority" value
  have authorityRealized : (services operations layout).assignment emptyLayout
      (bodyContext input driver task) (.assign (taskField "pure_authority") (driverField "pure_authority")) =
      (authority >>= fun _ => pure (bodyContext input driver task)) := by
    change StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout
      (bodyContext input driver task) (.assign (taskField "pure_authority") (driverField "pure_authority")) = _
    rw [task_authority_assignment_keeps_typed_load operations layout (bodyContext input driver task)
      driver task (by rfl) (by rfl)]
    simp only [authority, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc]
  let entries : List ((CExpr × CExpr) × CProg CVal Unit) :=
    [((taskField "kind", ident "kind"), taskStore layout task "kind" (.u32 input.kind)),
     ((taskField "pure_authority", driverField "pure_authority"), authority)]
  have actual := StatementBlock.scoped_assignment_prefix_keeps_operations
    (services operations layout) emptyLayout 0 58 (bodyContext input driver task) entries
    (taskSyntax.body.drop 6) (by
      intro entry member
      simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact initialize_kind_keeps_input operations layout input driver task
      · exact authorityRealized)
  change StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 60
    (bodyContext input driver task) (taskSyntax.body.drop 4) = _ at actual
  change StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 61
    (bodyContext input driver task)
    (.effect (.call "memset".toList
      [.unary .address (ident "task"), .decimal 0, .sizeOfExpr (ident "task")]) ::
      taskSyntax.body.drop 4) = _
  rw [StatementBlock.scoped_effect_keeps_continuation]
  change ((services operations layout).effect emptyLayout (bodyContext input driver task)
    (.call "memset".toList [.unary .address (ident "task"), .decimal 0, .sizeOfExpr (ident "task")]) >>=
      fun _ => StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 60
        (bodyContext input driver task) (taskSyntax.body.drop 4)) = _
  rw [memset_keeps_signed_zero_address_and_extent operations layout (bodyContext input driver task) task (by rfl),
    actual, initialization_after_authority]
  simp only [entries, authority, List.foldr_cons, List.foldr_nil, initializeTask,
    Prog.bind_eq, Prog.bind_assoc]

private theorem automatic_task_keeps_region_and_restoration (operations : TaskOperations)
    (layout : TaskLayout) (input : TaskInputs) (driver : Option Ptr) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 62
      (bindDriver (inputContext input) driver) (taskSyntax.body.drop 2) =
      (operations.region "task".toList layout.taskCells (fun task =>
        initializeTask operations layout input (bodyContext input driver task) driver task) >>= fun result =>
          pure (StatementBlock.ObjectBindings.restore "task".toList
            ((bindDriver (inputContext input) driver) "task".toList) result)) := by
  change StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 62
    (bindDriver (inputContext input) driver)
    (.declareUninitialized (type "PrimeEvalStackTask") "task".toList :: taskSyntax.body.drop 3) = _
  rw [StatementBlock.executeScopedWith.eq_def]
  dsimp only
  change StatementBlock.ObjectBindings.declaration (profile operations layout) operations.region emptyLayout
    (bindDriver (inputContext input) driver) (type "PrimeEvalStackTask") "task".toList none
    (fun updated => StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 61 updated
      (taskSyntax.body.drop 3)) = _
  rw [StatementBlock.ObjectBindings.declared_record_keeps_entry_and_continuation
    (profile operations layout) operations.region emptyLayout (bindDriver (inputContext input) driver)
    (type "PrimeEvalStackTask") "task".toList layout.taskCells (by rfl)]
  have bodies : (fun task => StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 61
      (Function.update (bindDriver (inputContext input) driver) "task".toList
        (some (.object (type "PrimeEvalStackTask") task))) (taskSyntax.body.drop 3)) =
      (fun task => initializeTask operations layout input (bodyContext input driver task) driver task) := by
    funext task
    exact initialization_retains_complete_sequence operations layout input driver task
  rw [bodies]

/-- Every statement in the admitted constructor has an independent operation
meaning. The theorem retains allocation scope, complete copying, all provider
refusals, and the lexical driver snapshot without moving effects. Physical
provider realization and native record encoding are separate obligations. -/
theorem interpreted_task_is_complete_operation_tree (operations : TaskOperations)
    (layout : TaskLayout) (input : TaskInputs) :
    interpretedTask operations layout input = taskOperations operations layout input := by
  rw [driver_declaration_keeps_snapshot]
  unfold taskOperations
  simp only [Prog.bind_eq]
  congr 1
  funext driver
  rw [guard_preserves_selected_continuation]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext refused
  cases refused with
  | true => rfl
  | false =>
      change (StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 62
        (bindDriver (inputContext input) driver) (taskSyntax.body.drop 2) >>= fun result =>
          pure (StatementBlock.ObjectBindings.restore "driver".toList
            ((inputContext input) "driver".toList) result)) = _
      rw [automatic_task_keeps_region_and_restoration]
      simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc, bodyContext]
      rfl

/-- The actual source text parses to the independent syntax and executes
its complete scoped operation tree under the declared providers. This is a
source interpretation theorem; physical layout, encoding, lifetime, argument
order and the compiled implementation require separate comparisons. -/
theorem original_task_executes_complete_operation_tree (operations : TaskOperations)
    (layout : TaskLayout) (input : TaskInputs) :
    (declaratorFunctionText? names source.toList).map
      (fun function => StatementBlock.executeScopedWith (services operations layout)
        emptyLayout 0 64 (inputContext input) function.body) =
      some (taskOperations operations layout input) := by
  rw [original_source_recognized, Option.map_some]
  exact congrArg some (interpreted_task_is_complete_operation_tree operations layout input)

namespace Controls

theorem missing_capture_destination_is_not_invented (operations : TaskOperations)
    (source : Option Ptr) :
    calls operations "prime_eval_stack_capture_dynamic_env".toList [.ptr none, .ptr source] =
      CProg.undefined := by
  simp only [calls, ↓reduceIte, ite_self]

theorem clone_arity_is_checked (operations : TaskOperations) :
    calls operations "bindings_clone".toList [] = CProg.undefined := by
  simp only [calls, ↓reduceIte, ite_self]

theorem unsigned_zero_is_not_the_memset_int_argument (operations : TaskOperations)
    (task : Ptr) (extent : UInt64) :
    effects operations "memset".toList [.ptr (some task), .u32 0, .u64 extent] =
      CProg.undefined := by
  simp only [effects, ↓reduceIte]

theorem signed_zero_retains_memset_address_and_extent (operations : TaskOperations)
    (task : Ptr) (extent : UInt64) :
    effects operations "memset".toList [.ptr (some task), .i32 0, .u64 extent] =
      operations.zeroTask task extent := by
  simp only [effects, ↓reduceIte]

end Controls

/-- Conversion for the declared unsigned-compatible 32-bit enum profile.
Signed native enum constants retain their bits; this does not assert a
platform-independent ABI or introduce general mixed-width conversions. -/
def kindWord? : CVal → Option UInt32
  | .i32 value => some value.toUInt32
  | .u32 value => some value
  | _ => none

/-- The exact twelve-argument boundary retains nullable references, signed
indices and the complete evaluator word. Unknown tags or arity are outside
this source interpretation; they do not manufacture a task request. -/
def TaskInputs.ofArguments? : List CVal → Option TaskInputs
  | [kind, .ptr space, .ptr arena, .ptr atom, .ptr expectedType,
      .i32 fuel, .bool preserve, .i32 strictIndex, .ptr target,
      .ptr dynamic, .ptr seed, .u64 evaluator] =>
      (kindWord? kind).map fun actualKind =>
        { kind := actualKind, s := space, a := arena, atom := atom,
          etype := expectedType, fuel := fuel, preserve_bindings := preserve,
          strict_ready_argument := strictIndex, target := target,
          dynamic_env := dynamic, seed_env := seed, evaluator_id := evaluator }
  | _ => none

/-- The caller observes only an explicit returned Boolean. A suspended,
falling-through or wrongly typed result is not a refused or accepted task. -/
def booleanReply (result : Result Context) : CProg CVal Bool :=
  match result.returnedValue? with
  | some (.bool accepted) => pure accepted
  | _ => CProg.undefined

theorem boolean_reply_context_transport (map : Context → Context)
    (result : Result Context) :
    booleanReply (result.mapContext map) = booleanReply result := by
  unfold booleanReply
  rw [ReadBlock.returned_value_context_map]

/-- The callable source realization elaborates its parameters and executes
the common scoped block interpreter, before performing the declared reply
readout. The inner physical providers remain explicit. -/
def setTask (operations : TaskOperations) (layout : TaskLayout) : Scheduling.SetTask :=
  fun arguments => match TaskInputs.ofArguments? arguments with
  | none => CProg.undefined
  | some input =>
      interpretedTask operations layout input >>= booleanReply

/-- Independent callee meaning at the same typed argument boundary. Every
heap operation and provider call in taskOperations precedes its reply readout. -/
def requestOperations (operations : TaskOperations) (layout : TaskLayout) : Scheduling.SetTask :=
  fun arguments => match TaskInputs.ofArguments? arguments with
  | none => CProg.undefined
  | some input => taskOperations operations layout input >>= booleanReply

theorem set_task_keeps_complete_operation_tree (operations : TaskOperations)
    (layout : TaskLayout) (arguments : List CVal) :
    setTask operations layout arguments = requestOperations operations layout arguments := by
  unfold setTask requestOperations
  cases TaskInputs.ofArguments? arguments with
  | none => rfl
  | some input =>
      change (interpretedTask operations layout input >>= booleanReply) = _
      rw [interpreted_task_is_complete_operation_tree operations layout input]

def TaskInputs.fromCall (input : Scheduling.CallInputs) : TaskInputs :=
  { kind := 1, s := input.space, a := input.arena, atom := input.atom,
    etype := input.expectedType, fuel := input.fuel,
    preserve_bindings := input.preserve, strict_ready_argument := input.strictIndex,
    target := input.target, dynamic_env := input.environment,
    seed_env := input.seed, evaluator_id := input.evaluator }

def TaskInputs.fromNormalize (input : Scheduling.NormalizeInputs) : TaskInputs :=
  { kind := 2, s := input.space, a := input.arena, atom := input.atom,
    etype := none, fuel := input.fuel, preserve_bindings := true,
    strict_ready_argument := -1, target := input.target,
    dynamic_env := input.environment, seed_env := none, evaluator_id := input.evaluator }

def TaskInputs.fromBind (input : NormalizeAtomConstructor.ConstructorInputs)
    (layout : BindSchedule.BindLayout) (finish : Ptr) : TaskInputs :=
  { kind := 0, s := input.space, a := input.arena, atom := input.atom,
    etype := none, fuel := input.fuel, preserve_bindings := true,
    strict_ready_argument := -1, target := some (finish + layout.frame.child),
    dynamic_env := some (finish + layout.frame.environment),
    seed_env := none, evaluator_id := input.evaluator }

theorem call_parameters_keep_actual_arguments (input : Scheduling.CallInputs) :
    TaskInputs.ofArguments? input.arguments = some (TaskInputs.fromCall input) := rfl

theorem normalize_parameters_keep_actual_arguments (input : Scheduling.NormalizeInputs) :
    TaskInputs.ofArguments? (Scheduling.normalizeArguments input) =
      some (TaskInputs.fromNormalize input) := rfl

theorem bind_parameters_keep_embedded_references
    (input : NormalizeAtomConstructor.ConstructorInputs)
    (layout : BindSchedule.BindLayout) (finish : Ptr) :
    TaskInputs.ofArguments? (BindSchedule.taskArguments input layout finish) =
      some (TaskInputs.fromBind input layout finish) := rfl

theorem call_request_is_complete_task (operations : TaskOperations) (layout : TaskLayout)
    (input : Scheduling.CallInputs) :
    setTask operations layout input.arguments =
      (taskOperations operations layout (TaskInputs.fromCall input) >>= booleanReply) := by
  rw [set_task_keeps_complete_operation_tree]
  simp only [requestOperations, call_parameters_keep_actual_arguments]

theorem normalize_request_is_complete_task (operations : TaskOperations) (layout : TaskLayout)
    (input : Scheduling.NormalizeInputs) :
    setTask operations layout (Scheduling.normalizeArguments input) =
      (taskOperations operations layout (TaskInputs.fromNormalize input) >>= booleanReply) := by
  rw [set_task_keeps_complete_operation_tree]
  simp only [requestOperations, normalize_parameters_keep_actual_arguments]

theorem bind_request_is_complete_task (operations : TaskOperations) (taskLayout : TaskLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs)
    (bindLayout : BindSchedule.BindLayout) (finish : Ptr) :
    setTask operations taskLayout (BindSchedule.taskArguments input bindLayout finish) =
      (taskOperations operations taskLayout (TaskInputs.fromBind input bindLayout finish) >>= booleanReply) := by
  rw [set_task_keeps_complete_operation_tree]
  simp only [requestOperations, bind_parameters_keep_embedded_references]

/-- The original CALL wrapper and interpreted callee compose through their
typed boundary. The equality retains the whole operation tree before its
Boolean reply; inner-provider and physical-ABI realization are separate. -/
theorem original_call_composes_complete_task (operations : TaskOperations) (layout : TaskLayout)
    (input : Scheduling.CallInputs) :
    (declaratorFunctionText? Scheduling.names Scheduling.callSource.toList).map
      (fun function => StatementBlock.executeWith
        (Scheduling.taskServices (setTask operations layout))
        (fun _ _ _ => CProg.undefined) emptyLayout 0 1 input.locals function.body) =
      some ((taskOperations operations layout (TaskInputs.fromCall input) >>= booleanReply) >>= fun accepted =>
        pure (.finished (.returned input.locals (some (.bool accepted))))) := by
  trans some (setTask operations layout input.arguments >>= fun accepted =>
    pure (.finished (.returned input.locals (some (.bool accepted)))))
  · exact Scheduling.original_call_executes_complete_arguments (setTask operations layout) input
  · rw [call_request_is_complete_task]

theorem original_normalize_composes_complete_task (operations : TaskOperations) (layout : TaskLayout)
    (input : Scheduling.NormalizeInputs) :
    (declaratorFunctionText? Scheduling.names Scheduling.normalizeSource.toList).map
      (fun function => StatementBlock.executeWith
        (Scheduling.taskServices (setTask operations layout))
        (fun _ _ _ => CProg.undefined) emptyLayout 0 1 (Scheduling.normalizeLocals input) function.body) =
      some ((taskOperations operations layout (TaskInputs.fromNormalize input) >>= booleanReply) >>= fun accepted =>
        pure (.finished (.returned (Scheduling.normalizeLocals input) (some (.bool accepted))))) := by
  trans some (setTask operations layout (Scheduling.normalizeArguments input) >>= fun accepted =>
    pure (.finished (.returned (Scheduling.normalizeLocals input) (some (.bool accepted)))))
  · exact Scheduling.original_normalize_executes_complete_arguments (setTask operations layout) input
  · rw [normalize_request_is_complete_task]

/-- The checked BIND wrapper embeds the interpreted Task callee. The
shared parsed-body entry point retains source admission and the complete
frame operation tree, including its refusal assertion and pop. -/
theorem original_bind_composes_complete_task (operations : TaskOperations) (taskLayout : TaskLayout)
    (frames : BindSchedule.BindOperations) (bindLayout : BindSchedule.BindLayout)
    (input : NormalizeAtomConstructor.ConstructorInputs) :
    StatementBlock.executeParsedBody
      (fun body => StatementBlock.executeWith
        ({ frames with setTask := setTask operations taskLayout }.profile bindLayout)
        (StatementBlock.fieldAssignment
          ({ frames with setTask := setTask operations taskLayout }.reader bindLayout))
        bindLayout.fields 0 17 (BindSchedule.inputs input) body)
      (declaratorFunctionText? BindSchedule.names BindSchedule.source.toList) =
      BindSchedule.bindOperations
        { frames with setTask := requestOperations operations taskLayout } bindLayout input := by
  trans BindSchedule.bindOperations
    { frames with setTask := setTask operations taskLayout } bindLayout input
  · exact BindSchedule.original_body_executes_complete_bind
      { frames with setTask := setTask operations taskLayout } bindLayout input
  · apply congrArg (fun callee =>
      BindSchedule.bindOperations { frames with setTask := callee } bindLayout input)
    funext arguments
    exact set_task_keeps_complete_operation_tree operations taskLayout arguments

namespace Controls

theorem wrong_kind_tag_is_rejected : kindWord? (.bool true) = none := rfl

theorem wrong_request_arity_is_rejected : TaskInputs.ofArguments? [] = none := rfl

theorem exhaustion_is_not_a_boolean_reply : booleanReply .exhausted = CProg.undefined := rfl

theorem fallthrough_is_not_a_boolean_reply (context : Context) :
    booleanReply (.finished (.next context)) = CProg.undefined := rfl

theorem returned_refusal_remains_refusal (context : Context) :
    booleanReply (.finished (.returned context (some (.bool false)))) = pure false := rfl

theorem wide_integer_return_is_not_a_boolean_reply (context : Context) :
    booleanReply (.finished (.returned context (some (.u64 1)))) = CProg.undefined := rfl

theorem null_and_wide_call_parameters_are_retained :
    (TaskInputs.fromCall Scheduling.Controls.input).seed_env = some ⟨6, 0⟩ ∧
    (TaskInputs.fromCall Scheduling.Controls.input).evaluator_id = 4294967303 ∧
    (TaskInputs.fromCall Scheduling.Controls.input).strict_ready_argument = -7 := by
  exact ⟨rfl, rfl, rfl⟩

end Controls

end Mettapedia.Languages.MeTTa.CeTTaNativeCost.TaskAdmission

namespace Mettapedia.Languages.MeTTa.CeTTaNativeCost.RunTaskSource

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ReadExpressions
open StatementBlock.ObjectBindings (Context)
open TaskAdmission (ident taskField driverField)

def names : TypeNames := TaskAdmission.names ++ ["void".toList,
  "PrimeEvalAuthorityGuard".toList, "PrimeNeedActiveGuard".toList,
  "PrimeEvalStackFrame".toList, "CettaCount".toList]

/-- These independent arms retain the real effect order, the CALL seed
conditional, and the NORMALIZE block's own declaration and refusal. -/
def bindArm : List CStatement :=
  [.effect (.call "cetta_runtime_stats_inc".toList
      [ident "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND"]),
   .assign (driverField "running_bind_task") (.bool true),
   .effect (.call "metta_eval_bind".toList
     [taskField "space", taskField "arena", taskField "atom",
      taskField "fuel", taskField "target"]),
   .assign (driverField "running_bind_task") (.bool false), .break]

def callArm : List CStatement :=
  [.effect (.call "cetta_runtime_stats_inc".toList
      [ident "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL"]),
   .effect (.call "metta_call_impl".toList
     [taskField "space", taskField "arena", taskField "atom", taskField "etype",
      taskField "fuel", taskField "preserve_bindings",
      .conditional (taskField "seed_env_initialized")
        (.unary .address (taskField "seed_env")) .null,
      taskField "strict_ready_argument", taskField "target"]), .break]

def normalizeArm : List CStatement :=
  [.effect (.call "cetta_runtime_stats_inc".toList
      [ident "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE"]),
   .block [.declare ⟨"PrimeEvalStackFrame".toList, 1⟩ "frame".toList
       (.call "prime_eval_stack_normalize_atom_frame_new".toList
         [taskField "space", taskField "arena", taskField "atom", taskField "fuel",
          .unary .address (taskField "dynamic_env"), taskField "evaluator_id",
          taskField "target"]),
     .branch (ident "frame")
       [.effect (.call "prime_eval_stack_push".toList [ident "frame"])]
       [.effect (.call "eval_mark_incomplete".toList
         [ident "CETTA_EVAL_INCOMPLETE_CAPACITY"])]], .break]

/-- The complete expected source syntax is independent of the reader result.
Both cleanup callbacks remain declarations. No attribute is stripped and no
unbraced arm is rewritten into new source text. -/
def runSyntax : CDeclaratorFunction :=
  ⟨⟨"void".toList, 0⟩, "prime_eval_stack_run_task".toList, [],
   [.declare ⟨"PrimeEvalStackDriver".toList, 1⟩ "driver".toList
      (ident "g_prime_eval_stack_driver"),
    .effect (.call "assert".toList [.binary .ne (ident "driver") .null]),
    .effect (.call "assert".toList [driverField "task_ready"]),
    .effect (.call "assert".toList [.unary .not (driverField "running_task")]),
    .declare ⟨"PrimeEvalStackTask".toList, 0⟩ "task".toList (driverField "task"),
    .declareCleanup ⟨"PrimeEvalAuthorityGuard".toList, 0⟩ "authority".toList
      (some (.call "prime_eval_authority_enter".toList [taskField "pure_authority"]))
      "prime_eval_authority_leave".toList,
    .effect (.call "memset".toList [.unary .address (driverField "task"),
      .decimal 0, .sizeOfExpr (driverField "task")]),
    .assign (driverField "task_ready") (.bool false),
    .assign (driverField "active_task") (.unary .address (ident "task")),
    .assign (driverField "running_task") (.bool true),
    .declare ⟨"CettaCount".toList, 0⟩ "published_before".toList
      (.conditional (taskField "target")
        (.field (taskField "target") "len".toList true) (.unsignedInteger 0)),
    .declareCleanup ⟨"PrimeNeedActiveGuard".toList, 0⟩ "need_guard".toList
      (some (.call "prime_need_active_enter".toList [.unary .address (taskField "dynamic_env")]))
      "prime_need_active_leave".toList,
    .declare ⟨"uint64_t".toList, 0⟩ "previous_evaluator_id".toList
      (ident "g_prime_need_evaluator_id"),
    .assign (ident "g_prime_need_evaluator_id") (taskField "evaluator_id"),
    .switch (taskField "kind")
      [(ident "PRIME_EVAL_STACK_TASK_BIND", bindArm),
       (ident "PRIME_EVAL_STACK_TASK_CALL", callArm),
       (ident "PRIME_EVAL_STACK_TASK_NORMALIZE", normalizeArm)] [],
    .assign (ident "g_prime_need_evaluator_id") (ident "previous_evaluator_id"),
    .assign (driverField "active_task") .null,
    .branch (.binary .and (taskField "target")
      (.binary .gt (.field (taskField "target") "len".toList true) (ident "published_before")))
      [.effect (.call "prime_eval_stack_stream_note".toList [taskField "target"])] [],
    .effect (.call "prime_eval_stack_task_free".toList [.unary .address (ident "task")]),
    .assign (driverField "running_task") (.bool false)]⟩

def source : String := "static void prime_eval_stack_run_task(void) {\n    PrimeEvalStackDriver *driver = g_prime_eval_stack_driver;\n    assert(driver != NULL);\n    assert(driver->task_ready);\n    assert(!driver->running_task);\n    PrimeEvalStackTask task = driver->task;\n    __attribute__((cleanup(prime_eval_authority_leave)))\n    PrimeEvalAuthorityGuard authority = prime_eval_authority_enter(task.pure_authority);\n    memset(&driver->task, 0, sizeof(driver->task));\n    driver->task_ready = false;\n    driver->active_task = &task;\n    driver->running_task = true;\n    CettaCount published_before = task.target ? task.target->len : 0u;\n\n    __attribute__((cleanup(prime_need_active_leave)))\n    PrimeNeedActiveGuard need_guard =\n        prime_need_active_enter(&task.dynamic_env);\n    uint64_t previous_evaluator_id = g_prime_need_evaluator_id;\n    g_prime_need_evaluator_id = task.evaluator_id;\n    switch (task.kind) {\n    case PRIME_EVAL_STACK_TASK_BIND:\n        cetta_runtime_stats_inc(\n            CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND);\n        driver->running_bind_task = true;\n        metta_eval_bind(\n            task.space, task.arena, task.atom,\n            task.fuel, task.target);\n        driver->running_bind_task = false;\n        break;\n    case PRIME_EVAL_STACK_TASK_CALL:\n        cetta_runtime_stats_inc(\n            CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL);\n        metta_call_impl(\n            task.space, task.arena, task.atom, task.etype,\n            task.fuel, task.preserve_bindings,\n            task.seed_env_initialized ? &task.seed_env : NULL,\n            task.strict_ready_argument, task.target);\n        break;\n    case PRIME_EVAL_STACK_TASK_NORMALIZE:\n        cetta_runtime_stats_inc(\n            CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE);\n        {\n            PrimeEvalStackFrame *frame =\n                prime_eval_stack_normalize_atom_frame_new(\n                    task.space, task.arena, task.atom, task.fuel,\n                    &task.dynamic_env, task.evaluator_id,\n                    task.target);\n            if (frame)\n                prime_eval_stack_push(frame);\n            else\n                eval_mark_incomplete(\n                    CETTA_EVAL_INCOMPLETE_CAPACITY);\n        }\n        break;\n    }\n    g_prime_need_evaluator_id = previous_evaluator_id;\n    driver->active_task = NULL;\n    if (task.target && task.target->len > published_before)\n        prime_eval_stack_stream_note(task.target);\n    prime_eval_stack_task_free(&task);\n    driver->running_task = false;\n}"
def characters : List Char := native_c_characters% "static void prime_eval_stack_run_task(void) {\n    PrimeEvalStackDriver *driver = g_prime_eval_stack_driver;\n    assert(driver != NULL);\n    assert(driver->task_ready);\n    assert(!driver->running_task);\n    PrimeEvalStackTask task = driver->task;\n    __attribute__((cleanup(prime_eval_authority_leave)))\n    PrimeEvalAuthorityGuard authority = prime_eval_authority_enter(task.pure_authority);\n    memset(&driver->task, 0, sizeof(driver->task));\n    driver->task_ready = false;\n    driver->active_task = &task;\n    driver->running_task = true;\n    CettaCount published_before = task.target ? task.target->len : 0u;\n\n    __attribute__((cleanup(prime_need_active_leave)))\n    PrimeNeedActiveGuard need_guard =\n        prime_need_active_enter(&task.dynamic_env);\n    uint64_t previous_evaluator_id = g_prime_need_evaluator_id;\n    g_prime_need_evaluator_id = task.evaluator_id;\n    switch (task.kind) {\n    case PRIME_EVAL_STACK_TASK_BIND:\n        cetta_runtime_stats_inc(\n            CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND);\n        driver->running_bind_task = true;\n        metta_eval_bind(\n            task.space, task.arena, task.atom,\n            task.fuel, task.target);\n        driver->running_bind_task = false;\n        break;\n    case PRIME_EVAL_STACK_TASK_CALL:\n        cetta_runtime_stats_inc(\n            CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL);\n        metta_call_impl(\n            task.space, task.arena, task.atom, task.etype,\n            task.fuel, task.preserve_bindings,\n            task.seed_env_initialized ? &task.seed_env : NULL,\n            task.strict_ready_argument, task.target);\n        break;\n    case PRIME_EVAL_STACK_TASK_NORMALIZE:\n        cetta_runtime_stats_inc(\n            CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE);\n        {\n            PrimeEvalStackFrame *frame =\n                prime_eval_stack_normalize_atom_frame_new(\n                    task.space, task.arena, task.atom, task.fuel,\n                    &task.dynamic_env, task.evaluator_id,\n                    task.target);\n            if (frame)\n                prime_eval_stack_push(frame);\n            else\n                eval_mark_incomplete(\n                    CETTA_EVAL_INCOMPLETE_CAPACITY);\n        }\n        break;\n    }\n    g_prime_need_evaluator_id = previous_evaluator_id;\n    driver->active_task = NULL;\n    if (task.target && task.target->len > published_before)\n        prime_eval_stack_stream_note(task.target);\n    prime_eval_stack_task_free(&task);\n    driver->running_task = false;\n}"

theorem characters_are_actual_source : source.toList = characters := by
  native_c_character_reflexivity

private def lexCharacters0 : List Char := native_c_characters% "static void prime_eval_stack_run_task(void) {\n"
private def lexTokens0 : List Token := [.identifier (native_c_characters% "static"), .identifier (native_c_characters% "void"), .identifier (native_c_characters% "prime_eval_stack_run_task"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "void"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% "{")]
private theorem lexPiece0 : lexCharacters0.foldl step initial = completed lexTokens0 := by
  native_c_parser_reflexivity

private def lexCharacters1 : List Char := native_c_characters% "    PrimeEvalStackDriver *driver = g_prime_eval_stack_driver;\n"
private def lexTokens1 : List Token := [.identifier (native_c_characters% "PrimeEvalStackDriver"), .punctuation (native_c_characters% "*"), .identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "g_prime_eval_stack_driver"), .punctuation (native_c_characters% ";")]
private theorem lexPiece1 : lexCharacters1.foldl step initial = completed lexTokens1 := by
  native_c_parser_reflexivity

private def lexCharacters2 : List Char := native_c_characters% "    assert(driver != NULL);\n"
private def lexTokens2 : List Token := [.identifier (native_c_characters% "assert"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "!="), .identifier (native_c_characters% "NULL"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece2 : lexCharacters2.foldl step initial = completed lexTokens2 := by
  native_c_parser_reflexivity

private def lexCharacters3 : List Char := native_c_characters% "    assert(driver->task_ready);\n"
private def lexTokens3 : List Token := [.identifier (native_c_characters% "assert"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "task_ready"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece3 : lexCharacters3.foldl step initial = completed lexTokens3 := by
  native_c_parser_reflexivity

private def lexCharacters4 : List Char := native_c_characters% "    assert(!driver->running_task);\n"
private def lexTokens4 : List Token := [.identifier (native_c_characters% "assert"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "!"), .identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "running_task"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece4 : lexCharacters4.foldl step initial = completed lexTokens4 := by
  native_c_parser_reflexivity

private def lexCharacters5 : List Char := native_c_characters% "    PrimeEvalStackTask task = driver->task;\n"
private def lexTokens5 : List Token := [.identifier (native_c_characters% "PrimeEvalStackTask"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% ";")]
private theorem lexPiece5 : lexCharacters5.foldl step initial = completed lexTokens5 := by
  native_c_parser_reflexivity

private def lexCharacters6 : List Char := native_c_characters% "    __attribute__((cleanup(prime_eval_authority_leave)))\n"
private def lexTokens6 : List Token := [.identifier (native_c_characters% "__attribute__"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "cleanup"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "prime_eval_authority_leave"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ")")]
private theorem lexPiece6 : lexCharacters6.foldl step initial = completed lexTokens6 := by
  native_c_parser_reflexivity

private def lexCharacters7 : List Char := native_c_characters% "    PrimeEvalAuthorityGuard authority = prime_eval_authority_enter(task.pure_authority);\n"
private def lexTokens7 : List Token := [.identifier (native_c_characters% "PrimeEvalAuthorityGuard"), .identifier (native_c_characters% "authority"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "prime_eval_authority_enter"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "pure_authority"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece7 : lexCharacters7.foldl step initial = completed lexTokens7 := by
  native_c_parser_reflexivity

private def lexCharacters8 : List Char := native_c_characters% "    memset(&driver->task, 0, sizeof(driver->task));\n"
private def lexTokens8 : List Token := [.identifier (native_c_characters% "memset"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "&"), .identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% ","), .number (native_c_characters% "0"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "sizeof"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece8 : lexCharacters8.foldl step initial = completed lexTokens8 := by
  native_c_parser_reflexivity

private def lexCharacters9 : List Char := native_c_characters% "    driver->task_ready = false;\n"
private def lexTokens9 : List Token := [.identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "task_ready"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "false"), .punctuation (native_c_characters% ";")]
private theorem lexPiece9 : lexCharacters9.foldl step initial = completed lexTokens9 := by
  native_c_parser_reflexivity

private def lexCharacters10 : List Char := native_c_characters% "    driver->active_task = &task;\n"
private def lexTokens10 : List Token := [.identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "active_task"), .punctuation (native_c_characters% "="), .punctuation (native_c_characters% "&"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% ";")]
private theorem lexPiece10 : lexCharacters10.foldl step initial = completed lexTokens10 := by
  native_c_parser_reflexivity

private def lexCharacters11 : List Char := native_c_characters% "    driver->running_task = true;\n"
private def lexTokens11 : List Token := [.identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "running_task"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "true"), .punctuation (native_c_characters% ";")]
private theorem lexPiece11 : lexCharacters11.foldl step initial = completed lexTokens11 := by
  native_c_parser_reflexivity

private def lexCharacters12 : List Char := native_c_characters% "    CettaCount published_before = task.target ? task.target->len : 0u;\n"
private def lexTokens12 : List Token := [.identifier (native_c_characters% "CettaCount"), .identifier (native_c_characters% "published_before"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "target"), .punctuation (native_c_characters% "?"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "target"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "len"), .punctuation (native_c_characters% ":"), .number (native_c_characters% "0u"), .punctuation (native_c_characters% ";")]
private theorem lexPiece12 : lexCharacters12.foldl step initial = completed lexTokens12 := by
  native_c_parser_reflexivity

private def lexCharacters13 : List Char := native_c_characters% "\n"
private def lexTokens13 : List Token := []
private theorem lexPiece13 : lexCharacters13.foldl step initial = completed lexTokens13 := by
  native_c_parser_reflexivity

private def lexCharacters14 : List Char := native_c_characters% "    __attribute__((cleanup(prime_need_active_leave)))\n"
private def lexTokens14 : List Token := [.identifier (native_c_characters% "__attribute__"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "cleanup"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "prime_need_active_leave"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ")")]
private theorem lexPiece14 : lexCharacters14.foldl step initial = completed lexTokens14 := by
  native_c_parser_reflexivity

private def lexCharacters15 : List Char := native_c_characters% "    PrimeNeedActiveGuard need_guard =\n"
private def lexTokens15 : List Token := [.identifier (native_c_characters% "PrimeNeedActiveGuard"), .identifier (native_c_characters% "need_guard"), .punctuation (native_c_characters% "=")]
private theorem lexPiece15 : lexCharacters15.foldl step initial = completed lexTokens15 := by
  native_c_parser_reflexivity

private def lexCharacters16 : List Char := native_c_characters% "        prime_need_active_enter(&task.dynamic_env);\n"
private def lexTokens16 : List Token := [.identifier (native_c_characters% "prime_need_active_enter"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "&"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "dynamic_env"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece16 : lexCharacters16.foldl step initial = completed lexTokens16 := by
  native_c_parser_reflexivity

private def lexCharacters17 : List Char := native_c_characters% "    uint64_t previous_evaluator_id = g_prime_need_evaluator_id;\n"
private def lexTokens17 : List Token := [.identifier (native_c_characters% "uint64_t"), .identifier (native_c_characters% "previous_evaluator_id"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "g_prime_need_evaluator_id"), .punctuation (native_c_characters% ";")]
private theorem lexPiece17 : lexCharacters17.foldl step initial = completed lexTokens17 := by
  native_c_parser_reflexivity

private def lexCharacters18 : List Char := native_c_characters% "    g_prime_need_evaluator_id = task.evaluator_id;\n"
private def lexTokens18 : List Token := [.identifier (native_c_characters% "g_prime_need_evaluator_id"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "evaluator_id"), .punctuation (native_c_characters% ";")]
private theorem lexPiece18 : lexCharacters18.foldl step initial = completed lexTokens18 := by
  native_c_parser_reflexivity

private def lexCharacters19 : List Char := native_c_characters% "    switch (task.kind) {\n"
private def lexTokens19 : List Token := [.identifier (native_c_characters% "switch"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "kind"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% "{")]
private theorem lexPiece19 : lexCharacters19.foldl step initial = completed lexTokens19 := by
  native_c_parser_reflexivity

private def lexCharacters20 : List Char := native_c_characters% "    case PRIME_EVAL_STACK_TASK_BIND:\n"
private def lexTokens20 : List Token := [.identifier (native_c_characters% "case"), .identifier (native_c_characters% "PRIME_EVAL_STACK_TASK_BIND"), .punctuation (native_c_characters% ":")]
private theorem lexPiece20 : lexCharacters20.foldl step initial = completed lexTokens20 := by
  native_c_parser_reflexivity

private def lexCharacters21 : List Char := native_c_characters% "        cetta_runtime_stats_inc(\n"
private def lexTokens21 : List Token := [.identifier (native_c_characters% "cetta_runtime_stats_inc"), .punctuation (native_c_characters% "(")]
private theorem lexPiece21 : lexCharacters21.foldl step initial = completed lexTokens21 := by
  native_c_parser_reflexivity

private def lexCharacters22 : List Char := native_c_characters% "            CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND);\n"
private def lexTokens22 : List Token := [.identifier (native_c_characters% "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece22 : lexCharacters22.foldl step initial = completed lexTokens22 := by
  native_c_parser_reflexivity

private def lexCharacters23 : List Char := native_c_characters% "        driver->running_bind_task = true;\n"
private def lexTokens23 : List Token := [.identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "running_bind_task"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "true"), .punctuation (native_c_characters% ";")]
private theorem lexPiece23 : lexCharacters23.foldl step initial = completed lexTokens23 := by
  native_c_parser_reflexivity

private def lexCharacters24 : List Char := native_c_characters% "        metta_eval_bind(\n"
private def lexTokens24 : List Token := [.identifier (native_c_characters% "metta_eval_bind"), .punctuation (native_c_characters% "(")]
private theorem lexPiece24 : lexCharacters24.foldl step initial = completed lexTokens24 := by
  native_c_parser_reflexivity

private def lexCharacters25 : List Char := native_c_characters% "            task.space, task.arena, task.atom,\n"
private def lexTokens25 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "space"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "arena"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "atom"), .punctuation (native_c_characters% ",")]
private theorem lexPiece25 : lexCharacters25.foldl step initial = completed lexTokens25 := by
  native_c_parser_reflexivity

private def lexCharacters26 : List Char := native_c_characters% "            task.fuel, task.target);\n"
private def lexTokens26 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "fuel"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "target"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece26 : lexCharacters26.foldl step initial = completed lexTokens26 := by
  native_c_parser_reflexivity

private def lexCharacters27 : List Char := native_c_characters% "        driver->running_bind_task = false;\n"
private def lexTokens27 : List Token := [.identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "running_bind_task"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "false"), .punctuation (native_c_characters% ";")]
private theorem lexPiece27 : lexCharacters27.foldl step initial = completed lexTokens27 := by
  native_c_parser_reflexivity

private def lexCharacters28 : List Char := native_c_characters% "        break;\n"
private def lexTokens28 : List Token := [.identifier (native_c_characters% "break"), .punctuation (native_c_characters% ";")]
private theorem lexPiece28 : lexCharacters28.foldl step initial = completed lexTokens28 := by
  native_c_parser_reflexivity

private def lexCharacters29 : List Char := native_c_characters% "    case PRIME_EVAL_STACK_TASK_CALL:\n"
private def lexTokens29 : List Token := [.identifier (native_c_characters% "case"), .identifier (native_c_characters% "PRIME_EVAL_STACK_TASK_CALL"), .punctuation (native_c_characters% ":")]
private theorem lexPiece29 : lexCharacters29.foldl step initial = completed lexTokens29 := by
  native_c_parser_reflexivity

private def lexCharacters30 : List Char := native_c_characters% "        cetta_runtime_stats_inc(\n"
private def lexTokens30 : List Token := [.identifier (native_c_characters% "cetta_runtime_stats_inc"), .punctuation (native_c_characters% "(")]
private theorem lexPiece30 : lexCharacters30.foldl step initial = completed lexTokens30 := by
  native_c_parser_reflexivity

private def lexCharacters31 : List Char := native_c_characters% "            CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL);\n"
private def lexTokens31 : List Token := [.identifier (native_c_characters% "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece31 : lexCharacters31.foldl step initial = completed lexTokens31 := by
  native_c_parser_reflexivity

private def lexCharacters32 : List Char := native_c_characters% "        metta_call_impl(\n"
private def lexTokens32 : List Token := [.identifier (native_c_characters% "metta_call_impl"), .punctuation (native_c_characters% "(")]
private theorem lexPiece32 : lexCharacters32.foldl step initial = completed lexTokens32 := by
  native_c_parser_reflexivity

private def lexCharacters33 : List Char := native_c_characters% "            task.space, task.arena, task.atom, task.etype,\n"
private def lexTokens33 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "space"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "arena"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "atom"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "etype"), .punctuation (native_c_characters% ",")]
private theorem lexPiece33 : lexCharacters33.foldl step initial = completed lexTokens33 := by
  native_c_parser_reflexivity

private def lexCharacters34 : List Char := native_c_characters% "            task.fuel, task.preserve_bindings,\n"
private def lexTokens34 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "fuel"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "preserve_bindings"), .punctuation (native_c_characters% ",")]
private theorem lexPiece34 : lexCharacters34.foldl step initial = completed lexTokens34 := by
  native_c_parser_reflexivity

private def lexCharacters35 : List Char := native_c_characters% "            task.seed_env_initialized ? &task.seed_env : NULL,\n"
private def lexTokens35 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "seed_env_initialized"), .punctuation (native_c_characters% "?"), .punctuation (native_c_characters% "&"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "seed_env"), .punctuation (native_c_characters% ":"), .identifier (native_c_characters% "NULL"), .punctuation (native_c_characters% ",")]
private theorem lexPiece35 : lexCharacters35.foldl step initial = completed lexTokens35 := by
  native_c_parser_reflexivity

private def lexCharacters36 : List Char := native_c_characters% "            task.strict_ready_argument, task.target);\n"
private def lexTokens36 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "strict_ready_argument"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "target"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece36 : lexCharacters36.foldl step initial = completed lexTokens36 := by
  native_c_parser_reflexivity

private def lexCharacters37 : List Char := native_c_characters% "        break;\n"
private def lexTokens37 : List Token := [.identifier (native_c_characters% "break"), .punctuation (native_c_characters% ";")]
private theorem lexPiece37 : lexCharacters37.foldl step initial = completed lexTokens37 := by
  native_c_parser_reflexivity

private def lexCharacters38 : List Char := native_c_characters% "    case PRIME_EVAL_STACK_TASK_NORMALIZE:\n"
private def lexTokens38 : List Token := [.identifier (native_c_characters% "case"), .identifier (native_c_characters% "PRIME_EVAL_STACK_TASK_NORMALIZE"), .punctuation (native_c_characters% ":")]
private theorem lexPiece38 : lexCharacters38.foldl step initial = completed lexTokens38 := by
  native_c_parser_reflexivity

private def lexCharacters39 : List Char := native_c_characters% "        cetta_runtime_stats_inc(\n"
private def lexTokens39 : List Token := [.identifier (native_c_characters% "cetta_runtime_stats_inc"), .punctuation (native_c_characters% "(")]
private theorem lexPiece39 : lexCharacters39.foldl step initial = completed lexTokens39 := by
  native_c_parser_reflexivity

private def lexCharacters40 : List Char := native_c_characters% "            CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE);\n"
private def lexTokens40 : List Token := [.identifier (native_c_characters% "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece40 : lexCharacters40.foldl step initial = completed lexTokens40 := by
  native_c_parser_reflexivity

private def lexCharacters41 : List Char := native_c_characters% "        {\n"
private def lexTokens41 : List Token := [.punctuation (native_c_characters% "{")]
private theorem lexPiece41 : lexCharacters41.foldl step initial = completed lexTokens41 := by
  native_c_parser_reflexivity

private def lexCharacters42 : List Char := native_c_characters% "            PrimeEvalStackFrame *frame =\n"
private def lexTokens42 : List Token := [.identifier (native_c_characters% "PrimeEvalStackFrame"), .punctuation (native_c_characters% "*"), .identifier (native_c_characters% "frame"), .punctuation (native_c_characters% "=")]
private theorem lexPiece42 : lexCharacters42.foldl step initial = completed lexTokens42 := by
  native_c_parser_reflexivity

private def lexCharacters43 : List Char := native_c_characters% "                prime_eval_stack_normalize_atom_frame_new(\n"
private def lexTokens43 : List Token := [.identifier (native_c_characters% "prime_eval_stack_normalize_atom_frame_new"), .punctuation (native_c_characters% "(")]
private theorem lexPiece43 : lexCharacters43.foldl step initial = completed lexTokens43 := by
  native_c_parser_reflexivity

private def lexCharacters44 : List Char := native_c_characters% "                    task.space, task.arena, task.atom, task.fuel,\n"
private def lexTokens44 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "space"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "arena"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "atom"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "fuel"), .punctuation (native_c_characters% ",")]
private theorem lexPiece44 : lexCharacters44.foldl step initial = completed lexTokens44 := by
  native_c_parser_reflexivity

private def lexCharacters45 : List Char := native_c_characters% "                    &task.dynamic_env, task.evaluator_id,\n"
private def lexTokens45 : List Token := [.punctuation (native_c_characters% "&"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "dynamic_env"), .punctuation (native_c_characters% ","), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "evaluator_id"), .punctuation (native_c_characters% ",")]
private theorem lexPiece45 : lexCharacters45.foldl step initial = completed lexTokens45 := by
  native_c_parser_reflexivity

private def lexCharacters46 : List Char := native_c_characters% "                    task.target);\n"
private def lexTokens46 : List Token := [.identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "target"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece46 : lexCharacters46.foldl step initial = completed lexTokens46 := by
  native_c_parser_reflexivity

private def lexCharacters47 : List Char := native_c_characters% "            if (frame)\n"
private def lexTokens47 : List Token := [.identifier (native_c_characters% "if"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "frame"), .punctuation (native_c_characters% ")")]
private theorem lexPiece47 : lexCharacters47.foldl step initial = completed lexTokens47 := by
  native_c_parser_reflexivity

private def lexCharacters48 : List Char := native_c_characters% "                prime_eval_stack_push(frame);\n"
private def lexTokens48 : List Token := [.identifier (native_c_characters% "prime_eval_stack_push"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "frame"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece48 : lexCharacters48.foldl step initial = completed lexTokens48 := by
  native_c_parser_reflexivity

private def lexCharacters49 : List Char := native_c_characters% "            else\n"
private def lexTokens49 : List Token := [.identifier (native_c_characters% "else")]
private theorem lexPiece49 : lexCharacters49.foldl step initial = completed lexTokens49 := by
  native_c_parser_reflexivity

private def lexCharacters50 : List Char := native_c_characters% "                eval_mark_incomplete(\n"
private def lexTokens50 : List Token := [.identifier (native_c_characters% "eval_mark_incomplete"), .punctuation (native_c_characters% "(")]
private theorem lexPiece50 : lexCharacters50.foldl step initial = completed lexTokens50 := by
  native_c_parser_reflexivity

private def lexCharacters51 : List Char := native_c_characters% "                    CETTA_EVAL_INCOMPLETE_CAPACITY);\n"
private def lexTokens51 : List Token := [.identifier (native_c_characters% "CETTA_EVAL_INCOMPLETE_CAPACITY"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece51 : lexCharacters51.foldl step initial = completed lexTokens51 := by
  native_c_parser_reflexivity

private def lexCharacters52 : List Char := native_c_characters% "        }\n"
private def lexTokens52 : List Token := [.punctuation (native_c_characters% "}")]
private theorem lexPiece52 : lexCharacters52.foldl step initial = completed lexTokens52 := by
  native_c_parser_reflexivity

private def lexCharacters53 : List Char := native_c_characters% "        break;\n"
private def lexTokens53 : List Token := [.identifier (native_c_characters% "break"), .punctuation (native_c_characters% ";")]
private theorem lexPiece53 : lexCharacters53.foldl step initial = completed lexTokens53 := by
  native_c_parser_reflexivity

private def lexCharacters54 : List Char := native_c_characters% "    }\n"
private def lexTokens54 : List Token := [.punctuation (native_c_characters% "}")]
private theorem lexPiece54 : lexCharacters54.foldl step initial = completed lexTokens54 := by
  native_c_parser_reflexivity

private def lexCharacters55 : List Char := native_c_characters% "    g_prime_need_evaluator_id = previous_evaluator_id;\n"
private def lexTokens55 : List Token := [.identifier (native_c_characters% "g_prime_need_evaluator_id"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "previous_evaluator_id"), .punctuation (native_c_characters% ";")]
private theorem lexPiece55 : lexCharacters55.foldl step initial = completed lexTokens55 := by
  native_c_parser_reflexivity

private def lexCharacters56 : List Char := native_c_characters% "    driver->active_task = NULL;\n"
private def lexTokens56 : List Token := [.identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "active_task"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "NULL"), .punctuation (native_c_characters% ";")]
private theorem lexPiece56 : lexCharacters56.foldl step initial = completed lexTokens56 := by
  native_c_parser_reflexivity

private def lexCharacters57 : List Char := native_c_characters% "    if (task.target && task.target->len > published_before)\n"
private def lexTokens57 : List Token := [.identifier (native_c_characters% "if"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "target"), .punctuation (native_c_characters% "&&"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "target"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "len"), .punctuation (native_c_characters% ">"), .identifier (native_c_characters% "published_before"), .punctuation (native_c_characters% ")")]
private theorem lexPiece57 : lexCharacters57.foldl step initial = completed lexTokens57 := by
  native_c_parser_reflexivity

private def lexCharacters58 : List Char := native_c_characters% "        prime_eval_stack_stream_note(task.target);\n"
private def lexTokens58 : List Token := [.identifier (native_c_characters% "prime_eval_stack_stream_note"), .punctuation (native_c_characters% "("), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% "."), .identifier (native_c_characters% "target"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece58 : lexCharacters58.foldl step initial = completed lexTokens58 := by
  native_c_parser_reflexivity

private def lexCharacters59 : List Char := native_c_characters% "    prime_eval_stack_task_free(&task);\n"
private def lexTokens59 : List Token := [.identifier (native_c_characters% "prime_eval_stack_task_free"), .punctuation (native_c_characters% "("), .punctuation (native_c_characters% "&"), .identifier (native_c_characters% "task"), .punctuation (native_c_characters% ")"), .punctuation (native_c_characters% ";")]
private theorem lexPiece59 : lexCharacters59.foldl step initial = completed lexTokens59 := by
  native_c_parser_reflexivity

private def lexCharacters60 : List Char := native_c_characters% "    driver->running_task = false;\n"
private def lexTokens60 : List Token := [.identifier (native_c_characters% "driver"), .punctuation (native_c_characters% "->"), .identifier (native_c_characters% "running_task"), .punctuation (native_c_characters% "="), .identifier (native_c_characters% "false"), .punctuation (native_c_characters% ";")]
private theorem lexPiece60 : lexCharacters60.foldl step initial = completed lexTokens60 := by
  native_c_parser_reflexivity

private def lexCharacters61 : List Char := native_c_characters% "}"
private def lexTokens61 : List Token := [.punctuation (native_c_characters% "}")]
private theorem lexPiece61 : lexCharacters61.foldl step initial = completed lexTokens61 := by
  native_c_parser_reflexivity

private def sourcePieces : List (List Char × List Token) := [(lexCharacters0, lexTokens0), (lexCharacters1, lexTokens1), (lexCharacters2, lexTokens2), (lexCharacters3, lexTokens3), (lexCharacters4, lexTokens4), (lexCharacters5, lexTokens5), (lexCharacters6, lexTokens6), (lexCharacters7, lexTokens7), (lexCharacters8, lexTokens8), (lexCharacters9, lexTokens9), (lexCharacters10, lexTokens10), (lexCharacters11, lexTokens11), (lexCharacters12, lexTokens12), (lexCharacters13, lexTokens13), (lexCharacters14, lexTokens14), (lexCharacters15, lexTokens15), (lexCharacters16, lexTokens16), (lexCharacters17, lexTokens17), (lexCharacters18, lexTokens18), (lexCharacters19, lexTokens19), (lexCharacters20, lexTokens20), (lexCharacters21, lexTokens21), (lexCharacters22, lexTokens22), (lexCharacters23, lexTokens23), (lexCharacters24, lexTokens24), (lexCharacters25, lexTokens25), (lexCharacters26, lexTokens26), (lexCharacters27, lexTokens27), (lexCharacters28, lexTokens28), (lexCharacters29, lexTokens29), (lexCharacters30, lexTokens30), (lexCharacters31, lexTokens31), (lexCharacters32, lexTokens32), (lexCharacters33, lexTokens33), (lexCharacters34, lexTokens34), (lexCharacters35, lexTokens35), (lexCharacters36, lexTokens36), (lexCharacters37, lexTokens37), (lexCharacters38, lexTokens38), (lexCharacters39, lexTokens39), (lexCharacters40, lexTokens40), (lexCharacters41, lexTokens41), (lexCharacters42, lexTokens42), (lexCharacters43, lexTokens43), (lexCharacters44, lexTokens44), (lexCharacters45, lexTokens45), (lexCharacters46, lexTokens46), (lexCharacters47, lexTokens47), (lexCharacters48, lexTokens48), (lexCharacters49, lexTokens49), (lexCharacters50, lexTokens50), (lexCharacters51, lexTokens51), (lexCharacters52, lexTokens52), (lexCharacters53, lexTokens53), (lexCharacters54, lexTokens54), (lexCharacters55, lexTokens55), (lexCharacters56, lexTokens56), (lexCharacters57, lexTokens57), (lexCharacters58, lexTokens58), (lexCharacters59, lexTokens59), (lexCharacters60, lexTokens60), (lexCharacters61, lexTokens61)]

private theorem characters_from_pieces : sourcePieces.flatMap Prod.fst = characters := by
  native_c_parser_reflexivity

def tokens : List Token := sourcePieces.flatMap Prod.snd

theorem actual_characters_lexed : lex characters = .ok tokens := by
  rw [← characters_from_pieces]
  apply lex_of_completed
  apply completed_pieces sourcePieces
  simp only [sourcePieces, List.forall_cons]
  exact ⟨lexPiece0, lexPiece1, lexPiece2, lexPiece3, lexPiece4, lexPiece5, lexPiece6, lexPiece7, lexPiece8, lexPiece9, lexPiece10, lexPiece11, lexPiece12, lexPiece13, lexPiece14, lexPiece15, lexPiece16, lexPiece17, lexPiece18, lexPiece19, lexPiece20, lexPiece21, lexPiece22, lexPiece23, lexPiece24, lexPiece25, lexPiece26, lexPiece27, lexPiece28, lexPiece29, lexPiece30, lexPiece31, lexPiece32, lexPiece33, lexPiece34, lexPiece35, lexPiece36, lexPiece37, lexPiece38, lexPiece39, lexPiece40, lexPiece41, lexPiece42, lexPiece43, lexPiece44, lexPiece45, lexPiece46, lexPiece47, lexPiece48, lexPiece49, lexPiece50, lexPiece51, lexPiece52, lexPiece53, lexPiece54, lexPiece55, lexPiece56, lexPiece57, lexPiece58, lexPiece59, lexPiece60, lexPiece61, by trivial⟩

theorem actual_tokens_parsed :
    functionUsing? (declaratorParameter? names) (2 * tokens.length + 4) names
      (ordinaryFunctionTokens tokens) = some (runSyntax, []) := by
  native_c_parser_reflexivity

theorem actual_task_parses : declaratorFunctionText? names characters = some runSyntax :=
  function_text_using_of_parts (declaratorParameter? names) names characters tokens runSyntax
    actual_characters_lexed actual_tokens_parsed

theorem original_source_recognized :
    declaratorFunctionText? names source.toList = some runSyntax := by
  rw [characters_are_actual_source]
  exact actual_task_parses

/-- The source admission executes the whole retained body through the existing
scoped engine. Its declaration, aggregate-call, effect, layout and cleanup
providers need their own physical/source realization; parser agreement grants
none of those permissions. No endpoint readout hides incomplete flow. -/
def fromOriginal (services : StatementBlock.ScopedServices Context) (layout : Layout)
    (loopFuel fuel : Nat) (context : Context) : CProg CVal (ReadBlock.Result Context) :=
  StatementBlock.executeParsedBody
    (StatementBlock.executeScopedWith services layout loopFuel fuel context)
    (declaratorFunctionText? names source.toList)

theorem original_source_executes_retained_body
    (services : StatementBlock.ScopedServices Context) (layout : Layout)
    (loopFuel fuel : Nat) (context : Context) :
    fromOriginal services layout loopFuel fuel context =
      StatementBlock.executeScopedWith services layout loopFuel fuel context runSyntax.body := by
  unfold fromOriginal
  rw [original_source_recognized, StatementBlock.execute_parsed_body_some]

theorem source_keeps_twenty_top_level_statements : runSyntax.body.length = 20 := rfl

end Mettapedia.Languages.MeTTa.CeTTaNativeCost.RunTaskSource

namespace Mettapedia.Languages.MeTTa.CeTTaNativeCost.CapturedRun

/-- Presence is supplied by the admitted carrier's actual predicates. It
does not inspect spellings, discard a carrier's contents or grant ownership
of the addresses in those contents. -/
structure Presence where
  need : Bool
  branch : Bool
  weights : Bool
  receipt : Bool
  deriving DecidableEq

variable {Need Branch Weights Receipt : Type}

/-- Ordinary task entry overlays only the present components. A non-null
environment always replaces the logical reference; null inherits every view.
This differs from a retained computation's complete captured installation. -/
def overlay (presence : Views Need Branch Weights Receipt → Presence)
    (environment : Option (Nat × Views Need Branch Weights Receipt))
    (caller : Views Need Branch Weights Receipt) : Views Need Branch Weights Receipt :=
  match environment with
  | none => caller
  | some (identity, captured) =>
      { need := if (presence captured).need then captured.need else caller.need
        branch := if (presence captured).branch then captured.branch else caller.branch
        weights := if (presence captured).weights then captured.weights else caller.weights
        receipt := if (presence captured).receipt then captured.receipt else caller.receipt
        logical := some identity }

/-- Ordinary task activation changes these views and no allocation owners,
driver selection or outer scope inventory. -/
def taskInstall (presence : Views Need Branch Weights Receipt → Presence)
    (environment : Option (Nat × Views Need Branch Weights Receipt))
    (caller : Context Need Branch Weights Receipt) : Context Need Branch Weights Receipt :=
  { caller with views := overlay presence environment caller.views }

theorem null_task_environment_inherits_every_view
    (presence : Views Need Branch Weights Receipt → Presence)
    (caller : Views Need Branch Weights Receipt) :
    overlay presence none caller = caller := rfl

theorem task_entry_retains_owners_and_outer_control
    (presence : Views Need Branch Weights Receipt → Presence)
    (environment : Option (Nat × Views Need Branch Weights Receipt))
    (caller : Context Need Branch Weights Receipt) :
    (taskInstall presence environment caller).driver = caller.driver ∧
      (taskInstall presence environment caller).first = caller.first ∧
      (taskInstall presence environment caller).needOwner = caller.needOwner ∧
      (taskInstall presence environment caller).episodeOwner = caller.episodeOwner ∧
      (taskInstall presence environment caller).branchOwner = caller.branchOwner ∧
      (taskInstall presence environment caller).regionPool = caller.regionPool :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nonnull_task_keeps_logical_reference
    (presence : Views Need Branch Weights Receipt → Presence)
    (identity : Nat) (captured caller : Views Need Branch Weights Receipt) :
    (overlay presence (some (identity, captured)) caller).logical = some identity := rfl

theorem absent_components_are_inherited
    (presence : Views Need Branch Weights Receipt → Presence)
    (identity : Nat) (captured caller : Views Need Branch Weights Receipt)
    (absent : presence captured = ⟨false, false, false, false⟩) :
    overlay presence (some (identity, captured)) caller =
      { caller with logical := some identity } := by
  simp only [overlay, absent, Bool.false_eq_true, ↓reduceIte]

theorem present_components_replace_complete_carriers
    (presence : Views Need Branch Weights Receipt → Presence)
    (identity : Nat) (captured caller : Views Need Branch Weights Receipt)
    (present : presence captured = ⟨true, true, true, true⟩) :
    overlay presence (some (identity, captured)) caller =
      { captured with logical := some identity } := by
  simp only [overlay, present, ↓reduceIte]

/-- A presence-preserving map transports all complete carriers and the
logical identity. The theorem does not infer injectivity, pointer ownership
or permission to erase receipt distinctions. -/
def Views.map {OtherNeed OtherBranch OtherWeights OtherReceipt : Type}
    (need : Need → OtherNeed) (branch : Branch → OtherBranch)
    (weights : Weights → OtherWeights) (receipt : Receipt → OtherReceipt)
    (logical : Nat → Nat) (view : Views Need Branch Weights Receipt) :
    Views OtherNeed OtherBranch OtherWeights OtherReceipt :=
  { need := need view.need, branch := branch view.branch
    weights := weights view.weights, receipt := receipt view.receipt
    logical := view.logical.map logical }

theorem overlay_transport {OtherNeed OtherBranch OtherWeights OtherReceipt : Type}
    (need : Need → OtherNeed) (branch : Branch → OtherBranch)
    (weights : Weights → OtherWeights) (receipt : Receipt → OtherReceipt)
    (logical : Nat → Nat)
    (presence : Views Need Branch Weights Receipt → Presence)
    (otherPresence : Views OtherNeed OtherBranch OtherWeights OtherReceipt → Presence)
    (environment : Option (Nat × Views Need Branch Weights Receipt))
    (caller : Views Need Branch Weights Receipt)
    (law : ∀ view, otherPresence (view.map need branch weights receipt logical) = presence view) :
    (overlay presence environment caller).map need branch weights receipt logical =
      overlay otherPresence
        (environment.map (fun entry =>
          (logical entry.1, entry.2.map need branch weights receipt logical)))
        (caller.map need branch weights receipt logical) := by
  cases environment with
  | none => rfl
  | some entry =>
      rcases entry with ⟨identity, captured⟩
      simp only [Option.map_some, overlay]
      rw [law captured]
      simp only [Views.map, Option.map_some]
      congr 1 <;> split <;> rfl

namespace OverlayControls

abbrev TestViews := Views (Option Nat) (Option Nat) (List Nat) (Option Nat)

def caller : TestViews := ⟨some 11, some 12, [13, 13], some 14, some 15⟩
def empty : TestViews := ⟨none, none, [], none, none⟩

def actualPresence (view : TestViews) : Presence :=
  ⟨view.need.isSome, view.branch.isSome, !view.weights.isEmpty, view.receipt.isSome⟩

theorem empty_ordinary_overlay_keeps_caller_dependencies :
    overlay actualPresence (some (20, empty)) caller =
      ⟨some 11, some 12, [13, 13], some 14, some 20⟩ := rfl

def callerContext : Context (Option Nat) (Option Nat) (List Nat) (Option Nat) :=
  ⟨caller, some 21, some 22, some 23, some 24, some 25, some 26⟩

def complete : Config (Option Nat) (Option Nat) (List Nat) (Option Nat) :=
  ⟨some empty, 30, none, 31, none, none⟩

theorem complete_capture_replaces_empty_components :
    (install complete callerContext).views = empty := rfl

theorem ordinary_overlay_is_not_complete_capture :
    overlay actualPresence (some (20, empty)) caller ≠ (install complete callerContext).views := by
  intro same
  have impossible := congrArg Views.need same
  cases impossible

theorem present_duplicate_weights_are_not_aggregated :
    (overlay actualPresence (some (20, {empty with weights := [4, 4]})) caller).weights = [4, 4] := rfl

theorem null_overlay_does_not_clear_logical_reference :
    (overlay actualPresence none caller).logical = some 15 := rfl

end OverlayControls

end Mettapedia.Languages.MeTTa.CeTTaNativeCost.CapturedRun

namespace Mettapedia.Languages.MeTTa.CeTTaNativeCost.RunTaskSource.Authority

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.Machines.CMemory
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u

/-- The current driver location and the admitted authority-field offset.
The two guard cells are a logical record representation; native layout and
automatic-storage admission remain separate source/ABI obligations. -/
structure Layout where
  currentDriver : Ptr
  pureOffset : Nat

/-- The actual authority-enter algorithm snapshots the selected driver's
previous flag and then changes that same driver's flag. It keeps both pointer
conditions, including their validity requirements. -/
def enterFromDriver (layout : Layout) (driver : Option Ptr) (incoming : Bool) :
    CProg CVal (List CVal) := do
  let nullForPrevious ← CProg.ptrEq driver none
  let previous ← if nullForPrevious then pure false else match driver with
    | some driver => CProg.loadBool (driver + layout.pureOffset)
    | none => CProg.undefined
  let nullForWrite ← CProg.ptrEq driver none
  if nullForWrite then pure () else match driver with
    | some driver => CProg.store (driver + layout.pureOffset) (.bool incoming)
    | none => CProg.undefined
  pure [.ptr driver, .bool previous]

def enter (layout : Layout) (incoming : Bool) : CProg CVal (List CVal) := do
  let driver ← CProg.loadPtr layout.currentDriver
  enterFromDriver layout driver incoming

/-- Cleanup restores the driver stored in the guard, never a fresh lookup of
the active global driver. Both authored driver-field reads are retained. The
admitted assignment order reads the previous flag before the destination;
the source comparison separately justifies their commuting read order. -/
def leave (layout : Layout) (guard : Ptr) : CProg CVal Unit := do
  let captured ← CProg.loadPtr guard
  let isNull ← CProg.ptrEq captured none
  if isNull then pure () else do
    let previous ← CProg.loadBool (guard + 1)
    let destination ← CProg.loadPtr guard
    match destination with
    | some driver => CProg.store (driver + layout.pureOffset) (.bool previous)
    | none => CProg.undefined

def recordCall (layout : Layout) : StatementBlock.ObjectBindings.RecordCall where
  resultType := ⟨"PrimeEvalAuthorityGuard".toList, 0⟩
  invoke := fun arguments => match arguments with
    | [.bool incoming] => enter layout incoming
    | _ => CProg.undefined

section Physical

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

/-- The guard needs the driver's live header and exclusive flag cell.
Other driver fields, dependencies and logical scopes are retained by framing. -/
def driverMemory (layout : Layout) (driver : Ptr) (cells : Nat) (flag : Bool) : Heap L → Prop :=
  LiveBlock driver.block cells ∗ PointsTo (driver + layout.pureOffset) (.bool flag)

private theorem driver_valid (layout : Layout) (driver : Ptr) (cells : Nat) (flag : Bool)
    (inside : driver.offset ≤ cells) (heap : Heap L)
    (held : driverMemory layout driver cells flag heap) : ValidOpt heap (some driver) :=
  valid_of_liveBlock held inside

private theorem stored_flag (layout : Layout) (driver : Ptr) (cells : Nat)
    (previous incoming : Bool) :
    CTriple (L := L) (driverMemory layout driver cells previous)
      (CProg.store (driver + layout.pureOffset) (.bool incoming))
      (fun _ => driverMemory layout driver cells incoming) := by
  exact frame_left (triple_pre _ (fun _ held => ⟨some (.bool previous), held⟩)
    (store_spec (L := L) (driver + layout.pureOffset) (.bool incoming)))
    (LiveBlock driver.block cells)

theorem nonnull_entry_keeps_saved_identity_and_previous_flag (layout : Layout)
    (driver : Ptr) (cells : Nat) (previous incoming : Bool) (inside : driver.offset ≤ cells) :
    CTriple (L := L) (driverMemory layout driver cells previous)
      (enterFromDriver layout (some driver) incoming)
      (fun result heap => result = [.ptr (some driver), .bool previous] ∧
        driverMemory layout driver cells incoming heap) := by
  unfold enterFromDriver
  simp only [Prog.bind_eq]
  refine triple_bind _ (ptrEq_rule (p := some driver) (q := none)
    (fun heap held => ⟨driver_valid layout driver cells previous inside heap held, trivial⟩))
    fun test => ?_
  apply triple_pure
  intro actual
  have nullFalse : test = false := by simpa using actual
  subst test
  refine triple_bind _ (loadBool_rule (b := previous) fun _ held =>
    read_of_pointsTo_right held) fun saved => ?_
  apply triple_pure
  intro savedSame
  subst saved
  refine triple_bind _ (ptrEq_rule (p := some driver) (q := none)
    (fun heap held => ⟨driver_valid layout driver cells previous inside heap held, trivial⟩))
    fun test => ?_
  apply triple_pure
  intro actual
  have nullFalse : test = false := by simpa using actual
  subst test
  refine triple_bind _ (stored_flag layout driver cells previous incoming) fun _ => ?_
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩)
    (triple_ret act [CVal.ptr (some driver), CVal.bool previous]
      (fun result heap => result = [CVal.ptr (some driver), CVal.bool previous] ∧
        driverMemory (L := L) layout driver cells incoming heap))

theorem null_entry_never_reads_or_writes_a_driver (layout : Layout) (incoming : Bool)
    (P : Heap L → Prop) :
    CTriple P (enterFromDriver layout none incoming)
      (fun result heap => result = [.ptr none, .bool false] ∧ P heap) := by
  unfold enterFromDriver
  simp only [Prog.bind_eq]
  refine triple_bind _ (ptrEq_rule (p := none) (q := none) (fun _ _ => ⟨trivial, trivial⟩))
    fun test => ?_
  apply triple_pure
  intro actual
  have nullTrue : test = true := by simpa using actual
  subst test
  simp only [Prog.pure_eq, Prog.ret_bind]
  refine triple_bind _ (ptrEq_rule (p := none) (q := none) (fun _ _ => ⟨trivial, trivial⟩))
    fun test => ?_
  apply triple_pure
  intro actual
  have nullTrue : test = true := by simpa using actual
  subst test
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩)
    (triple_ret act [CVal.ptr none, CVal.bool false]
      (fun result heap => result = [CVal.ptr none, CVal.bool false] ∧ P heap))

theorem current_driver_is_read_before_entry (layout : Layout) (incoming : Bool) :
    enter layout incoming =
      (CProg.loadPtr layout.currentDriver >>= fun driver =>
        enterFromDriver layout driver incoming) := rfl

/-- Entry reads the actual selected driver cell, then composes the
non-null field service. The global pointer and all unrelated fields stay
owned and unchanged; validity is supplied by the driver's live block. -/
theorem current_nonnull_entry (layout : Layout) (driver : Ptr) (cells : Nat)
    (previous incoming : Bool) (inside : driver.offset ≤ cells) :
    CTriple (L := L)
      (PointsTo layout.currentDriver (.ptr (some driver)) ∗
        driverMemory layout driver cells previous)
      (enter layout incoming)
      (fun result heap => result = [.ptr (some driver), .bool previous] ∧
        (PointsTo layout.currentDriver (.ptr (some driver)) ∗
          driverMemory layout driver cells incoming) heap) := by
  unfold enter
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadPtr_rule (q := some driver) fun _ held =>
    read_of_pointsTo held) fun selected => ?_
  apply triple_pure
  intro same
  subst selected
  apply triple_post _ (frame_left
    (nonnull_entry_keeps_saved_identity_and_previous_flag layout driver cells previous incoming inside)
    (PointsTo layout.currentDriver (CVal.ptr (some driver))))
  intro result heap held
  rw [sepConj_pure_right] at held
  exact held

/-- The null global selection still performs its pointer-cell read and
both null tests, while retaining the complete framed caller memory. -/
theorem current_null_entry (layout : Layout) (incoming : Bool)
    (F : Heap L → Prop) :
    CTriple (L := L) (PointsTo layout.currentDriver (.ptr none) ∗ F)
      (enter layout incoming)
      (fun result heap => result = [.ptr none, .bool false] ∧
        (PointsTo layout.currentDriver (.ptr none) ∗ F) heap) := by
  unfold enter
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadPtr_rule (q := none) fun _ held =>
    read_of_pointsTo held) fun selected => ?_
  apply triple_pure
  intro same
  subst selected
  exact null_entry_never_reads_or_writes_a_driver layout incoming _

def guardMemory (layout : Layout) (guard driver : Ptr) (cells : Nat)
    (saved current : Bool) : Heap L → Prop :=
  Cells guard [some (.ptr (some driver)), some (.bool saved)] ∗
    driverMemory layout driver cells current

private theorem guard_valid (layout : Layout) (guard driver : Ptr) (cells : Nat)
    (saved current : Bool) (inside : driver.offset ≤ cells) (heap : Heap L)
    (held : guardMemory layout guard driver cells saved current heap) :
    ValidOpt heap (some driver) := by
  rw [guardMemory, sepConj_comm, driverMemory, sepConj_assoc] at held
  exact valid_of_liveBlock held inside

theorem cleanup_restores_the_saved_driver_and_preserves_guard (layout : Layout)
    (guard driver : Ptr) (cells : Nat) (saved current : Bool) (inside : driver.offset ≤ cells) :
    CTriple (L := L) (guardMemory layout guard driver cells saved current)
      (leave layout guard)
      (fun _ => guardMemory layout guard driver cells saved saved) := by
  unfold leave
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadPtr_rule (q := some driver) fun _ held =>
    read_cells (i := 0) (by simp) (by rfl) held) fun captured => ?_
  apply triple_pure
  intro same
  subst captured
  refine triple_bind _ (ptrEq_rule (p := some driver) (q := none)
    (fun heap held => ⟨guard_valid layout guard driver cells saved current inside heap held, trivial⟩))
    fun test => ?_
  apply triple_pure
  intro actual
  have nullFalse : test = false := by simpa using actual
  subst test
  refine triple_bind _ (loadBool_rule (b := saved) fun _ held =>
    read_cells (i := 1) (by simp) (by rfl) held) fun previous => ?_
  apply triple_pure
  intro same
  subst previous
  refine triple_bind _ (loadPtr_rule (q := some driver) fun _ held =>
    read_cells (i := 0) (by simp) (by rfl) held) fun destination => ?_
  apply triple_pure
  intro same
  subst destination
  exact frame_left (stored_flag layout driver cells current saved)
    (Cells guard [some (CVal.ptr (some driver)), some (CVal.bool saved)])

theorem null_cleanup_does_not_read_previous_flag (layout : Layout) (guard : Ptr)
    (F : Heap L → Prop) :
    CTriple (L := L) (PointsTo guard (.ptr none) ∗ F) (leave layout guard)
      (fun _ => PointsTo guard (.ptr none) ∗ F) := by
  unfold leave
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadPtr_rule (q := none) fun _ held => read_of_pointsTo held)
    fun captured => ?_
  apply triple_pure
  intro same
  subst captured
  refine triple_bind _ (ptrEq_rule (p := none) (q := none) (fun _ _ => ⟨trivial, trivial⟩))
    fun test => ?_
  apply triple_pure
  intro actual
  have nullTrue : test = true := by simpa using actual
  subst test
  simpa using
    (triple_ret act () (fun _ => PointsTo guard (CVal.ptr none) ∗ F))

end Physical

namespace Controls

theorem record_call_retains_boolean_input (layout : Layout) (incoming : Bool) :
    (recordCall layout).invoke [.bool incoming] = enter layout incoming := rfl

theorem record_call_does_not_accept_unsigned_as_authority (layout : Layout) (value : UInt32) :
    (recordCall layout).invoke [.u32 value] = CProg.undefined := rfl

theorem record_call_does_not_accept_missing_authority (layout : Layout) :
    (recordCall layout).invoke [] = CProg.undefined := rfl

end Controls

end Mettapedia.Languages.MeTTa.CeTTaNativeCost.RunTaskSource.Authority

namespace Mettapedia.Languages.MeTTa.CeTTaNativeCost.RunTaskSource.Execution

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Machines.CMemory
open ReadExpressions
open StatementBlock.ObjectBindings (Context)

private def ctype (name : String) (depth : Nat := 0) : CType := ⟨name.toList, depth⟩

/-- The Task inventory is shared with admission. Additional locations and
record extents belong to the runner's actual source. Logical cells and
native byte layout are separate; the physical realization supplies their
type, bounds, alignment, encoding and lifetime correspondence. -/
structure RunLayout extends TaskAdmission.TaskLayout where
  evaluatorId : Ptr
  outcomeLength : Nat
  needCells : Nat
  needCellsPositive : 0 < needCells

def RunLayout.authority (layout : RunLayout) : Authority.Layout :=
  ⟨layout.currentDriver, layout.driverOffset "pure_authority".toList⟩

/-- Each void callback retains its actual typed source operands. The Need
entry returns every guard cell by value; no pointer or Boolean stands in
for the guard. Normalization reuses the existing interpreted constructor,
including its allocation, root capture, refusal and retirement operations.
Automatic storage and native callback/lifetime realization remain explicit
obligations of these supplied services. -/
structure Operations where
  bind : Option Ptr → Option Ptr → Option Ptr → Int32 → Option Ptr → CProg CVal Unit
  call : Option Ptr → Option Ptr → Option Ptr → Option Ptr → Int32 → Bool →
    Option Ptr → Int32 → Option Ptr → CProg CVal Unit
  constructor : NormalizeAtomConstructor.ConstructorOperations
  constructorLayout : NormalizeAtomConstructor.FrameLayout
  needEnter : Ptr → CProg CVal (List CVal)
  needLeave : Ptr → CProg CVal Unit
  zeroTask : Ptr → UInt64 → CProg CVal Unit
  releaseTask : Ptr → CProg CVal Unit
  push : Ptr → CProg CVal Unit
  streamNote : Option Ptr → CProg CVal Unit
  markIncomplete : Int32 → CProg CVal Unit
  statistics : Int32 → CProg CVal Unit
  region : StatementBlock.AutomaticRegion Context
  assertions : Bool

/-- Only a normally returned nullable frame is a constructor result.
Exhaustion, fallthrough and scalar replies keep undefined rather than
fabricating either successful allocation or normal refusal. -/
def frameReply : ReadBlock.Result → CProg CVal CVal
  | .finished (.returned _ (some (.ptr frame))) => pure (.ptr frame)
  | _ => CProg.undefined

def constructorValues (operations : Operations) : Calls := fun name arguments =>
  if name = "prime_eval_stack_normalize_atom_frame_new".toList then match arguments with
    | [.ptr space, .ptr arena, .ptr atom, .i32 fuel, .ptr environment,
        .u64 evaluator, .ptr target] =>
      NormalizeAtomConstructor.interpretedConstructor operations.constructor
        operations.constructorLayout
        ⟨space, arena, atom, environment, target, fuel, evaluator⟩ >>= frameReply
    | _ => CProg.undefined
  else CProg.undefined

def needRecord (operations : Operations) : StatementBlock.ObjectBindings.RecordCall where
  resultType := ctype "PrimeNeedActiveGuard"
  invoke := fun arguments => match arguments with
    | [.ptr (some environment)] => operations.needEnter environment
    | _ => CProg.undefined

def recordCalls (operations : Operations) (layout : RunLayout) :
    Name → Option StatementBlock.ObjectBindings.RecordCall := fun name =>
  if name = "prime_eval_authority_enter".toList then some (Authority.recordCall layout.authority)
  else if name = "prime_need_active_enter".toList then some (needRecord operations)
  else none

/-- Assertions are source macros. An enabled assertion evaluates its actual
operand and rejects a false value; a disabled assertion omits its argument
evaluation in `omittedMacros`, before the void-call service is reached.
A false assertion is outside this admitted normal-return fragment; its
undefined operation is not an interpretation of native abort as ISO C
undefined behavior or as a normal resource refusal. -/
def effects (operations : Operations) : CallService Unit := fun name arguments =>
  if name = "assert".toList then match arguments with
    | [value] => truth value >>= fun accepted =>
        if accepted then pure () else CProg.undefined
    | _ => CProg.undefined
  else if name = "metta_eval_bind".toList then match arguments with
    | [.ptr space, .ptr arena, .ptr atom, .i32 fuel, .ptr target] =>
      operations.bind space arena atom fuel target
    | _ => CProg.undefined
  else if name = "metta_call_impl".toList then match arguments with
    | [.ptr space, .ptr arena, .ptr atom, .ptr etype, .i32 fuel,
        .bool preserve, .ptr seed, .i32 strictIndex, .ptr target] =>
      operations.call space arena atom etype fuel preserve seed strictIndex target
    | _ => CProg.undefined
  else if name = "memset".toList then match arguments with
    | [.ptr (some task), .i32 zero, .u64 bytes] =>
        if zero = 0 then operations.zeroTask task bytes else CProg.undefined
    | _ => CProg.undefined
  else if name = "prime_eval_stack_task_free".toList then match arguments with
    | [.ptr (some task)] => operations.releaseTask task
    | _ => CProg.undefined
  else if name = "prime_eval_stack_push".toList then match arguments with
    | [.ptr (some frame)] => operations.push frame
    | _ => CProg.undefined
  else if name = "prime_eval_stack_stream_note".toList then match arguments with
    | [.ptr target] => operations.streamNote target
    | _ => CProg.undefined
  else if name = "eval_mark_incomplete".toList then match arguments with
    | [.i32 reason] => operations.markIncomplete reason
    | _ => CProg.undefined
  else if name = "cetta_runtime_stats_inc".toList then match arguments with
    | [.i32 counter] => operations.statistics counter
    | _ => CProg.undefined
  else CProg.undefined

def omittedMacros (operations : Operations) : EffectStatements.OmittedMacros := fun name =>
  if !operations.assertions && name == "assert".toList then some 1 else none

/-- Cleanup dispatches only the two authored callbacks. Each receives the
actual still-live automatic guard address and retains the completed flow
until restoration. Unknown callback names are not silent no-ops. -/
def cleanup (operations : Operations) (layout : RunLayout) :
    Name → Ptr → ReadBlock.Flow Context → CProg CVal Unit := fun name guard _ =>
  if name = "prime_eval_authority_leave".toList then Authority.leave layout.authority guard
  else if name = "prime_need_active_leave".toList then operations.needLeave guard
  else CProg.undefined

def driverFields (layout : RunLayout) : Layout := fun name =>
  if name = "running_task".toList then some ⟨layout.driverOffset name, .boolean⟩ else
  if name = "running_bind_task".toList then some ⟨layout.driverOffset name, .boolean⟩ else
  if name = "active_task".toList then some ⟨layout.driverOffset name, .pointer⟩ else
  TaskAdmission.driverFields layout.toTaskLayout name

def recordLayouts (layout : RunLayout) : CType → Layout := fun record =>
  if record = ctype "PrimeEvalStackTask" then TaskAdmission.taskFields layout.toTaskLayout else
  if record = ctype "PrimeEvalStackDriver" then driverFields layout else
  if record = ctype "OutcomeSet" then fun name =>
    if name = "len".toList then some ⟨layout.outcomeLength, .word64⟩ else none
  else fun _ => none

def fieldTypes : ScalarBytes.FieldTypes := fun owner name =>
  if owner = ctype "PrimeEvalStackDriver" &&
      (name == "running_task".toList || name == "running_bind_task".toList) then
    some (ctype "bool") else
  if owner = ctype "PrimeEvalStackDriver" && name == "active_task".toList then
    some (ctype "PrimeEvalStackTask" 1) else
  if owner = ctype "OutcomeSet" && name == "len".toList then some (ctype "CettaCount") else
  TaskAdmission.fieldTypes owner name

def caseConstants : ScalarRead.Environment Ptr := fun name =>
  if name = "PRIME_EVAL_STACK_TASK_BIND".toList then some (.unsigned 0) else
  if name = "PRIME_EVAL_STACK_TASK_CALL".toList then some (.unsigned 1) else
  if name = "PRIME_EVAL_STACK_TASK_NORMALIZE".toList then some (.unsigned 2) else none

/-- Immutable source enumeration bindings use signed int values for the
counter/reason call operands. Their exact source enumeration and effective
representation are checked separately; they are not selected by runtime
boundness or the current mathematical weight algebra. -/
def initialContext : Context := fun name =>
  if name = "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList then
    some (.scalar (ctype "int") (some (.i32 262))) else
  if name = "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList then
    some (.scalar (ctype "int") (some (.i32 263))) else
  if name = "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList then
    some (.scalar (ctype "int") (some (.i32 264))) else
  if name = "CETTA_EVAL_INCOMPLETE_CAPACITY".toList then
    some (.scalar (ctype "int") (some (.i32 4))) else none

/-- Global scalar reads and writable places share one typed address inventory.
A local declaration still shields that inventory; missing names have no place. -/
def globalLocations (layout : RunLayout) : Locations := fun name =>
  if name = "g_prime_eval_stack_driver".toList then some (layout.currentDriver, .pointer) else
  if name = "g_prime_need_evaluator_id".toList then some (layout.evaluatorId, .word64) else none

def profile (operations : Operations) (layout : RunLayout) : StatementBlock.ObjectBindings.Profile where
  values := constructorValues operations
  locations := globalLocations layout
  outsideTypes := fun name =>
    if name = "g_prime_eval_stack_driver".toList then some (ctype "PrimeEvalStackDriver" 1) else
    if name = "g_prime_need_evaluator_id".toList then some (ctype "uint64_t") else none
  outsidePlaces := fun name => (globalLocations layout name).map Prod.fst
  fieldTypes := fieldTypes
  cellExtent := fun record =>
    if record = ctype "PrimeEvalStackTask" then some layout.taskCells else
    if record = ctype "PrimeEvalAuthorityGuard" then some 2 else
    if record = ctype "PrimeNeedActiveGuard" then some layout.needCells else none
  byteExtent := fun record =>
    if record = ctype "PrimeEvalStackTask" then some layout.taskBytes else none
  sizeWidth := .bits64
  recordFields := some (recordLayouts layout)
  caseConstants := caseConstants
  recordCalls := recordCalls operations layout
  scalarAliases := fun record =>
    if record = ctype "CettaCount" then some (ctype "uint64_t") else none

def services (operations : Operations) (layout : RunLayout) : StatementBlock.ScopedServices Context :=
  StatementBlock.ObjectBindings.services (profile operations layout) operations.region
    (EffectStatements.withObjectMacros (profile operations layout) (effects operations)
      (omittedMacros operations)) (cleanup operations layout)

theorem global_evaluator_keeps_writable_place (operations : Operations) (layout : RunLayout)
    (context : Context) (outside : context "g_prime_need_evaluator_id".toList = none) :
    StatementBlock.ObjectBindings.place (profile operations layout) (fun _ => none) context
      (.identifier "g_prime_need_evaluator_id".toList) = pure layout.evaluatorId := by
  simp only [StatementBlock.ObjectBindings.place, placeWithNames.eq_def,
    StatementBlock.ObjectBindings.objects, StatementBlock.ObjectBindings.places,
    outside, Option.bind_some]
  change resolved (some layout.evaluatorId) = _
  rfl

theorem global_evaluator_write_keeps_typed_value (operations : Operations) (layout : RunLayout)
    (context : Context) (value : UInt64)
    (outside : context "g_prime_need_evaluator_id".toList = none) :
    StatementBlock.ObjectBindings.writeValue (profile operations layout) (fun _ => none) context
      (.identifier "g_prime_need_evaluator_id".toList) (.u64 value) =
      (CProg.store layout.evaluatorId (.u64 value) >>= fun _ => pure context) := by
  simp only [StatementBlock.ObjectBindings.writeValue, outside]
  change (pure (.u64 value) >>= fun converted =>
    StatementBlock.ObjectBindings.place (profile operations layout) (fun _ => none) context
      (.identifier "g_prime_need_evaluator_id".toList) >>= fun address =>
        CProg.store address converted >>= fun _ => pure context) = _
  rw [global_evaluator_keeps_writable_place operations layout context outside]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

theorem constructor_call_keeps_complete_interpreted_callee (operations : Operations)
    (input : NormalizeAtomConstructor.ConstructorInputs) :
    constructorValues operations "prime_eval_stack_normalize_atom_frame_new".toList
      [.ptr input.space, .ptr input.arena, .ptr input.atom, .i32 input.fuel,
        .ptr input.environment, .u64 input.evaluator, .ptr input.target] =
      (NormalizeAtomConstructor.constructorOperations operations.constructor
        operations.constructorLayout input >>= frameReply) := by
  change (NormalizeAtomConstructor.interpretedConstructor operations.constructor
    operations.constructorLayout input >>= frameReply) = _
  rw [NormalizeAtomConstructor.original_constructor_executes_declared_operations]

theorem bind_callback_keeps_all_five_source_operands (operations : Operations)
    (space arena atom target : Option Ptr) (fuel : Int32) :
    effects operations "metta_eval_bind".toList
      [.ptr space, .ptr arena, .ptr atom, .i32 fuel, .ptr target] =
      operations.bind space arena atom fuel target := rfl

theorem call_callback_keeps_all_nine_source_operands (operations : Operations)
    (space arena atom etype seed target : Option Ptr) (fuel strictIndex : Int32)
    (preserve : Bool) :
    effects operations "metta_call_impl".toList
      [.ptr space, .ptr arena, .ptr atom, .ptr etype, .i32 fuel, .bool preserve,
        .ptr seed, .i32 strictIndex, .ptr target] =
      operations.call space arena atom etype fuel preserve seed strictIndex target := rfl

theorem need_entry_keeps_the_actual_environment_address (operations : Operations)
    (environment : Ptr) :
    (needRecord operations).invoke [.ptr (some environment)] =
      operations.needEnter environment := rfl

theorem authority_cleanup_keeps_the_actual_guard_address (operations : Operations)
    (layout : RunLayout) (guard : Ptr) (flow : ReadBlock.Flow Context) :
    cleanup operations layout "prime_eval_authority_leave".toList guard flow =
      Authority.leave layout.authority guard := rfl

theorem need_cleanup_keeps_the_actual_guard_address (operations : Operations)
    (layout : RunLayout) (guard : Ptr) (flow : ReadBlock.Flow Context) :
    cleanup operations layout "prime_need_active_leave".toList guard flow =
      operations.needLeave guard := rfl

theorem count_alias_keeps_wide_length (operations : Operations) (layout : RunLayout) (length : UInt64) :
    StatementBlock.ObjectBindings.scalarInitialValue (profile operations layout)
      (ctype "CettaCount") (.u64 length) = pure (.u64 length) := rfl

theorem count_alias_widens_null_target_zero (operations : Operations) (layout : RunLayout) :
    StatementBlock.ObjectBindings.scalarInitialValue (profile operations layout)
      (ctype "CettaCount") (.u32 0) = pure (.u64 0) := rfl

theorem original_runner_instantiates_common_services (operations : Operations) (layout : RunLayout)
    (loopFuel fuel : Nat) :
    fromOriginal (services operations layout) (fun _ => none) loopFuel fuel initialContext =
      StatementBlock.executeScopedWith (services operations layout) (fun _ => none)
        loopFuel fuel initialContext runSyntax.body :=
  original_source_executes_retained_body _ _ _ _ _

namespace Controls

/-- Omitting the writable place does not silently reuse the rvalue location. -/
theorem omitted_global_place_remains_unresolved (operations : Operations) (layout : RunLayout)
    (context : Context) (outside : context "g_prime_need_evaluator_id".toList = none) :
    StatementBlock.ObjectBindings.place
      { profile operations layout with outsidePlaces := fun _ => none }
      (fun _ => none) context (.identifier "g_prime_need_evaluator_id".toList) =
        CProg.undefined := by
  simp only [StatementBlock.ObjectBindings.place, placeWithNames.eq_def,
    StatementBlock.ObjectBindings.objects, StatementBlock.ObjectBindings.places,
    outside, Option.bind_some]
  rfl

/-- A declared scalar cannot take the place of a same-spelled global object. -/
theorem declared_local_shields_global_place (operations : Operations) (layout : RunLayout)
    (context : Context) (type : CType) (value : Option CVal)
    (bound : context "g_prime_need_evaluator_id".toList = some (.scalar type value)) :
    StatementBlock.ObjectBindings.place (profile operations layout) (fun _ => none) context
      (.identifier "g_prime_need_evaluator_id".toList) = CProg.undefined := by
  simp only [StatementBlock.ObjectBindings.place, placeWithNames.eq_def,
    StatementBlock.ObjectBindings.objects, StatementBlock.ObjectBindings.places,
    bound, Option.bind_some]
  rfl

/-- Uninitialized local storage also shields the global's rvalue reader. -/
theorem uninitialized_local_shields_global_read (operations : Operations) (layout : RunLayout)
    (context : Context) (type : CType)
    (bound : context "g_prime_need_evaluator_id".toList = some (.scalar type none)) :
    StatementBlock.ObjectBindings.read (profile operations layout) (fun _ => none) context
      (.identifier "g_prime_need_evaluator_id".toList) = CProg.undefined :=
  StatementBlock.ObjectBindings.local_uninitialized_scalar_shields_outer _ _ _ _ _ bound

theorem missing_bind_operand_is_not_a_void_success (operations : Operations) :
    effects operations "metta_eval_bind".toList [] = CProg.undefined := rfl

theorem pointer_in_place_of_call_boolean_is_not_reinterpreted (operations : Operations)
    (space arena atom etype seed target : Option Ptr) (fuel strictIndex : Int32) :
    effects operations "metta_call_impl".toList
      [.ptr space, .ptr arena, .ptr atom, .ptr etype, .i32 fuel, .ptr none,
        .ptr seed, .i32 strictIndex, .ptr target] = CProg.undefined := rfl

theorem null_need_environment_is_not_an_initialized_record (operations : Operations) :
    (needRecord operations).invoke [.ptr none] = CProg.undefined := rfl

theorem exhausted_constructor_is_not_a_frame : frameReply .exhausted = CProg.undefined := rfl

theorem returned_null_frame_remains_normal_refusal (environment : ReadExpressions.Environment) :
    frameReply (.finished (.returned environment (some (.ptr none)))) = pure (.ptr none) := rfl

theorem false_enabled_assertion_remains_undefined (operations : Operations) :
    effects operations "assert".toList [.bool false] = CProg.undefined := rfl

theorem disabled_assertion_omits_an_unavailable_operand (operations : Operations) (layout : RunLayout)
    (context : Context) (disabled : operations.assertions = false) :
    (services operations layout).effect (fun _ => none) context
      (.call "assert".toList [.call "unavailable_external_effect".toList []]) = pure () := by
  change EffectStatements.withObjectMacros (profile operations layout) (effects operations)
    (omittedMacros operations) (fun _ => none) context
    (.call "assert".toList [.call "unavailable_external_effect".toList []]) = _
  apply EffectStatements.omitted_macro_does_not_evaluate_arguments _ _ _ _ _ _ _ 1
  · simp only [omittedMacros, disabled]
    rfl
  · rfl

end Controls

end Mettapedia.Languages.MeTTa.CeTTaNativeCost.RunTaskSource.Execution

namespace Mettapedia.Languages.MeTTa.CeTTaNativeCost.RunTaskSource.Execution.Tree

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Machines.CMemory
open ReadExpressions
open StatementBlock.ObjectBindings (Context)

private def runType (name : String) (depth : Nat := 0) : CType := ⟨name.toList, depth⟩

private def bindScalar (context : Context) (name : String) (type : CType) (value : CVal) : Context :=
  Function.update context name.toList (some (.scalar type (some value)))

private def bindObject (context : Context) (name : String) (type : CType) (address : Ptr) : Context :=
  Function.update context name.toList (some (.object type address))

private def driverRead (layout : RunLayout) (driver : Option Ptr) (name : String) : CProg CVal CVal :=
  field (driverFields layout) (.ptr driver) name.toList

private def driverPlace (layout : RunLayout) (driver : Option Ptr) (name : String) : CProg CVal Ptr :=
  fieldAddress (driverFields layout) (.ptr driver) name.toList

private def driverStore (layout : RunLayout) (driver : Option Ptr) (name : String) (value : CVal) :
    CProg CVal Unit := do
  let destination ← driverPlace layout driver name
  CProg.store destination value

private def taskRead (layout : RunLayout) (task : Ptr) (name : String) : CProg CVal CVal :=
  field (TaskAdmission.taskFields layout.toTaskLayout) (.ptr (some task)) name.toList

/-- A disabled assertion omits its complete operand tree. Enabled assertions
retain pointer validity and both subsequent field reads in authored order.
False assertions are outside the admitted normally returning fragment. -/
def assertions (operations : Operations) (layout : RunLayout) (driver : Option Ptr) : CProg CVal Unit := do
  if operations.assertions then
    let nullDriver ← CProg.ptrEq driver none
    if nullDriver then CProg.undefined else pure ()
    let ready ← driverRead layout driver "task_ready"
    let ready ← truth ready
    if ready then pure () else CProg.undefined
    let running ← driverRead layout driver "running_task"
    let running ← truth running
    if running then CProg.undefined else pure ()
  else pure ()

/-- BIND retains its statistics, authority-visible flag writes, each argument
load and the actual void callback. Its break belongs to the switch. -/
def bindOperations (operations : Operations) (layout : RunLayout)
    (context : Context) (driver : Option Ptr) (task : Ptr) : CProg CVal (ReadBlock.Result Context) := do
  operations.statistics 262
  driverStore layout driver "running_bind_task" (.bool true)
  let space ← CProg.loadPtr (task + layout.taskOffset "space".toList)
  let arena ← CProg.loadPtr (task + layout.taskOffset "arena".toList)
  let atom ← CProg.loadPtr (task + layout.taskOffset "atom".toList)
  let fuel ← CProg.loadI32 (task + layout.taskOffset "fuel".toList)
  let target ← CProg.loadPtr (task + layout.taskOffset "target".toList)
  operations.bind space arena atom fuel target
  driverStore layout driver "running_bind_task" (.bool false)
  pure (.finished (.broken context))

/-- CALL preserves every operand, including the seed flag's selected address.
No environment snapshot replaces the source's borrowed pointer identity. -/
def callOperations (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr) : CProg CVal (ReadBlock.Result Context) := do
  operations.statistics 263
  let space ← CProg.loadPtr (task + layout.taskOffset "space".toList)
  let arena ← CProg.loadPtr (task + layout.taskOffset "arena".toList)
  let atom ← CProg.loadPtr (task + layout.taskOffset "atom".toList)
  let etype ← CProg.loadPtr (task + layout.taskOffset "etype".toList)
  let fuel ← CProg.loadI32 (task + layout.taskOffset "fuel".toList)
  let preserve ← CProg.loadBool (task + layout.taskOffset "preserve_bindings".toList)
  let seedInitialized ← CProg.loadBool (task + layout.taskOffset "seed_env_initialized".toList)
  let seed := if seedInitialized then some (task + layout.taskOffset "seed_env".toList) else none
  let strictIndex ← CProg.loadI32 (task + layout.taskOffset "strict_ready_argument".toList)
  let target ← CProg.loadPtr (task + layout.taskOffset "target".toList)
  operations.call space arena atom etype fuel preserve seed strictIndex target
  pure (.finished (.broken context))

/-- Normalization's source effects retain all operands, constructor flow,
nullable conversion and the chosen push-or-capacity operation. -/
def normalizeEffects (operations : Operations) (layout : RunLayout) (task : Ptr) : CProg CVal Unit := do
  let space ← CProg.loadPtr (task + layout.taskOffset "space".toList)
  let arena ← CProg.loadPtr (task + layout.taskOffset "arena".toList)
  let atom ← CProg.loadPtr (task + layout.taskOffset "atom".toList)
  let fuel ← CProg.loadI32 (task + layout.taskOffset "fuel".toList)
  let evaluator ← CProg.loadU64 (task + layout.taskOffset "evaluator_id".toList)
  let result ← NormalizeAtomConstructor.constructorOperations operations.constructor
    operations.constructorLayout
    ⟨space, arena, atom, some (task + layout.taskOffset "dynamic_env".toList),
      (← CProg.loadPtr (task + layout.taskOffset "target".toList)), fuel, evaluator⟩
  let actual ← frameReply result
  let frame ← pointer actual
  let present ← truth (.ptr frame)
  if present then match frame with
    | some frame => operations.push frame
    | none => CProg.undefined
  else operations.markIncomplete 4

/-- NORMALIZE retains its statistics and the switch-owned break around the
complete normalization effect tree. -/
def normalizeOperations (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr) : CProg CVal (ReadBlock.Result Context) := do
  operations.statistics 264
  normalizeEffects operations layout task
  pure (.finished (.broken context))

/-- The target is read twice when the condition is true, as authored: once
for presence and again for its field owner. Numeric comparison retains the
complete wide value and conversion laws of the common scalar interpreter. -/
def publicationGrowth (layout : RunLayout) (task : Ptr) (published : UInt64) : CProg CVal Bool := do
  let target ← taskRead layout task "target"
  let present ← truth target
  if present then do
    let owner ← taskRead layout task "target"
    let length ← field (fun name => if name = "len".toList then
      some ⟨layout.outcomeLength, .word64⟩ else none) owner "len".toList
    let greater ← binary .gt length (.u64 published)
    truth greater
  else pure false

/-- Retirement follows publication and precedes the final driver flag write.
The enclosing Need and authority cleanups occur later, while their own guard
records remain live. Borrowed-view lifetime safety is a separate obligation. -/
def completion (operations : Operations) (layout : RunLayout) (context : Context)
    (driver : Option Ptr) (task : Ptr) (previous published : UInt64) :
    CProg CVal (ReadBlock.Result Context) := do
  CProg.store layout.evaluatorId (.u64 previous)
  driverStore layout driver "active_task" (.ptr none)
  let grew ← publicationGrowth layout task published
  if grew then do
    let target ← CProg.loadPtr (task + layout.taskOffset "target".toList)
    operations.streamNote target
  else pure ()
  operations.releaseTask task
  driverStore layout driver "running_task" (.bool false)
  pure (.finished (.next context))

/-- Static enum dispatch retains unknown-kind fallthrough and the owning
switch's break. Ordinary execution still uses the same source service model. -/
def dispatch (operations : Operations) (layout : RunLayout) (context : Context)
    (driver : Option Ptr) (task : Ptr) : CProg CVal (ReadBlock.Result Context) := do
  let kind ← CProg.loadU32 (task + layout.taskOffset "kind".toList)
  if kind = 0 then bindOperations operations layout context driver task
  else if kind = 1 then callOperations operations layout context task
  else if kind = 2 then normalizeOperations operations layout context task
  else pure (.finished (.next context))

/-- Evaluator installation and selected dispatch retain the full completion
flow, without performing either enclosing lexical restoration. -/
def installedEvaluatorBody (operations : Operations) (layout : RunLayout) (context : Context)
    (driver : Option Ptr) (task : Ptr) (previous published : UInt64) :
    CProg CVal (ReadBlock.Result Context) := do
  let evaluator ← CProg.loadU64 (task + layout.taskOffset "evaluator_id".toList)
  CProg.store layout.evaluatorId (.u64 evaluator)
  let selected ← dispatch operations layout context driver task
  StatementBlock.resumeSwitch
    (fun actual => completion operations layout actual driver task previous published) selected

/-- The saved global word remains local until every dispatch and completion
operation has returned its complete flow. -/
def evaluatorBody (operations : Operations) (layout : RunLayout) (context : Context)
    (driver : Option Ptr) (task : Ptr) (published : UInt64) : CProg CVal (ReadBlock.Result Context) := do
  let previous ← CProg.loadU64 layout.evaluatorId
  let finished ← installedEvaluatorBody operations layout
    (bindScalar context "previous_evaluator_id" (runType "uint64_t") (.u64 previous))
    driver task previous published
  pure (StatementBlock.ObjectBindings.restore "previous_evaluator_id".toList
    (context "previous_evaluator_id".toList) finished)

/-- The Need region keeps the complete by-value result, exact extent check,
evaluator installation and complete scoped continuation. A returned callback
flow reaches cleanup before automatic-region exit and lexical restoration. -/
def needBody (operations : Operations) (layout : RunLayout) (context : Context)
    (driver : Option Ptr) (task : Ptr) (published : UInt64) : CProg CVal (ReadBlock.Result Context) := do
  let result ← StatementBlock.AutomaticRegion.withCleanup operations.region
    (fun _ address _ _ => operations.needLeave address)
    "need_guard".toList layout.needCells fun guard => do
      let withGuard := bindObject context "need_guard" (runType "PrimeNeedActiveGuard") guard
      let fields ← operations.needEnter (task + layout.taskOffset "dynamic_env".toList)
      if fields.length = layout.needCells then CProg.initializeCells guard fields else CProg.undefined
      evaluatorBody operations layout withGuard driver task published
  pure (StatementBlock.ObjectBindings.restore "need_guard".toList (context "need_guard".toList) result)

private def publicationStart (layout : RunLayout) (task : Ptr) : CProg CVal UInt64 := do
  let target ← CProg.loadPtr (task + layout.taskOffset "target".toList)
  let absent ← CProg.ptrEq target none
  if !absent then do
    let owner ← CProg.loadPtr (task + layout.taskOffset "target".toList)
    match owner with
    | some owner => CProg.loadU64 (owner + layout.outcomeLength)
    | none => CProg.undefined
  else pure 0


/-- Initial publication count is read before Need entry. The scalar binding
remains live throughout that complete inner flow and restores afterward. -/
def publishedBody (operations : Operations) (layout : RunLayout) (context : Context)
    (driver : Option Ptr) (task : Ptr) : CProg CVal (ReadBlock.Result Context) := do
  let published ← publicationStart layout task
  let finished ← needBody operations layout
    (bindScalar context "published_before" (runType "CettaCount") (.u64 published))
    driver task published
  pure (StatementBlock.ObjectBindings.restore "published_before".toList
    (context "published_before".toList) finished)

/-- The queued Task is cleared before its copied automatic Task is exposed
as active. These writes precede the initial publication count and Need scope. -/
def prepareBody (operations : Operations) (layout : RunLayout) (context : Context)
    (driver : Option Ptr) (task : Ptr) : CProg CVal (ReadBlock.Result Context) := do
  let queuedTask ← driverPlace layout driver "task"
  operations.zeroTask queuedTask (UInt64.ofNat layout.taskBytes)
  driverStore layout driver "task_ready" (.bool false)
  driverStore layout driver "active_task" (.ptr (some task))
  driverStore layout driver "running_task" (.bool true)
  publishedBody operations layout context driver task

/-- Ordinary task entry keeps partial-overlay semantics in the supplied Need
service. It does not replace that service with complete captured installation. -/
def authorityBody (operations : Operations) (layout : RunLayout) (context : Context)
    (driver : Option Ptr) (task : Ptr) : CProg CVal (ReadBlock.Result Context) := do
  let result ← StatementBlock.AutomaticRegion.withCleanup operations.region
    (fun _ address _ _ => Authority.leave layout.authority address)
    "authority".toList 2 fun guard => do
      let withAuthority := bindObject context "authority" (runType "PrimeEvalAuthorityGuard") guard
      let incoming ← CProg.loadBool (task + layout.taskOffset "pure_authority".toList)
      let fields ← Authority.enter layout.authority incoming
      if fields.length = 2 then CProg.initializeCells guard fields else CProg.undefined
      prepareBody operations layout withAuthority driver task
  pure (StatementBlock.ObjectBindings.restore "authority".toList (context "authority".toList) result)

/-- The source's full Task copy precedes authority entry. Lexical restoration
runs only after the automatic region has inspected the entire inner flow. -/
def taskBody (operations : Operations) (layout : RunLayout) (context : Context)
    (driver : Option Ptr) : CProg CVal (ReadBlock.Result Context) := do
  let result ← operations.region "task".toList layout.taskCells fun task => do
    let original ← driverPlace layout driver "task"
    CProg.copyCells original task layout.taskCells
    authorityBody operations layout
      (bindObject context "task" (runType "PrimeEvalStackTask") task) driver task
  pure (StatementBlock.ObjectBindings.restore "task".toList (context "task".toList) result)

/-- The whole independent runner tree snapshots the driver, checks admission,
copies all Task cells into its own automatic region and executes the actual
nested guards. It never calls the statement interpreter or defines itself as
its readout. Every region receives the complete unprojected scoped flow. -/
def runOperations (operations : Operations) (layout : RunLayout) : CProg CVal (ReadBlock.Result Context) := do
  let driver ← CProg.loadPtr layout.currentDriver
  let withDriver := bindScalar initialContext "driver" (runType "PrimeEvalStackDriver" 1) (.ptr driver)
  let result ← do
    assertions operations layout driver
    taskBody operations layout withDriver driver
  pure (StatementBlock.ObjectBindings.restore "driver".toList (initialContext "driver".toList) result)


private def emptyLayout : Layout := fun _ => none

private def runRead (operations : Operations) (layout : RunLayout) (context : Context)
    (operand : CExpr) : CProg CVal CVal :=
  StatementBlock.ObjectBindings.read (profile operations layout) emptyLayout context operand

private theorem local_read (operations : Operations) (layout : RunLayout) (context : Context)
    (name : Name) (type : CType) (value : CVal)
    (known : context name = some (.scalar type (some value))) :
    runRead operations layout context (.identifier name) = pure value :=
  StatementBlock.ObjectBindings.initialized_local_keeps_its_value _ _ _ _ _ _ known

private theorem driver_field_read (operations : Operations) (layout : RunLayout)
    (context : Context) (driver : Option Ptr) (name : String)
    (known : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver)))) :
    runRead operations layout context (TaskAdmission.driverField name) = driverRead layout driver name := by
  change StatementBlock.ObjectBindings.read (profile operations layout) emptyLayout context
    (.field (.identifier "driver".toList) name.toList true) = _
  rw [StatementBlock.ObjectBindings.local_pointer_field_keeps_reference_and_inventory
    (profile operations layout) emptyLayout context (recordLayouts layout)
    "driver".toList name.toList "PrimeEvalStackDriver".toList 0 driver (by rfl) known]
  rfl

private theorem task_field_read (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr) (name : String)
    (known : context "task".toList = some (.object (runType "PrimeEvalStackTask") task)) :
    runRead operations layout context (TaskAdmission.taskField name) = taskRead layout task name := by
  change StatementBlock.ObjectBindings.read (profile operations layout) emptyLayout context
    (.field (.identifier "task".toList) name.toList false) = _
  rw [StatementBlock.ObjectBindings.local_object_field_keeps_place_and_inventory
    (profile operations layout) emptyLayout context (recordLayouts layout)
    "task".toList name.toList (runType "PrimeEvalStackTask") task (by rfl) known]
  rfl

private theorem driver_field_place (operations : Operations) (layout : RunLayout)
    (context : Context) (driver : Option Ptr) (name : String)
    (known : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver)))) :
    StatementBlock.ObjectBindings.place (profile operations layout) emptyLayout context
      (TaskAdmission.driverField name) = driverPlace layout driver name := by
  change StatementBlock.ObjectBindings.place (profile operations layout) emptyLayout context
    (.field (.identifier "driver".toList) name.toList true) = _
  rw [StatementBlock.ObjectBindings.local_pointer_field_keeps_address
    (profile operations layout) emptyLayout context (recordLayouts layout)
    "driver".toList name.toList "PrimeEvalStackDriver".toList 0 driver (by rfl) known]
  rfl

private theorem task_field_address (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr) (name : String) (kind : FieldKind)
    (known : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (selected : TaskAdmission.taskFields layout.toTaskLayout name.toList =
      some ⟨layout.taskOffset name.toList, kind⟩) :
    runRead operations layout context (.unary .address (TaskAdmission.taskField name)) =
      pure (.ptr (some (task + layout.taskOffset name.toList))) := by
  change (StatementBlock.ObjectBindings.place (profile operations layout) emptyLayout context
    (.field (.identifier "task".toList) name.toList false) >>= fun address =>
      pure (CVal.ptr (some address))) = _
  rw [StatementBlock.ObjectBindings.local_object_field_keeps_address
    (profile operations layout) emptyLayout context (recordLayouts layout)
    "task".toList name.toList (runType "PrimeEvalStackTask") task
    (layout.taskOffset name.toList) kind (by rfl) known]
  · simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  · exact selected

private theorem negated_read (operations : Operations) (layout : RunLayout) (context : Context)
    (operand : CExpr) :
    runRead operations layout context (.unary .not operand) =
      (runRead operations layout context operand >>= fun value => truth value >>= fun selected =>
        pure (.bool (!selected))) := rfl

/-- A runner effect keeps macro omission distinct from actual argument
execution. This reduction applies only to non-assert call names. -/
private theorem effect_keeps_arguments (operations : Operations) (layout : RunLayout)
    (context : Context) (name : Name) (arguments : List CExpr)
    (notAssert : name ≠ "assert".toList) :
    (services operations layout).effect emptyLayout context (.call name arguments) =
      (argumentsWithNames
        (localOrLocated (StatementBlock.ObjectBindings.values context)
          (StatementBlock.ObjectBindings.declared context) (profile operations layout).locations)
        (profile operations layout).values emptyLayout arguments
        (StatementBlock.ObjectBindings.objects (profile operations layout) context) >>=
          effects operations name) := by
  change EffectStatements.withObjectMacros (profile operations layout) (effects operations)
    (omittedMacros operations) emptyLayout context (.call name arguments) = _
  have omitted : omittedMacros operations name = none := by
    change name ≠ ['a', 's', 's', 'e', 'r', 't'] at notAssert
    simp [omittedMacros, notAssert]
  exact EffectStatements.enabled_call_keeps_the_whole_argument_evaluation
    (profile operations layout) (effects operations) (omittedMacros operations)
    emptyLayout context name arguments omitted


private theorem statistics_effect (operations : Operations) (layout : RunLayout)
    (context : Context) (counterName : String) (counter : Int32)
    (known : context counterName.toList = some (.scalar (runType "int") (some (.i32 counter)))) :
    (services operations layout).effect emptyLayout context
      (.call "cetta_runtime_stats_inc".toList [.identifier counterName.toList]) =
        operations.statistics counter := by
  rw [effect_keeps_arguments operations layout context "cetta_runtime_stats_inc".toList
    [.identifier counterName.toList] (by decide)]
  simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  change (runRead operations layout context (.identifier counterName.toList) >>= fun value =>
    effects operations "cetta_runtime_stats_inc".toList [value]) = _
  rw [local_read operations layout context counterName.toList _ _ known]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rfl

private theorem driver_assignment (operations : Operations) (layout : RunLayout)
    (context : Context) (driver : Option Ptr) (name : String) (type : CType)
    (operand : CExpr) (value : CVal)
    (known : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (typed : fieldTypes (runType "PrimeEvalStackDriver") name.toList = some type)
    (notRecord : (profile operations layout).cellExtent type = none)
    (descriptor : driverFields layout name.toList =
      some ⟨layout.driverOffset name.toList, valueKind value⟩)
    (actual : runRead operations layout context operand = pure value) :
    (services operations layout).assignment emptyLayout context
      (.assign (TaskAdmission.driverField name) operand) =
      (driverStore layout driver name value >>= fun _ => pure context) := by
  have targetType : ScalarBytes.typeOf?
      (StatementBlock.ObjectBindings.types context (profile operations layout).outsideTypes)
      (TaskAdmission.driverField name) (profile operations layout).fieldTypes = some type := by
    simp only [TaskAdmission.driverField, TaskAdmission.ident, ScalarBytes.typeOf?,
      StatementBlock.ObjectBindings.types, known, bind, Option.bind_some, runType, ↓reduceIte]
    exact typed
  change StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout context
    (.assign (TaskAdmission.driverField name) operand) = _
  rw [StatementBlock.ObjectBindings.assignment, targetType]
  simp only [resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, notRecord]
  change (runRead operations layout context operand >>= fun value =>
    StatementBlock.ObjectBindings.writeValue (profile operations layout) emptyLayout context
      (TaskAdmission.driverField name) value) = _
  rw [actual]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  simp only [TaskAdmission.driverField]
  rw [StatementBlock.ObjectBindings.scalar_field_write_keeps_place_and_value
    (profile operations layout) emptyLayout context (TaskAdmission.ident "driver") name.toList true
    value (layout.driverOffset name.toList)]
  · change (StatementBlock.ObjectBindings.place (profile operations layout) emptyLayout context
      (TaskAdmission.driverField name) >>= fun address => CProg.store address value >>= fun _ => pure context) = _
    rw [driver_field_place operations layout context driver name known]
    simp only [driverStore, Prog.bind_eq, Prog.bind_assoc]
    rfl
  · simp only [TaskAdmission.ident]
    rw [StatementBlock.ObjectBindings.local_pointer_keeps_field_inventory
      (profile operations layout) emptyLayout context (recordLayouts layout)
      "driver".toList "PrimeEvalStackDriver".toList 0 driver (by rfl) known]
    exact descriptor

private theorem bind_effect_keeps_five_loads (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr)
    (known : context "task".toList = some (.object (runType "PrimeEvalStackTask") task)) :
    (services operations layout).effect emptyLayout context
      (.call "metta_eval_bind".toList
        [TaskAdmission.taskField "space", TaskAdmission.taskField "arena", TaskAdmission.taskField "atom",
          TaskAdmission.taskField "fuel", TaskAdmission.taskField "target"]) =
      (do
        let space ← CProg.loadPtr (task + layout.taskOffset "space".toList)
        let arena ← CProg.loadPtr (task + layout.taskOffset "arena".toList)
        let atom ← CProg.loadPtr (task + layout.taskOffset "atom".toList)
        let fuel ← CProg.loadI32 (task + layout.taskOffset "fuel".toList)
        let target ← CProg.loadPtr (task + layout.taskOffset "target".toList)
        operations.bind space arena atom fuel target) := by
  rw [effect_keeps_arguments operations layout context "metta_eval_bind".toList _ (by decide)]
  simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  change (runRead operations layout context (TaskAdmission.taskField "space") >>= fun space =>
    runRead operations layout context (TaskAdmission.taskField "arena") >>= fun arena =>
      runRead operations layout context (TaskAdmission.taskField "atom") >>= fun atom =>
        runRead operations layout context (TaskAdmission.taskField "fuel") >>= fun fuel =>
          runRead operations layout context (TaskAdmission.taskField "target") >>= fun target =>
            effects operations "metta_eval_bind".toList [space, arena, atom, fuel, target]) = _
  rw [task_field_read operations layout context task "space" known,
    task_field_read operations layout context task "arena" known,
    task_field_read operations layout context task "atom" known,
    task_field_read operations layout context task "fuel" known,
    task_field_read operations layout context task "target" known]
  unfold taskRead
  rw [pointer_field_uses_actual_offset _ task "space".toList _ (by rfl),
    pointer_field_uses_actual_offset _ task "arena".toList _ (by rfl),
    pointer_field_uses_actual_offset _ task "atom".toList _ (by rfl),
    signed_field_uses_actual_offset _ task "fuel".toList _ (by rfl),
    pointer_field_uses_actual_offset _ task "target".toList _ (by rfl)]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc,
    bind_callback_keeps_all_five_source_operands]

/-- The BIND arm compares its actual source statements with an independent
memory/callback tree. It retains both flag writes, all five loads and the
switch-owned break, rather than merely comparing the printed result. -/
theorem bind_arm_is_complete_operation_tree (operations : Operations) (layout : RunLayout)
    (context : Context) (driver : Option Ptr) (task : Ptr) (fuel : Nat)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (knownCounter : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList =
      some (.scalar (runType "int") (some (.i32 262)))) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 5)
      context bindArm = bindOperations operations layout context driver task := by
  unfold bindArm
  rw [StatementBlock.executeScopedWith.eq_def]
  change ((services operations layout).effect emptyLayout context
    (.call "cetta_runtime_stats_inc".toList
      [TaskAdmission.ident "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND"]) >>=
        fun _ => StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 4)
          context _) = _
  simp only [TaskAdmission.ident]
  rw [statistics_effect operations layout context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND" 262 knownCounter]
  unfold bindOperations
  simp only [Prog.bind_eq]
  congr 1
  funext ignored
  rw [StatementBlock.scoped_assignment_keeps_continuation]
  rw [driver_assignment operations layout context driver "running_bind_task" (runType "bool")
    (.bool true) (.bool true) knownDriver (by rfl) (by rfl) (by rfl) (by rfl)]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext ignoredFlag
  rw [StatementBlock.scoped_effect_keeps_continuation]
  rw [bind_effect_keeps_five_loads operations layout context task knownTask]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext space
  congr 1
  funext arena
  congr 1
  funext atom
  congr 1
  funext inputFuel
  congr 1
  funext target
  congr 1
  funext ignored
  rw [StatementBlock.scoped_assignment_keeps_continuation]
  rw [driver_assignment operations layout context driver "running_bind_task" (runType "bool")
    (.bool false) (.bool false) knownDriver (by rfl) (by rfl) (by rfl) (by rfl)]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl


private theorem call_seed_keeps_selected_address (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr)
    (known : context "task".toList = some (.object (runType "PrimeEvalStackTask") task)) :
    runRead operations layout context
      (.conditional (TaskAdmission.taskField "seed_env_initialized")
        (.unary .address (TaskAdmission.taskField "seed_env")) .null) =
      (CProg.loadBool (task + layout.taskOffset "seed_env_initialized".toList) >>= fun initialized =>
        pure (.ptr (if initialized then some (task + layout.taskOffset "seed_env".toList) else none))) := by
  change (runRead operations layout context (TaskAdmission.taskField "seed_env_initialized") >>=
    fun value => truth value >>= fun initialized =>
      (if initialized then runRead operations layout context
        (.unary .address (TaskAdmission.taskField "seed_env"))
       else runRead operations layout context .null)) = _
  rw [task_field_read operations layout context task "seed_env_initialized" known]
  unfold taskRead
  rw [boolean_field_uses_actual_offset _ task "seed_env_initialized".toList _ (by rfl)]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc, truth]
  congr 1
  funext initialized
  cases initialized
  · rfl
  · simp only [↓reduceIte]
    exact task_field_address operations layout context task "seed_env" .embedded known (by rfl)

/-- CALL argument evaluation retains all nine operands and its selected
borrowed seed address. The flag and address are neither reordered nor copied
into an unrelated environment snapshot. -/
private theorem call_effect_keeps_nine_loads (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr)
    (known : context "task".toList = some (.object (runType "PrimeEvalStackTask") task)) :
    (services operations layout).effect emptyLayout context
      (.call "metta_call_impl".toList
        [TaskAdmission.taskField "space", TaskAdmission.taskField "arena", TaskAdmission.taskField "atom",
          TaskAdmission.taskField "etype", TaskAdmission.taskField "fuel",
          TaskAdmission.taskField "preserve_bindings",
          .conditional (TaskAdmission.taskField "seed_env_initialized")
            (.unary .address (TaskAdmission.taskField "seed_env")) .null,
          TaskAdmission.taskField "strict_ready_argument", TaskAdmission.taskField "target"]) =
      (do
        let space ← CProg.loadPtr (task + layout.taskOffset "space".toList)
        let arena ← CProg.loadPtr (task + layout.taskOffset "arena".toList)
        let atom ← CProg.loadPtr (task + layout.taskOffset "atom".toList)
        let etype ← CProg.loadPtr (task + layout.taskOffset "etype".toList)
        let fuel ← CProg.loadI32 (task + layout.taskOffset "fuel".toList)
        let preserve ← CProg.loadBool (task + layout.taskOffset "preserve_bindings".toList)
        let initialized ← CProg.loadBool (task + layout.taskOffset "seed_env_initialized".toList)
        let seed := if initialized then some (task + layout.taskOffset "seed_env".toList) else none
        let strictIndex ← CProg.loadI32 (task + layout.taskOffset "strict_ready_argument".toList)
        let target ← CProg.loadPtr (task + layout.taskOffset "target".toList)
        operations.call space arena atom etype fuel preserve seed strictIndex target) := by
  rw [effect_keeps_arguments operations layout context "metta_call_impl".toList _ (by decide)]
  simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  change (runRead operations layout context (TaskAdmission.taskField "space") >>= fun space =>
    runRead operations layout context (TaskAdmission.taskField "arena") >>= fun arena =>
      runRead operations layout context (TaskAdmission.taskField "atom") >>= fun atom =>
        runRead operations layout context (TaskAdmission.taskField "etype") >>= fun etype =>
          runRead operations layout context (TaskAdmission.taskField "fuel") >>= fun fuel =>
            runRead operations layout context (TaskAdmission.taskField "preserve_bindings") >>= fun preserve =>
              runRead operations layout context
                (.conditional (TaskAdmission.taskField "seed_env_initialized")
                  (.unary .address (TaskAdmission.taskField "seed_env")) .null) >>= fun seed =>
                runRead operations layout context (TaskAdmission.taskField "strict_ready_argument") >>= fun strictIndex =>
                  runRead operations layout context (TaskAdmission.taskField "target") >>= fun target =>
                    effects operations "metta_call_impl".toList
                      [space, arena, atom, etype, fuel, preserve, seed, strictIndex, target]) = _
  rw [task_field_read operations layout context task "space" known,
    task_field_read operations layout context task "arena" known,
    task_field_read operations layout context task "atom" known,
    task_field_read operations layout context task "etype" known,
    task_field_read operations layout context task "fuel" known,
    task_field_read operations layout context task "preserve_bindings" known,
    call_seed_keeps_selected_address operations layout context task known,
    task_field_read operations layout context task "strict_ready_argument" known,
    task_field_read operations layout context task "target" known]
  unfold taskRead
  rw [pointer_field_uses_actual_offset _ task "space".toList _ (by rfl),
    pointer_field_uses_actual_offset _ task "arena".toList _ (by rfl),
    pointer_field_uses_actual_offset _ task "atom".toList _ (by rfl),
    pointer_field_uses_actual_offset _ task "etype".toList _ (by rfl),
    signed_field_uses_actual_offset _ task "fuel".toList _ (by rfl),
    boolean_field_uses_actual_offset _ task "preserve_bindings".toList _ (by rfl),
    signed_field_uses_actual_offset _ task "strict_ready_argument".toList _ (by rfl),
    pointer_field_uses_actual_offset _ task "target".toList _ (by rfl)]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc,
    call_callback_keeps_all_nine_source_operands]

/-- The CALL arm compares the real source statement list with its complete
independent memory/callback tree, including the owning switch break. -/
theorem call_arm_is_complete_operation_tree (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr) (fuel : Nat)
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (knownCounter : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList =
      some (.scalar (runType "int") (some (.i32 263)))) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 3)
      context callArm = callOperations operations layout context task := by
  unfold callArm
  rw [StatementBlock.scoped_effect_keeps_continuation]
  simp only [TaskAdmission.ident]
  rw [statistics_effect operations layout context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL" 263 knownCounter]
  unfold callOperations
  simp only [Prog.bind_eq]
  congr 1
  funext ignored
  rw [StatementBlock.scoped_effect_keeps_continuation]
  rw [call_effect_keeps_nine_loads operations layout context task knownTask]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc]
  rfl


/-- NORMALIZE preserves the seven source operands in their admitted reader
order and invokes the independently compared constructor. The dynamic
environment remains the address of the copied Task's own embedded field. -/
private theorem normalize_read_keeps_complete_constructor (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr)
    (known : context "task".toList = some (.object (runType "PrimeEvalStackTask") task)) :
    runRead operations layout context
      (.call "prime_eval_stack_normalize_atom_frame_new".toList
        [TaskAdmission.taskField "space", TaskAdmission.taskField "arena", TaskAdmission.taskField "atom",
          TaskAdmission.taskField "fuel", .unary .address (TaskAdmission.taskField "dynamic_env"),
          TaskAdmission.taskField "evaluator_id", TaskAdmission.taskField "target"]) =
      (do
        let space ← CProg.loadPtr (task + layout.taskOffset "space".toList)
        let arena ← CProg.loadPtr (task + layout.taskOffset "arena".toList)
        let atom ← CProg.loadPtr (task + layout.taskOffset "atom".toList)
        let fuel ← CProg.loadI32 (task + layout.taskOffset "fuel".toList)
        let evaluator ← CProg.loadU64 (task + layout.taskOffset "evaluator_id".toList)
        let target ← CProg.loadPtr (task + layout.taskOffset "target".toList)
        let result ← NormalizeAtomConstructor.constructorOperations operations.constructor
          operations.constructorLayout
          ⟨space, arena, atom, some (task + layout.taskOffset "dynamic_env".toList), target, fuel, evaluator⟩
        frameReply result) := by
  change (argumentsWithNames
    (localOrLocated (StatementBlock.ObjectBindings.values context)
      (StatementBlock.ObjectBindings.declared context) (profile operations layout).locations)
    (profile operations layout).values emptyLayout _
    (StatementBlock.ObjectBindings.objects (profile operations layout) context) >>=
      constructorValues operations "prime_eval_stack_normalize_atom_frame_new".toList) = _
  simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  change (runRead operations layout context (TaskAdmission.taskField "space") >>= fun space =>
    runRead operations layout context (TaskAdmission.taskField "arena") >>= fun arena =>
      runRead operations layout context (TaskAdmission.taskField "atom") >>= fun atom =>
        runRead operations layout context (TaskAdmission.taskField "fuel") >>= fun fuel =>
          runRead operations layout context (.unary .address (TaskAdmission.taskField "dynamic_env")) >>= fun environment =>
            runRead operations layout context (TaskAdmission.taskField "evaluator_id") >>= fun evaluator =>
              runRead operations layout context (TaskAdmission.taskField "target") >>= fun target =>
                constructorValues operations "prime_eval_stack_normalize_atom_frame_new".toList
                  [space, arena, atom, fuel, environment, evaluator, target]) = _
  rw [task_field_read operations layout context task "space" known,
    task_field_read operations layout context task "arena" known,
    task_field_read operations layout context task "atom" known,
    task_field_read operations layout context task "fuel" known,
    task_field_address operations layout context task "dynamic_env" .embedded known (by rfl),
    task_field_read operations layout context task "evaluator_id" known,
    task_field_read operations layout context task "target" known]
  unfold taskRead
  rw [pointer_field_uses_actual_offset _ task "space".toList _ (by rfl),
    pointer_field_uses_actual_offset _ task "arena".toList _ (by rfl),
    pointer_field_uses_actual_offset _ task "atom".toList _ (by rfl),
    signed_field_uses_actual_offset _ task "fuel".toList _ (by rfl),
    word64_field_uses_actual_offset _ task "evaluator_id".toList _ (by rfl),
    pointer_field_uses_actual_offset _ task "target".toList _ (by rfl)]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  congr 1
  funext space
  congr 1
  funext arena
  congr 1
  funext atom
  congr 1
  funext fuel
  congr 1
  funext evaluator
  congr 1
  funext target
  exact constructor_call_keeps_complete_interpreted_callee operations
    ⟨space, arena, atom, some (task + layout.taskOffset "dynamic_env".toList), target, fuel, evaluator⟩


private theorem push_effect_keeps_nullable_reply (operations : Operations) (layout : RunLayout)
    (context : Context) (frame : Option Ptr)
    (known : context "frame".toList =
      some (.scalar (runType "PrimeEvalStackFrame" 1) (some (.ptr frame)))) :
    (services operations layout).effect emptyLayout context
      (.call "prime_eval_stack_push".toList [TaskAdmission.ident "frame"]) =
      (match frame with | some address => operations.push address | none => CProg.undefined) := by
  rw [effect_keeps_arguments operations layout context "prime_eval_stack_push".toList _ (by decide)]
  simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  change (runRead operations layout context (.identifier "frame".toList) >>= fun value =>
    effects operations "prime_eval_stack_push".toList [value]) = _
  rw [local_read operations layout context "frame".toList _ (.ptr frame) known]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  cases frame <;> rfl

private theorem capacity_effect_keeps_reason (operations : Operations) (layout : RunLayout)
    (context : Context)
    (known : context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4)))) :
    (services operations layout).effect emptyLayout context
      (.call "eval_mark_incomplete".toList [TaskAdmission.ident "CETTA_EVAL_INCOMPLETE_CAPACITY"]) =
      operations.markIncomplete 4 := by
  rw [effect_keeps_arguments operations layout context "eval_mark_incomplete".toList _ (by decide)]
  simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  change (runRead operations layout context (.identifier "CETTA_EVAL_INCOMPLETE_CAPACITY".toList) >>= fun value =>
    effects operations "eval_mark_incomplete".toList [value]) = _
  rw [local_read operations layout context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList _ (.i32 4) known]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rfl

/-- The source tests the actual nullable constructor reply, publishes only
through its chosen arm, and retains the capacity reason on the other arm. -/
private theorem frame_branch_is_complete_operation_tree (operations : Operations) (layout : RunLayout)
    (context : Context) (frame : Option Ptr) (fuel : Nat)
    (knownFrame : context "frame".toList =
      some (.scalar (runType "PrimeEvalStackFrame" 1) (some (.ptr frame))))
    (knownCapacity : context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4)))) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 2) context
      [.branch (TaskAdmission.ident "frame")
        [.effect (.call "prime_eval_stack_push".toList [TaskAdmission.ident "frame"])]
        [.effect (.call "eval_mark_incomplete".toList [TaskAdmission.ident "CETTA_EVAL_INCOMPLETE_CAPACITY"])]] =
      (do
        let present ← truth (.ptr frame)
        if present then
          match frame with | some address => operations.push address | none => CProg.undefined
        else operations.markIncomplete 4
        pure (.finished (.next context))) := by
  rw [StatementBlock.executeScopedWith.eq_def]
  change (runRead operations layout context (.identifier "frame".toList) >>= fun value =>
    truth value >>= fun present =>
      StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 1) context
        (if present then _ else _) >>= fun result =>
          ReadBlock.resume
            (fun updated => StatementBlock.executeScopedWith (services operations layout) emptyLayout 0
              (fuel + 1) updated []) result) = _
  rw [local_read operations layout context "frame".toList _ (.ptr frame) knownFrame]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext present
  cases present
  · simp only [Bool.false_eq_true, if_false]
    rw [StatementBlock.scoped_effect_keeps_continuation,
      capacity_effect_keeps_reason operations layout context knownCapacity]
    simp only [StatementBlock.executeScopedWith.eq_def, Prog.bind_eq, Prog.pure_eq,
      Prog.ret_bind, Prog.bind_assoc, ReadBlock.resume]
  · simp only [if_true]
    rw [StatementBlock.scoped_effect_keeps_continuation,
      push_effect_keeps_nullable_reply operations layout context frame knownFrame]
    cases frame <;> simp only [StatementBlock.executeScopedWith.eq_def, Prog.bind_eq, Prog.pure_eq,
      Prog.ret_bind, Prog.bind_assoc, ReadBlock.resume]


private def frameInitializer : CExpr :=
  .call "prime_eval_stack_normalize_atom_frame_new".toList
    [TaskAdmission.taskField "space", TaskAdmission.taskField "arena", TaskAdmission.taskField "atom",
      TaskAdmission.taskField "fuel", .unary .address (TaskAdmission.taskField "dynamic_env"),
      TaskAdmission.taskField "evaluator_id", TaskAdmission.taskField "target"]

private def frameBranch : CStatement :=
  .branch (TaskAdmission.ident "frame")
    [.effect (.call "prime_eval_stack_push".toList [TaskAdmission.ident "frame"])]
    [.effect (.call "eval_mark_incomplete".toList [TaskAdmission.ident "CETTA_EVAL_INCOMPLETE_CAPACITY"])]

private theorem frame_initial_value (operations : Operations) (layout : RunLayout) (value : CVal) :
    StatementBlock.ObjectBindings.scalarInitialValue (profile operations layout)
      (runType "PrimeEvalStackFrame" 1) value =
      (pointer value >>= fun frame => pure (.ptr frame)) := rfl

/-- The scalar frame declaration preserves its nullable conversion, selected
branch and restoration of the previous binding after the complete flow. -/
private theorem frame_block_is_complete_operation_tree (operations : Operations) (layout : RunLayout)
    (context : Context) (fuel : Nat)
    (knownCapacity : context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4)))) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 3) context
      [.declare (runType "PrimeEvalStackFrame" 1) "frame".toList frameInitializer, frameBranch] =
      (do
        let actual ← runRead operations layout context frameInitializer
        let frame ← pointer actual
        let present ← truth (.ptr frame)
        if present then
          match frame with | some address => operations.push address | none => CProg.undefined
        else operations.markIncomplete 4
        pure (.finished (.next context))) := by
  rw [StatementBlock.executeScopedWith.eq_def]
  change StatementBlock.ObjectBindings.declaration (profile operations layout) operations.region
    emptyLayout context (runType "PrimeEvalStackFrame" 1) "frame".toList (some frameInitializer)
    (fun updated => StatementBlock.executeScopedWith (services operations layout) emptyLayout 0
      (fuel + 2) updated [frameBranch]) = _
  have scalar : (profile operations layout).cellExtent (runType "PrimeEvalStackFrame" 1) = none := rfl
  simp only [StatementBlock.ObjectBindings.declaration, scalar, Prog.bind_eq]
  change (runRead operations layout context frameInitializer >>= fun actual =>
    StatementBlock.ObjectBindings.scalarInitialValue (profile operations layout)
      (runType "PrimeEvalStackFrame" 1) actual >>= fun converted =>
        StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 2)
          (Function.update context "frame".toList
            (some (.scalar (runType "PrimeEvalStackFrame" 1) (some converted)))) [frameBranch] >>= fun result =>
              pure (StatementBlock.ObjectBindings.restore "frame".toList (context "frame".toList) result)) = _
  simp only [frame_initial_value, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext actual
  congr 1
  funext frame
  unfold frameBranch
  rw [frame_branch_is_complete_operation_tree operations layout
    (Function.update context "frame".toList
      (some (.scalar (runType "PrimeEvalStackFrame" 1) (some (.ptr frame))))) frame fuel
      (by simp only [Function.update_self])
      (by
        rw [Function.update_of_ne
          (show "CETTA_EVAL_INCOMPLETE_CAPACITY".toList ≠ "frame".toList from by decide)]
        exact knownCapacity)]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext present
  cases present
  · simp only [Bool.false_eq_true, if_false, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind,
      StatementBlock.ObjectBindings.restore, ReadBlock.Result.mapContext,
      ReadBlock.Flow.mapContext, Function.update_idem, Function.update_eq_self]
  · simp only [if_true]
    cases frame <;> simp only [Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind,
      StatementBlock.ObjectBindings.restore, ReadBlock.Result.mapContext,
      ReadBlock.Flow.mapContext, Function.update_idem, Function.update_eq_self]


/-- The complete NORMALIZE source arm agrees with the independent constructor,
nullable publication/refusal and switch-owned break operation tree. -/
theorem normalize_arm_is_complete_operation_tree (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr) (fuel : Nat)
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (knownCounter : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList =
      some (.scalar (runType "int") (some (.i32 264))))
    (knownCapacity : context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4)))) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 5)
      context normalizeArm = normalizeOperations operations layout context task := by
  unfold normalizeArm
  rw [StatementBlock.executeScopedWith.eq_def]
  change ((services operations layout).effect emptyLayout context
    (.call "cetta_runtime_stats_inc".toList
      [TaskAdmission.ident "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE"]) >>=
        fun _ => StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 4)
          context _) = _
  simp only [TaskAdmission.ident]
  rw [statistics_effect operations layout context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE"
    264 knownCounter]
  unfold normalizeOperations normalizeEffects
  simp only [Prog.bind_eq]
  congr 1
  funext ignored
  rw [StatementBlock.scoped_nested_block_keeps_flow _ _ _ _ _ _ _ (by rfl)]
  change (StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 3)
    context [.declare (runType "PrimeEvalStackFrame" 1) "frame".toList frameInitializer, frameBranch] >>=
      fun result => ReadBlock.resume
        (fun updated => StatementBlock.executeScopedWith (services operations layout) emptyLayout 0
          (fuel + 3) updated [.break]) result) = _
  rw [frame_block_is_complete_operation_tree operations layout context fuel knownCapacity]
  have initializer := normalize_read_keeps_complete_constructor operations layout context task knownTask
  change runRead operations layout context frameInitializer = _ at initializer
  rw [initializer]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext space
  congr 1
  funext arena
  congr 1
  funext atom
  congr 1
  funext inputFuel
  congr 1
  funext evaluator
  congr 1
  funext target
  congr 1
  funext result
  congr 1
  funext actual
  congr 1
  funext frame
  congr 1
  funext present
  cases present
  · simp only [Bool.false_eq_true, if_false, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
      ReadBlock.resume, StatementBlock.executeScopedWith.eq_def]
  · simp only [if_true]
    cases frame <;> simp only [Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
      ReadBlock.resume, StatementBlock.executeScopedWith.eq_def]


private def taskCases : List (CExpr × List CStatement) :=
  [(TaskAdmission.ident "PRIME_EVAL_STACK_TASK_BIND", bindArm),
    (TaskAdmission.ident "PRIME_EVAL_STACK_TASK_CALL", callArm),
    (TaskAdmission.ident "PRIME_EVAL_STACK_TASK_NORMALIZE", normalizeArm)]

private def selectedPlan (kind : UInt32) : List CStatement :=
  if kind = 0 then [.block bindArm, .block callArm, .block normalizeArm, .block []]
  else if kind = 1 then [.block callArm, .block normalizeArm, .block []]
  else if kind = 2 then [.block normalizeArm, .block []]
  else [.block []]

/-- Static enum planning preserves the source's full fall-through suffix,
including its default block; only execution's break will suppress that suffix. -/
private theorem case_plan_keeps_actual_fallthrough (kind : UInt32) :
    StatementBlock.integerSwitchBody caseConstants (.u32 kind) taskCases [] =
      pure (selectedPlan kind) := by
  by_cases zero : kind = 0
  · simp [StatementBlock.integerSwitchBody, LocalBlock.switchBody?, ScalarRead.expression,
      ScalarRead.equal?, scalar, resolved, caseConstants, taskCases, TaskAdmission.ident,
      selectedPlan, zero]
  · by_cases one : kind = 1
    · simp [StatementBlock.integerSwitchBody, LocalBlock.switchBody?, ScalarRead.expression,
        ScalarRead.equal?, scalar, resolved, caseConstants, taskCases, TaskAdmission.ident,
        selectedPlan, one]
    · by_cases two : kind = 2
      · simp [StatementBlock.integerSwitchBody, LocalBlock.switchBody?, ScalarRead.expression,
          ScalarRead.equal?, scalar, resolved, caseConstants, taskCases, TaskAdmission.ident,
          selectedPlan, two]
      · simp [StatementBlock.integerSwitchBody, LocalBlock.switchBody?, ScalarRead.expression,
          ScalarRead.equal?, scalar, resolved, caseConstants, taskCases, TaskAdmission.ident,
          selectedPlan, zero, one, two]


/-- The source retains every fall-through arm but its actual break suppresses
later arms. Unknown enum values retain the empty default's ordinary flow. -/
private theorem selected_plan_is_complete_tree (operations : Operations) (layout : RunLayout)
    (context : Context) (driver : Option Ptr) (task : Ptr) (kind : UInt32) (fuel : Nat)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (knownBind : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList =
      some (.scalar (runType "int") (some (.i32 262))))
    (knownCall : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList =
      some (.scalar (runType "int") (some (.i32 263))))
    (knownNormalize : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList =
      some (.scalar (runType "int") (some (.i32 264))))
    (knownCapacity : context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4)))) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 6)
      context (selectedPlan kind) =
      (if kind = 0 then bindOperations operations layout context driver task
       else if kind = 1 then callOperations operations layout context task
       else if kind = 2 then normalizeOperations operations layout context task
       else pure (.finished (.next context))) := by
  by_cases zero : kind = 0
  · simp only [selectedPlan, zero, ↓reduceIte]
    rw [StatementBlock.scoped_nested_block_keeps_flow _ _ _ _ _ _ _ (by rfl),
      bind_arm_is_complete_operation_tree operations layout context driver task fuel knownDriver knownTask knownBind]
    simp only [bindOperations, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
  · by_cases one : kind = 1
    · simp [selectedPlan, one]
      rw [StatementBlock.scoped_nested_block_keeps_flow _ _ _ _ _ _ _ (by rfl),
        call_arm_is_complete_operation_tree operations layout context task (fuel + 2) knownTask knownCall]
      simp only [callOperations, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
    · by_cases two : kind = 2
      · simp [selectedPlan, two]
        rw [StatementBlock.scoped_nested_block_keeps_flow _ _ _ _ _ _ _ (by rfl),
          normalize_arm_is_complete_operation_tree operations layout context task fuel knownTask knownNormalize knownCapacity]
        simp only [normalizeOperations, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
      · simp only [selectedPlan, zero, one, two, ↓reduceIte]
        rw [StatementBlock.scoped_nested_block_keeps_flow _ _ _ _ _ _ _ (by rfl)]
        simp only [StatementBlock.executeScopedWith.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]


/-- The nested arrow retains Task.target's actual pointer and OutcomeSet's
own typed wide-length descriptor. It does not choose an offset by spelling. -/
private theorem target_length_read (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr)
    (known : context "task".toList = some (.object (runType "PrimeEvalStackTask") task)) :
    runRead operations layout context (.field (TaskAdmission.taskField "target") "len".toList true) =
      (taskRead layout task "target" >>= fun target =>
        field (fun name => if name = "len".toList then
          some ⟨layout.outcomeLength, .word64⟩ else none) target "len".toList) := by
  have ownerType : ScalarBytes.typeOf?
      (StatementBlock.ObjectBindings.types context (profile operations layout).outsideTypes)
      (TaskAdmission.taskField "target") (profile operations layout).fieldTypes =
        some (runType "OutcomeSet" 1) := by
    simp only [TaskAdmission.taskField, TaskAdmission.ident, ScalarBytes.typeOf?,
      StatementBlock.ObjectBindings.types, known, bind, Option.bind_some, Bool.false_eq_true, if_false]
    rfl
  rw [runRead, StatementBlock.ObjectBindings.read, expressionWithNames.eq_def]
  change (runRead operations layout context (TaskAdmission.taskField "target") >>= fun target =>
    field ((StatementBlock.ObjectBindings.objects (profile operations layout) context).fieldLayout
      emptyLayout (TaskAdmission.taskField "target") true) target "len".toList) = _
  rw [task_field_read operations layout context task "target" known,
    StatementBlock.ObjectBindings.arrow_layout_uses_retained_record_type
      (profile operations layout) context (recordLayouts layout) emptyLayout
      (TaskAdmission.taskField "target") (runType "OutcomeSet") (by rfl) ownerType]
  rfl

private def growthCondition : CExpr :=
  .binary .and (TaskAdmission.taskField "target")
    (.binary .gt (.field (TaskAdmission.taskField "target") "len".toList true)
      (TaskAdmission.ident "published_before"))

/-- Growth notification uses the source's current target and wide count.
The pointer and its field owner are read separately in their actual order. -/
private theorem publication_growth_read (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr) (published : UInt64)
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (knownPublished : context "published_before".toList =
      some (.scalar (runType "CettaCount") (some (.u64 published)))) :
    runRead operations layout context growthCondition =
      (publicationGrowth layout task published >>= fun grew => pure (CVal.bool grew)) := by
  rw [runRead, StatementBlock.ObjectBindings.read, growthCondition, expressionWithNames.eq_def]
  change (runRead operations layout context (TaskAdmission.taskField "target") >>= fun target =>
    truth target >>= fun present =>
      if present then
        runRead operations layout context
          (.binary .gt (.field (TaskAdmission.taskField "target") "len".toList true)
            (TaskAdmission.ident "published_before")) >>= fun greater =>
              truth greater >>= fun grew => pure (CVal.bool grew)
      else pure (CVal.bool false)) = _
  rw [task_field_read operations layout context task "target" knownTask]
  unfold publicationGrowth
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext target
  congr 1
  funext present
  cases present
  · simp only [Bool.false_eq_true, if_false, Prog.pure_eq, Prog.ret_bind]
  · simp only [if_true]
    rw [runRead, StatementBlock.ObjectBindings.read, expressionWithNames.eq_def]
    simp only [Prog.bind_eq, Prog.bind_assoc]
    change (runRead operations layout context
        (.field (TaskAdmission.taskField "target") "len".toList true) >>= fun length =>
      runRead operations layout context (TaskAdmission.ident "published_before") >>= fun previous =>
        binary .gt length previous >>= fun greater => truth greater >>= fun grew => pure (CVal.bool grew)) = _
    simp only [TaskAdmission.ident]
    rw [target_length_read operations layout context task knownTask,
      local_read operations layout context "published_before".toList _ (.u64 published) knownPublished]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]


/-- Selector loading, fall-through planning, switch-owned break and the whole
outer continuation compose without projecting the dispatch result. -/
private theorem dispatch_statement_keeps_complete_tree (operations : Operations) (layout : RunLayout)
    (context : Context) (driver : Option Ptr) (task : Ptr) (fuel : Nat) (rest : List CStatement)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (knownBind : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList =
      some (.scalar (runType "int") (some (.i32 262))))
    (knownCall : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList =
      some (.scalar (runType "int") (some (.i32 263))))
    (knownNormalize : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList =
      some (.scalar (runType "int") (some (.i32 264))))
    (knownCapacity : context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4)))) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 7)
      context (.switch (TaskAdmission.taskField "kind") taskCases [] :: rest) =
      (dispatch operations layout context driver task >>= fun result =>
        StatementBlock.resumeSwitch
          (fun updated => StatementBlock.executeScopedWith (services operations layout) emptyLayout 0
            (fuel + 6) updated rest) result) := by
  rw [StatementBlock.scoped_switch_keeps_selection_and_flow]
  simp only [services, StatementBlock.ObjectBindings.services,
    StatementBlock.ObjectBindings.selectSwitch, Prog.bind_eq, Prog.bind_assoc]
  change (runRead operations layout context (TaskAdmission.taskField "kind") >>= fun kind =>
    StatementBlock.integerSwitchBody caseConstants kind taskCases [] >>= fun selected =>
      StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 6) context selected >>=
        fun result => StatementBlock.resumeSwitch
          (fun updated => StatementBlock.executeScopedWith (services operations layout) emptyLayout 0
            (fuel + 6) updated rest) result) = _
  rw [task_field_read operations layout context task "kind" knownTask]
  unfold taskRead
  rw [word_field_uses_actual_offset _ task "kind".toList _ (by rfl)]
  unfold dispatch
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext kind
  rw [case_plan_keeps_actual_fallthrough]
  simp only [Prog.pure_eq, Prog.ret_bind]
  rw [selected_plan_is_complete_tree operations layout context driver task kind fuel
    knownDriver knownTask knownBind knownCall knownNormalize knownCapacity]
  rfl


private theorem evaluator_assignment (operations : Operations) (layout : RunLayout)
    (context : Context) (operand : CExpr) (value : UInt64)
    (outside : context "g_prime_need_evaluator_id".toList = none)
    (actual : runRead operations layout context operand = pure (.u64 value)) :
    (services operations layout).assignment emptyLayout context
      (.assign (TaskAdmission.ident "g_prime_need_evaluator_id") operand) =
      (CProg.store layout.evaluatorId (.u64 value) >>= fun _ => pure context) := by
  have targetType : ScalarBytes.typeOf?
      (StatementBlock.ObjectBindings.types context (profile operations layout).outsideTypes)
      (TaskAdmission.ident "g_prime_need_evaluator_id") (profile operations layout).fieldTypes =
        some (runType "uint64_t") := by
    simp only [TaskAdmission.ident, ScalarBytes.typeOf?, StatementBlock.ObjectBindings.types, outside]
    rfl
  change StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout context
    (.assign (TaskAdmission.ident "g_prime_need_evaluator_id") operand) = _
  rw [StatementBlock.ObjectBindings.assignment, targetType]
  change (pure (runType "uint64_t") >>= fun _ =>
    runRead operations layout context operand >>= fun value =>
      StatementBlock.ObjectBindings.writeValue (profile operations layout) emptyLayout context
        (TaskAdmission.ident "g_prime_need_evaluator_id") value) = _
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rw [actual]
  simp only [Prog.pure_eq, Prog.ret_bind, TaskAdmission.ident]
  exact global_evaluator_write_keeps_typed_value operations layout context value outside

private theorem stream_note_keeps_current_target (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr)
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task)) :
    (services operations layout).effect emptyLayout context
      (.call "prime_eval_stack_stream_note".toList [TaskAdmission.taskField "target"]) =
        (CProg.loadPtr (task + layout.taskOffset "target".toList) >>= operations.streamNote) := by
  rw [effect_keeps_arguments operations layout context "prime_eval_stack_stream_note".toList _ (by decide)]
  simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  change (runRead operations layout context (TaskAdmission.taskField "target") >>= fun value =>
    effects operations "prime_eval_stack_stream_note".toList [value]) = _
  rw [task_field_read operations layout context task "target" knownTask]
  unfold taskRead
  rw [pointer_field_uses_actual_offset _ task "target".toList _ (by rfl)]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rfl

private theorem task_retirement_keeps_actual_address (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr)
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task)) :
    (services operations layout).effect emptyLayout context
      (.call "prime_eval_stack_task_free".toList
        [.unary .address (TaskAdmission.ident "task")]) = operations.releaseTask task := by
  rw [effect_keeps_arguments operations layout context "prime_eval_stack_task_free".toList _ (by decide)]
  simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  change (runRead operations layout context (.unary .address (.identifier "task".toList)) >>= fun value =>
    effects operations "prime_eval_stack_task_free".toList [value]) = _
  rw [runRead, StatementBlock.ObjectBindings.local_object_address_does_not_read_value
    (profile operations layout) emptyLayout context "task".toList (runType "PrimeEvalStackTask") task knownTask]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rfl

private def publicationBranch : CStatement :=
  .branch growthCondition
    [.effect (.call "prime_eval_stack_stream_note".toList [TaskAdmission.taskField "target"])] []

private theorem publication_branch_keeps_wide_current_comparison
    (operations : Operations) (layout : RunLayout) (context : Context) (task : Ptr)
    (published : UInt64) (fuel : Nat)
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (knownPublished : context "published_before".toList =
      some (.scalar (runType "CettaCount") (some (.u64 published)))) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 2)
      context [publicationBranch] =
      (do
        let grew ← publicationGrowth layout task published
        if grew then
          CProg.loadPtr (task + layout.taskOffset "target".toList) >>= operations.streamNote
        else pure ()
        pure (.finished (.next context))) := by
  unfold publicationBranch
  rw [StatementBlock.executeScopedWith.eq_def]
  change (runRead operations layout context growthCondition >>= fun value =>
    truth value >>= fun grew =>
      StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 1) context
        (if grew then _ else _) >>= fun result =>
          ReadBlock.resume
            (fun updated => StatementBlock.executeScopedWith (services operations layout) emptyLayout 0
              (fuel + 1) updated []) result) = _
  rw [publication_growth_read operations layout context task published knownTask knownPublished]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
  congr 1
  funext grew
  cases grew
  · simp only [Bool.false_eq_true, if_false, StatementBlock.executeScopedWith.eq_def,
      Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
  · simp only [if_true]
    rw [StatementBlock.scoped_effect_keeps_continuation,
      stream_note_keeps_current_target operations layout context task knownTask]
    simp only [StatementBlock.executeScopedWith.eq_def, Prog.bind_eq, Prog.bind_assoc,
      Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]

private def completionStatements : List CStatement :=
  [.assign (TaskAdmission.ident "g_prime_need_evaluator_id") (TaskAdmission.ident "previous_evaluator_id"),
   .assign (TaskAdmission.driverField "active_task") .null,
   publicationBranch,
   .effect (.call "prime_eval_stack_task_free".toList [.unary .address (TaskAdmission.ident "task")]),
   .assign (TaskAdmission.driverField "running_task") (.bool false)]

private theorem completion_is_actual_source_suffix :
    runSyntax.body.drop 15 = completionStatements := rfl

/-- Publication reads the live count before retirement. The final flag write
occurs before enclosing guard cleanup; no effect is moved across that order. -/
theorem completion_keeps_entire_source_order (operations : Operations) (layout : RunLayout)
    (context : Context) (driver : Option Ptr) (task : Ptr) (previous published : UInt64) (fuel : Nat)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (knownPrevious : context "previous_evaluator_id".toList =
      some (.scalar (runType "uint64_t") (some (.u64 previous))))
    (knownPublished : context "published_before".toList =
      some (.scalar (runType "CettaCount") (some (.u64 published))))
    (outside : context "g_prime_need_evaluator_id".toList = none) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 5)
      context completionStatements = completion operations layout context driver task previous published := by
  unfold completionStatements
  rw [StatementBlock.scoped_assignment_keeps_continuation,
    evaluator_assignment operations layout context (TaskAdmission.ident "previous_evaluator_id") previous outside]
  · unfold completion
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
    congr 1
    funext restored
    rw [StatementBlock.scoped_assignment_keeps_continuation,
      driver_assignment operations layout context driver "active_task" (runType "PrimeEvalStackTask" 1)
        .null (.ptr none) knownDriver (by rfl) (by rfl) (by rfl) (by rfl)]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
    congr 1
    funext deactivated
    unfold publicationBranch
    rw [StatementBlock.executeScopedWith.eq_def]
    change (runRead operations layout context growthCondition >>= fun value => truth value >>= fun grew =>
      StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 2) context
        (if grew then _ else _) >>= fun result =>
          ReadBlock.resume
            (fun updated => StatementBlock.executeScopedWith (services operations layout) emptyLayout 0
              (fuel + 2) updated _) result) = _
    rw [publication_growth_read operations layout context task published knownTask knownPublished]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
    congr 1
    funext grew
    have retirement : StatementBlock.executeScopedWith (services operations layout) emptyLayout 0
        (fuel + 2) context
          [.effect (.call "prime_eval_stack_task_free".toList [.unary .address (TaskAdmission.ident "task")]),
           .assign (TaskAdmission.driverField "running_task") (.bool false)] =
          (operations.releaseTask task >>= fun _ =>
            driverStore layout driver "running_task" (.bool false) >>= fun _ =>
              pure (.finished (.next context))) := by
      rw [StatementBlock.scoped_effect_keeps_continuation,
        task_retirement_keeps_actual_address operations layout context task knownTask,
        StatementBlock.scoped_assignment_keeps_continuation,
        driver_assignment operations layout context driver "running_task" (runType "bool")
          (.bool false) (.bool false) knownDriver (by rfl) (by rfl) (by rfl) (by rfl)]
      simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
        StatementBlock.executeScopedWith.eq_def]
    cases grew
    · simp only [Bool.false_eq_true, if_false]
      rw [StatementBlock.executeScopedWith.eq_def]
      simp only [Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
      exact retirement
    · simp only [if_true]
      rw [StatementBlock.scoped_effect_keeps_continuation,
        stream_note_keeps_current_target operations layout context task knownTask]
      rw [StatementBlock.executeScopedWith.eq_def]
      simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
      rw [retirement]
      rfl
  · exact local_read operations layout context "previous_evaluator_id".toList _ _ knownPrevious


private theorem evaluator_read_keeps_global_word (operations : Operations) (layout : RunLayout)
    (context : Context) (outside : context "g_prime_need_evaluator_id".toList = none) :
    runRead operations layout context (TaskAdmission.ident "g_prime_need_evaluator_id") =
      (CProg.loadU64 layout.evaluatorId >>= fun value => pure (.u64 value)) := by
  simp only [runRead, StatementBlock.ObjectBindings.read, TaskAdmission.ident,
    expressionWithNames.eq_def, localOrLocated, StatementBlock.ObjectBindings.values,
    StatementBlock.ObjectBindings.declared, outside, Option.isSome_none,
    Bool.false_eq_true, if_false]
  change located (globalLocations layout) "g_prime_need_evaluator_id".toList = _
  unfold located
  change field (fun _ => some ⟨0, .word64⟩) (.ptr (some layout.evaluatorId))
    "g_prime_need_evaluator_id".toList = _
  rw [word64_field_uses_actual_offset _ layout.evaluatorId
    "g_prime_need_evaluator_id".toList 0 (by rfl)]
  rfl

private def needInitializer : CExpr :=
  .call "prime_need_active_enter".toList [.unary .address (TaskAdmission.taskField "dynamic_env")]

/-- By-value Need entry keeps every returned guard cell and the exact source
dynamic-environment address. Ordinary overlay remains the supplied service. -/
private theorem need_initializer_retains_every_guard_cell (operations : Operations) (layout : RunLayout)
    (context : Context) (task guard : Ptr)
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task)) :
    StatementBlock.ObjectBindings.initializeRecord (profile operations layout) emptyLayout context
      (runType "PrimeNeedActiveGuard") layout.needCells guard needInitializer =
      (operations.needEnter (task + layout.taskOffset "dynamic_env".toList) >>= fun fields =>
        if fields.length = layout.needCells then CProg.initializeCells guard fields else CProg.undefined) := by
  unfold needInitializer
  rw [StatementBlock.ObjectBindings.record_call_keeps_arguments_and_complete_return
    (profile operations layout) emptyLayout context (runType "PrimeNeedActiveGuard")
    layout.needCells guard "prime_need_active_enter".toList _ (needRecord operations) (by rfl) (by rfl)]
  simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  change (runRead operations layout context
      (.unary .address (TaskAdmission.taskField "dynamic_env")) >>= fun value =>
    (needRecord operations).invoke [value] >>= fun fields =>
      if fields.length = layout.needCells then CProg.initializeCells guard fields else CProg.undefined) = _
  rw [task_field_address operations layout context task "dynamic_env" .embedded knownTask (by rfl)]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rfl

private def authorityInitializer : CExpr :=
  .call "prime_eval_authority_enter".toList [TaskAdmission.taskField "pure_authority"]

/-- Authority entry retains its full saved-driver/saved-flag return and the
same complete extent check. It is not summarized by its incoming Boolean. -/
private theorem authority_initializer_retains_both_saved_cells (operations : Operations)
    (layout : RunLayout) (context : Context) (task guard : Ptr)
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task)) :
    StatementBlock.ObjectBindings.initializeRecord (profile operations layout) emptyLayout context
      (runType "PrimeEvalAuthorityGuard") 2 guard authorityInitializer =
      (CProg.loadBool (task + layout.taskOffset "pure_authority".toList) >>= fun incoming =>
        Authority.enter layout.authority incoming >>= fun fields =>
          if fields.length = 2 then CProg.initializeCells guard fields else CProg.undefined) := by
  unfold authorityInitializer
  rw [StatementBlock.ObjectBindings.record_call_keeps_arguments_and_complete_return
    (profile operations layout) emptyLayout context (runType "PrimeEvalAuthorityGuard")
    2 guard "prime_eval_authority_enter".toList _ (Authority.recordCall layout.authority) (by rfl) (by rfl)]
  simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  change (runRead operations layout context (TaskAdmission.taskField "pure_authority") >>= fun value =>
    (Authority.recordCall layout.authority).invoke [value] >>= fun fields =>
      if fields.length = 2 then CProg.initializeCells guard fields else CProg.undefined) = _
  rw [task_field_read operations layout context task "pure_authority" knownTask]
  unfold taskRead
  rw [boolean_field_uses_actual_offset _ task "pure_authority".toList _ (by rfl)]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  rfl


private theorem evaluator_assignment_keeps_live_reader (operations : Operations) (layout : RunLayout)
    (context : Context) (operand : CExpr)
    (outside : context "g_prime_need_evaluator_id".toList = none) :
    (services operations layout).assignment emptyLayout context
      (.assign (TaskAdmission.ident "g_prime_need_evaluator_id") operand) =
      (runRead operations layout context operand >>= fun value =>
        StatementBlock.ObjectBindings.writeValue (profile operations layout) emptyLayout context
          (TaskAdmission.ident "g_prime_need_evaluator_id") value) := by
  have targetType : ScalarBytes.typeOf?
      (StatementBlock.ObjectBindings.types context (profile operations layout).outsideTypes)
      (TaskAdmission.ident "g_prime_need_evaluator_id") (profile operations layout).fieldTypes =
        some (runType "uint64_t") := by
    simp only [TaskAdmission.ident, ScalarBytes.typeOf?, StatementBlock.ObjectBindings.types, outside]
    rfl
  change StatementBlock.ObjectBindings.assignment (profile operations layout) emptyLayout context
    (.assign (TaskAdmission.ident "g_prime_need_evaluator_id") operand) = _
  rw [StatementBlock.ObjectBindings.assignment, targetType]
  rfl

private theorem evaluator_installation_keeps_task_word (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr)
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (outside : context "g_prime_need_evaluator_id".toList = none) :
    (services operations layout).assignment emptyLayout context
      (.assign (TaskAdmission.ident "g_prime_need_evaluator_id") (TaskAdmission.taskField "evaluator_id")) =
      (CProg.loadU64 (task + layout.taskOffset "evaluator_id".toList) >>= fun evaluator =>
        CProg.store layout.evaluatorId (.u64 evaluator) >>= fun _ => pure context) := by
  rw [evaluator_assignment_keeps_live_reader operations layout context _ outside,
    task_field_read operations layout context task "evaluator_id" knownTask]
  unfold taskRead
  rw [word64_field_uses_actual_offset _ task "evaluator_id".toList _ (by rfl)]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1
  funext evaluator
  exact global_evaluator_write_keeps_typed_value operations layout context evaluator outside

private def evaluatorStatements : List CStatement :=
  [.declare (runType "uint64_t") "previous_evaluator_id".toList
      (TaskAdmission.ident "g_prime_need_evaluator_id"),
   .assign (TaskAdmission.ident "g_prime_need_evaluator_id") (TaskAdmission.taskField "evaluator_id"),
   .switch (TaskAdmission.taskField "kind") taskCases []] ++ completionStatements

private theorem evaluator_is_actual_source_suffix :
    runSyntax.body.drop 12 = evaluatorStatements := rfl


/-- Every dispatch arm retains the same lexical context beneath its
switch-owned break, so equal complete continuations compose through it. -/
private theorem dispatch_continuation_congr (operations : Operations) (layout : RunLayout)
    (context : Context) (driver : Option Ptr) (task : Ptr)
    (left right : Context → CProg CVal (ReadBlock.Result Context))
    (agreement : left context = right context) :
    (dispatch operations layout context driver task >>= StatementBlock.resumeSwitch left) =
      (dispatch operations layout context driver task >>= StatementBlock.resumeSwitch right) := by
  unfold dispatch
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext kind
  split
  · simp only [bindOperations, Prog.bind_eq, Prog.bind_assoc,
      Prog.pure_eq, Prog.ret_bind, StatementBlock.resumeSwitch, agreement]
  · split
    · simp only [callOperations, Prog.bind_eq, Prog.bind_assoc,
        Prog.pure_eq, Prog.ret_bind, StatementBlock.resumeSwitch, agreement]
    · split
      · simp only [normalizeOperations, Prog.bind_eq, Prog.bind_assoc,
          Prog.pure_eq, Prog.ret_bind, StatementBlock.resumeSwitch, agreement]
      · simp only [Prog.pure_eq, Prog.ret_bind, StatementBlock.resumeSwitch, ReadBlock.resume, agreement]


private theorem previous_evaluator_declaration_keeps_read_and_scope (operations : Operations)
    (layout : RunLayout) (context : Context)
    (outside : context "g_prime_need_evaluator_id".toList = none)
    (continuation : Context → CProg CVal (ReadBlock.Result Context)) :
    StatementBlock.ObjectBindings.declaration (profile operations layout) operations.region
      emptyLayout context (runType "uint64_t") "previous_evaluator_id".toList
      (some (TaskAdmission.ident "g_prime_need_evaluator_id")) continuation =
      (do
        let previous ← CProg.loadU64 layout.evaluatorId
        let result ← continuation
          (bindScalar context "previous_evaluator_id" (runType "uint64_t") (.u64 previous))
        pure (StatementBlock.ObjectBindings.restore "previous_evaluator_id".toList
          (context "previous_evaluator_id".toList) result)) := by
  rw [StatementBlock.ObjectBindings.initialized_scalar_keeps_read_conversion_and_flow
    (profile operations layout) operations.region emptyLayout context (runType "uint64_t")
    "previous_evaluator_id".toList _ (by rfl)]
  have globalRead := evaluator_read_keeps_global_word operations layout context outside
  change StatementBlock.ObjectBindings.read (profile operations layout) emptyLayout context
    (TaskAdmission.ident "g_prime_need_evaluator_id") = _ at globalRead
  rw [globalRead]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1


private theorem evaluator_installation_before_complete_flow (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr)
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (outside : context "g_prime_need_evaluator_id".toList = none)
    (continuation : Context → CProg CVal (ReadBlock.Result Context)) :
    ((services operations layout).assignment emptyLayout context
      (.assign (TaskAdmission.ident "g_prime_need_evaluator_id") (TaskAdmission.taskField "evaluator_id"))
        >>= continuation) =
      (CProg.loadU64 (task + layout.taskOffset "evaluator_id".toList) >>= fun evaluator =>
        CProg.store layout.evaluatorId (.u64 evaluator) >>= fun _ => continuation context) := by
  rw [evaluator_installation_keeps_task_word operations layout context task knownTask outside]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]


private def installedEvaluatorStatements : List CStatement :=
  .assign (TaskAdmission.ident "g_prime_need_evaluator_id") (TaskAdmission.taskField "evaluator_id") ::
    .switch (TaskAdmission.taskField "kind") taskCases [] :: completionStatements

private theorem installed_evaluator_keeps_dispatch_and_completion (operations : Operations)
    (layout : RunLayout) (context : Context) (driver : Option Ptr) (task : Ptr)
    (previous published : UInt64) (fuel : Nat)
    (knownPrevious : context "previous_evaluator_id".toList =
      some (.scalar (runType "uint64_t") (some (.u64 previous))))
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (knownPublished : context "published_before".toList =
      some (.scalar (runType "CettaCount") (some (.u64 published))))
    (knownBind : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList =
      some (.scalar (runType "int") (some (.i32 262))))
    (knownCall : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList =
      some (.scalar (runType "int") (some (.i32 263))))
    (knownNormalize : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList =
      some (.scalar (runType "int") (some (.i32 264))))
    (knownCapacity : context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4))))
    (outside : context "g_prime_need_evaluator_id".toList = none) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 8)
      context installedEvaluatorStatements =
      installedEvaluatorBody operations layout context driver task previous published := by
  have sourceTail : StatementBlock.executeScopedWith (services operations layout) emptyLayout 0
      (fuel + 7) context (.switch (TaskAdmission.taskField "kind") taskCases [] :: completionStatements) =
      (dispatch operations layout context driver task >>= StatementBlock.resumeSwitch
        (fun actual => completion operations layout actual driver task previous published)) := by
    rw [dispatch_statement_keeps_complete_tree operations layout context driver task fuel
      completionStatements knownDriver knownTask knownBind knownCall knownNormalize knownCapacity]
    exact dispatch_continuation_congr operations layout context driver task _ _
      (completion_keeps_entire_source_order operations layout context driver task previous published
        (fuel + 1) knownDriver knownTask knownPrevious knownPublished outside)
  unfold installedEvaluatorStatements
  rw [StatementBlock.scoped_assignment_keeps_continuation,
    evaluator_installation_before_complete_flow operations layout context task knownTask outside]
  unfold installedEvaluatorBody
  simp only [Prog.bind_eq]
  congr 1
  funext evaluator
  congr 1
  funext installed
  exact sourceTail

private theorem installed_evaluator_keeps_complete_readout (operations : Operations)
    (layout : RunLayout) (context : Context) (driver : Option Ptr) (task : Ptr)
    (previous published : UInt64) (fuel : Nat)
    (knownPrevious : context "previous_evaluator_id".toList =
      some (.scalar (runType "uint64_t") (some (.u64 previous))))
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (knownPublished : context "published_before".toList =
      some (.scalar (runType "CettaCount") (some (.u64 published))))
    (knownBind : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList =
      some (.scalar (runType "int") (some (.i32 262))))
    (knownCall : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList =
      some (.scalar (runType "int") (some (.i32 263))))
    (knownNormalize : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList =
      some (.scalar (runType "int") (some (.i32 264))))
    (knownCapacity : context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4))))
    (outside : context "g_prime_need_evaluator_id".toList = none)
    (readout : ReadBlock.Result Context → ReadBlock.Result Context) :
    (StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 8)
      context installedEvaluatorStatements >>= fun result => pure (readout result)) =
    (installedEvaluatorBody operations layout context driver task previous published >>=
      fun result => pure (readout result)) := by
  have agreement := installed_evaluator_keeps_dispatch_and_completion operations layout context
    driver task previous published fuel knownPrevious knownDriver knownTask knownPublished
    knownBind knownCall knownNormalize knownCapacity outside
  exact congrArg (fun program : CProg CVal (ReadBlock.Result Context) =>
    program >>= fun result => pure (readout result)) agreement


private theorem saved_evaluator_suffix_keeps_flow_readout (operations : Operations) (layout : RunLayout)
    (context : Context) (driver : Option Ptr) (task : Ptr) (published : UInt64) (fuel : Nat)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (knownPublished : context "published_before".toList =
      some (.scalar (runType "CettaCount") (some (.u64 published))))
    (knownBind : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList =
      some (.scalar (runType "int") (some (.i32 262))))
    (knownCall : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList =
      some (.scalar (runType "int") (some (.i32 263))))
    (knownNormalize : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList =
      some (.scalar (runType "int") (some (.i32 264))))
    (knownCapacity : context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4))))
    (outside : context "g_prime_need_evaluator_id".toList = none)
    (previous : UInt64) :
    (StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 8)
      (bindScalar context "previous_evaluator_id" (runType "uint64_t") (.u64 previous))
      installedEvaluatorStatements >>= fun result => pure (StatementBlock.ObjectBindings.restore
        "previous_evaluator_id".toList (context "previous_evaluator_id".toList) result)) =
    (installedEvaluatorBody operations layout
      (bindScalar context "previous_evaluator_id" (runType "uint64_t") (.u64 previous))
      driver task previous published >>= fun result => pure (StatementBlock.ObjectBindings.restore
        "previous_evaluator_id".toList (context "previous_evaluator_id".toList) result)) := by
  have distinct_driverIn : "driver".toList ≠ "previous_evaluator_id".toList := by
    intro same
    have sameString := String.toList_inj.mp same
    have distinctString : "driver" ≠ "previous_evaluator_id" := by decide
    exact distinctString sameString
  have distinct_taskIn : "task".toList ≠ "previous_evaluator_id".toList := by
    intro same
    have sameString := String.toList_inj.mp same
    have distinctString : "task" ≠ "previous_evaluator_id" := by decide
    exact distinctString sameString
  have distinct_publishedIn : "published_before".toList ≠ "previous_evaluator_id".toList := by
    intro same
    have sameString := String.toList_inj.mp same
    have distinctString : "published_before" ≠ "previous_evaluator_id" := by decide
    exact distinctString sameString
  have distinct_bindIn : "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList ≠ "previous_evaluator_id".toList := by
    intro same
    have sameString := String.toList_inj.mp same
    have distinctString : "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND" ≠ "previous_evaluator_id" := by decide
    exact distinctString sameString
  have distinct_callIn : "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList ≠ "previous_evaluator_id".toList := by
    intro same
    have sameString := String.toList_inj.mp same
    have distinctString : "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL" ≠ "previous_evaluator_id" := by decide
    exact distinctString sameString
  have distinct_normalizeIn : "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList ≠ "previous_evaluator_id".toList := by
    intro same
    have sameString := String.toList_inj.mp same
    have distinctString : "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE" ≠ "previous_evaluator_id" := by decide
    exact distinctString sameString
  have distinct_capacityIn : "CETTA_EVAL_INCOMPLETE_CAPACITY".toList ≠ "previous_evaluator_id".toList := by
    intro same
    have sameString := String.toList_inj.mp same
    have distinctString : "CETTA_EVAL_INCOMPLETE_CAPACITY" ≠ "previous_evaluator_id" := by decide
    exact distinctString sameString
  have distinct_outsideIn : "g_prime_need_evaluator_id".toList ≠ "previous_evaluator_id".toList := by
    intro same
    have sameString := String.toList_inj.mp same
    have distinctString : "g_prime_need_evaluator_id" ≠ "previous_evaluator_id" := by decide
    exact distinctString sameString
  have driverIn : (bindScalar context "previous_evaluator_id" (runType "uint64_t") (.u64 previous)) "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))) := by
    unfold bindScalar
    rewrite [Function.update_of_ne distinct_driverIn]
    exact knownDriver
  have taskIn : (bindScalar context "previous_evaluator_id" (runType "uint64_t") (.u64 previous)) "task".toList = some (.object (runType "PrimeEvalStackTask") task) := by
    unfold bindScalar
    rewrite [Function.update_of_ne distinct_taskIn]
    exact knownTask
  have publishedIn : (bindScalar context "previous_evaluator_id" (runType "uint64_t") (.u64 previous)) "published_before".toList =
      some (.scalar (runType "CettaCount") (some (.u64 published))) := by
    unfold bindScalar
    rewrite [Function.update_of_ne distinct_publishedIn]
    exact knownPublished
  have bindIn : (bindScalar context "previous_evaluator_id" (runType "uint64_t") (.u64 previous)) "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList =
      some (.scalar (runType "int") (some (.i32 262))) := by
    unfold bindScalar
    rewrite [Function.update_of_ne distinct_bindIn]
    exact knownBind
  have callIn : (bindScalar context "previous_evaluator_id" (runType "uint64_t") (.u64 previous)) "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList =
      some (.scalar (runType "int") (some (.i32 263))) := by
    unfold bindScalar
    rewrite [Function.update_of_ne distinct_callIn]
    exact knownCall
  have normalizeIn : (bindScalar context "previous_evaluator_id" (runType "uint64_t") (.u64 previous)) "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList =
      some (.scalar (runType "int") (some (.i32 264))) := by
    unfold bindScalar
    rewrite [Function.update_of_ne distinct_normalizeIn]
    exact knownNormalize
  have capacityIn : (bindScalar context "previous_evaluator_id" (runType "uint64_t") (.u64 previous)) "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4))) := by
    unfold bindScalar
    rewrite [Function.update_of_ne distinct_capacityIn]
    exact knownCapacity
  have outsideIn : (bindScalar context "previous_evaluator_id" (runType "uint64_t") (.u64 previous)) "g_prime_need_evaluator_id".toList = none := by
    unfold bindScalar
    rewrite [Function.update_of_ne distinct_outsideIn]
    exact outside
  have previousIn : (bindScalar context "previous_evaluator_id" (runType "uint64_t") (.u64 previous)) "previous_evaluator_id".toList =
      some (.scalar (runType "uint64_t") (some (.u64 previous))) := by
    unfold bindScalar
    exact Function.update_self _ _ _
  exact installed_evaluator_keeps_complete_readout operations layout (bindScalar context "previous_evaluator_id" (runType "uint64_t") (.u64 previous)) driver task
    previous published fuel previousIn driverIn taskIn publishedIn bindIn callIn
    normalizeIn capacityIn outsideIn (StatementBlock.ObjectBindings.restore
      "previous_evaluator_id".toList (context "previous_evaluator_id".toList))


/-- Saving, installing and restoring the evaluator word preserves the
complete source continuation, including unknown-kind fallthrough. -/
private theorem evaluator_scope_keeps_complete_continuation (operations : Operations) (layout : RunLayout)
    (context : Context) (driver : Option Ptr) (task : Ptr) (published : UInt64) (fuel : Nat)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (knownPublished : context "published_before".toList =
      some (.scalar (runType "CettaCount") (some (.u64 published))))
    (knownBind : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList =
      some (.scalar (runType "int") (some (.i32 262))))
    (knownCall : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList =
      some (.scalar (runType "int") (some (.i32 263))))
    (knownNormalize : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList =
      some (.scalar (runType "int") (some (.i32 264))))
    (knownCapacity : context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4))))
    (outside : context "g_prime_need_evaluator_id".toList = none) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 9)
      context evaluatorStatements = evaluatorBody operations layout context driver task published := by
  have statementsEq : evaluatorStatements =
      .declare (runType "uint64_t") "previous_evaluator_id".toList
        (TaskAdmission.ident "g_prime_need_evaluator_id") :: installedEvaluatorStatements := rfl
  rewrite [statementsEq, StatementBlock.scoped_initialized_declaration_keeps_continuation]
  have provider : (services operations layout).declaration =
      StatementBlock.ObjectBindings.declaration (profile operations layout) operations.region := rfl
  rewrite [provider,
    previous_evaluator_declaration_keeps_read_and_scope operations layout context outside]
  unfold evaluatorBody
  apply congrArg (fun next => CProg.loadU64 layout.evaluatorId >>= next)
  funext previous
  exact saved_evaluator_suffix_keeps_flow_readout operations layout context driver task published fuel
    knownDriver knownTask knownPublished knownBind knownCall knownNormalize knownCapacity outside previous


private theorem object_slot_keeps_other (context : Context) (slot name : String)
    (type : CType) (address : Ptr) (distinct : name ≠ slot) :
    (bindObject context slot type address) name.toList = context name.toList := by
  unfold bindObject
  apply Function.update_of_ne
  intro same
  exact distinct (String.toList_inj.mp same)

private def needStatements : List CStatement :=
  .declareCleanup (runType "PrimeNeedActiveGuard") "need_guard".toList (some needInitializer)
    "prime_need_active_leave".toList :: evaluatorStatements

private theorem need_is_actual_source_suffix :
    runSyntax.body.drop 11 = needStatements := rfl

/-- Need introduction retains the complete initialized guard, callback and
unprojected continuation, before lexical restoration. -/
private theorem need_declaration_keeps_entire_guard (operations : Operations) (layout : RunLayout)
    (context : Context) (task : Ptr)
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (continuation : Context → CProg CVal (ReadBlock.Result Context)) :
    StatementBlock.ObjectBindings.declarationCleanup (profile operations layout)
      operations.region (cleanup operations layout) emptyLayout context
      (runType "PrimeNeedActiveGuard") "need_guard".toList (some needInitializer)
      "prime_need_active_leave".toList continuation =
      (StatementBlock.AutomaticRegion.withCleanup operations.region
        (fun _ address _ _ => operations.needLeave address)
        "need_guard".toList layout.needCells (fun guard => do
          let fields ← operations.needEnter (task + layout.taskOffset "dynamic_env".toList)
          if fields.length = layout.needCells then CProg.initializeCells guard fields
          else CProg.undefined
          continuation (bindObject context "need_guard" (runType "PrimeNeedActiveGuard") guard)) >>=
        fun result => pure (StatementBlock.ObjectBindings.restore "need_guard".toList
          (context "need_guard".toList) result)) := by
  rewrite [StatementBlock.ObjectBindings.cleanup_declaration_keeps_region_and_callback
    (profile operations layout) operations.region (cleanup operations layout) emptyLayout context
    (runType "PrimeNeedActiveGuard") "need_guard".toList "prime_need_active_leave".toList
    (some needInitializer) layout.needCells (by rfl)]
  rewrite [StatementBlock.ObjectBindings.initialized_record_keeps_initializer_region_and_flow
    (profile operations layout)
    (StatementBlock.AutomaticRegion.withCleanup operations.region
      (fun _ address _ flow => cleanup operations layout "prime_need_active_leave".toList address flow))
    emptyLayout context (runType "PrimeNeedActiveGuard") "need_guard".toList layout.needCells
    needInitializer (by rfl)]
  apply congrArg (fun body =>
    StatementBlock.AutomaticRegion.withCleanup operations.region
      (fun _ address _ _ => operations.needLeave address)
      "need_guard".toList layout.needCells body >>= fun result =>
        pure (StatementBlock.ObjectBindings.restore "need_guard".toList
          (context "need_guard".toList) result))
  funext guard
  have taskIn : (bindObject context "need_guard" (runType "PrimeNeedActiveGuard") guard)
      "task".toList = some (.object (runType "PrimeEvalStackTask") task) :=
    (object_slot_keeps_other context "need_guard" "task" _ guard (by decide)).trans knownTask
  change (StatementBlock.ObjectBindings.initializeRecord (profile operations layout) emptyLayout
    (bindObject context "need_guard" (runType "PrimeNeedActiveGuard") guard)
    (runType "PrimeNeedActiveGuard") layout.needCells guard needInitializer >>= fun _ =>
      continuation (bindObject context "need_guard" (runType "PrimeNeedActiveGuard") guard)) = _
  rewrite [need_initializer_retains_every_guard_cell operations layout
    (bindObject context "need_guard" (runType "PrimeNeedActiveGuard") guard) task guard taskIn]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext fields
  split <;> rfl

/-- The full ordinary Need guard is initialized in its own automatic region.
Its cleanup follows evaluator restoration and Task retirement, before lexical
restoration and automatic-region exit. Every guard cell remains in the tree. -/
private theorem need_scope_keeps_full_guard_and_flow (operations : Operations) (layout : RunLayout)
    (context : Context) (driver : Option Ptr) (task : Ptr) (published : UInt64) (fuel : Nat)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (knownPublished : context "published_before".toList =
      some (.scalar (runType "CettaCount") (some (.u64 published))))
    (knownBind : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList =
      some (.scalar (runType "int") (some (.i32 262))))
    (knownCall : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList =
      some (.scalar (runType "int") (some (.i32 263))))
    (knownNormalize : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList =
      some (.scalar (runType "int") (some (.i32 264))))
    (knownCapacity : context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4))))
    (outside : context "g_prime_need_evaluator_id".toList = none) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 10)
      context needStatements = needBody operations layout context driver task published := by
  unfold needStatements
  rewrite [StatementBlock.scoped_cleanup_declaration_retains_provider]
  have provider : (services operations layout).declarationCleanup =
      StatementBlock.ObjectBindings.declarationCleanup (profile operations layout)
        operations.region (cleanup operations layout) := rfl
  rewrite [provider, need_declaration_keeps_entire_guard operations layout context task knownTask]
  unfold needBody
  apply congrArg (fun body => StatementBlock.AutomaticRegion.withCleanup operations.region
    (fun _ address _ _ => operations.needLeave address) "need_guard".toList layout.needCells body >>=
      fun result => pure (StatementBlock.ObjectBindings.restore "need_guard".toList
        (context "need_guard".toList) result))
  funext guard
  have driverIn : (bindObject context "need_guard" (runType "PrimeNeedActiveGuard") guard)
      "driver".toList = some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))) :=
    (object_slot_keeps_other context "need_guard" "driver" _ guard (by decide)).trans knownDriver
  have taskIn : (bindObject context "need_guard" (runType "PrimeNeedActiveGuard") guard)
      "task".toList = some (.object (runType "PrimeEvalStackTask") task) :=
    (object_slot_keeps_other context "need_guard" "task" _ guard (by decide)).trans knownTask
  have publishedIn : (bindObject context "need_guard" (runType "PrimeNeedActiveGuard") guard)
      "published_before".toList = some (.scalar (runType "CettaCount") (some (.u64 published))) :=
    (object_slot_keeps_other context "need_guard" "published_before" _ guard (by decide)).trans knownPublished
  have bindIn : (bindObject context "need_guard" (runType "PrimeNeedActiveGuard") guard)
      "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList = some (.scalar (runType "int") (some (.i32 262))) :=
    (object_slot_keeps_other context "need_guard" "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND" _ guard (by decide)).trans knownBind
  have callIn : (bindObject context "need_guard" (runType "PrimeNeedActiveGuard") guard)
      "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList = some (.scalar (runType "int") (some (.i32 263))) :=
    (object_slot_keeps_other context "need_guard" "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL" _ guard (by decide)).trans knownCall
  have normalizeIn : (bindObject context "need_guard" (runType "PrimeNeedActiveGuard") guard)
      "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList = some (.scalar (runType "int") (some (.i32 264))) :=
    (object_slot_keeps_other context "need_guard" "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE" _ guard (by decide)).trans knownNormalize
  have capacityIn : (bindObject context "need_guard" (runType "PrimeNeedActiveGuard") guard)
      "CETTA_EVAL_INCOMPLETE_CAPACITY".toList = some (.scalar (runType "int") (some (.i32 4))) :=
    (object_slot_keeps_other context "need_guard" "CETTA_EVAL_INCOMPLETE_CAPACITY" _ guard (by decide)).trans knownCapacity
  have outsideIn : (bindObject context "need_guard" (runType "PrimeNeedActiveGuard") guard)
      "g_prime_need_evaluator_id".toList = none :=
    (object_slot_keeps_other context "need_guard" "g_prime_need_evaluator_id" _ guard (by decide)).trans outside
  apply congrArg (fun next : CProg CVal (ReadBlock.Result Context) => operations.needEnter
    (task + layout.taskOffset "dynamic_env".toList) >>= fun fields =>
      if fields.length = layout.needCells then
        CProg.initializeCells guard fields >>= fun _ => next
      else CProg.undefined >>= fun _ => next)
  exact evaluator_scope_keeps_complete_continuation operations layout
    (bindObject context "need_guard" (runType "PrimeNeedActiveGuard") guard) driver task published fuel
    driverIn taskIn publishedIn bindIn callIn normalizeIn capacityIn outsideIn


private def publishedInitializer : CExpr :=
  .conditional (TaskAdmission.taskField "target")
    (.field (TaskAdmission.taskField "target") "len".toList true) (.unsignedInteger 0)

/-- The initial wide count retains both authored target reads. Scalar alias
conversion preserves the wide result and the unsigned zero branch. -/
private theorem published_initializer_keeps_actual_wide_count (operations : Operations)
    (layout : RunLayout) (context : Context) (task : Ptr)
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task)) :
    (runRead operations layout context publishedInitializer >>= fun value =>
      StatementBlock.ObjectBindings.scalarInitialValue (profile operations layout)
        (runType "CettaCount") value) =
      (publicationStart layout task >>= fun value => pure (.u64 value)) := by
  unfold publishedInitializer
  rewrite [runRead, StatementBlock.ObjectBindings.read, expressionWithNames.eq_def]
  change ((runRead operations layout context (TaskAdmission.taskField "target") >>= fun target =>
    truth target >>= fun present =>
      if present then runRead operations layout context
        (.field (TaskAdmission.taskField "target") "len".toList true)
      else runRead operations layout context (.unsignedInteger 0)) >>= fun value =>
    StatementBlock.ObjectBindings.scalarInitialValue (profile operations layout)
      (runType "CettaCount") value) = _
  rewrite [task_field_read operations layout context task "target" knownTask]
  unfold publicationStart taskRead
  rewrite [pointer_field_uses_actual_offset _ task "target".toList _ (by rfl)]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, truth]
  congr 1
  funext target
  congr 1
  funext absent
  cases absent
  · simp only [Bool.not_false, ↓reduceIte]
    rewrite [target_length_read operations layout context task knownTask]
    unfold taskRead
    rewrite [pointer_field_uses_actual_offset _ task "target".toList _ (by rfl)]
    simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
    congr 1
    funext owner
    cases owner with
    | none =>
      rewrite [null_owner_field_is_undefined]
      exact (undefined_bind _).trans (undefined_bind _).symm
    | some owner =>
      rewrite [word64_field_uses_actual_offset _ owner "len".toList _ (by rfl)]
      simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
      congr 1
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl


/-- Scalar introduction keeps the current target's initial wide count and
its complete continuation before restoring any prior local count binding. -/
private theorem published_declaration_keeps_read_and_scope (operations : Operations)
    (layout : RunLayout) (context : Context) (task : Ptr)
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (continuation : Context → CProg CVal (ReadBlock.Result Context)) :
    StatementBlock.ObjectBindings.declaration (profile operations layout) operations.region
      emptyLayout context (runType "CettaCount") "published_before".toList
      (some publishedInitializer) continuation =
      (do
        let published ← publicationStart layout task
        let result ← continuation
          (bindScalar context "published_before" (runType "CettaCount") (.u64 published))
        pure (StatementBlock.ObjectBindings.restore "published_before".toList
          (context "published_before".toList) result)) := by
  rewrite [StatementBlock.ObjectBindings.initialized_scalar_keeps_read_conversion_and_flow
    (profile operations layout) operations.region emptyLayout context (runType "CettaCount")
    "published_before".toList publishedInitializer (by rfl)]
  have initializer := published_initializer_keeps_actual_wide_count operations layout context task knownTask
  change (StatementBlock.ObjectBindings.read (profile operations layout) emptyLayout context
    publishedInitializer >>= fun value =>
      StatementBlock.ObjectBindings.scalarInitialValue (profile operations layout)
        (runType "CettaCount") value) = _ at initializer
  have joined := congrArg (fun input : CProg CVal CVal => input >>= fun value =>
    continuation (Function.update context "published_before".toList
      (some (.scalar (runType "CettaCount") (some value)))) >>= fun result =>
        pure (StatementBlock.ObjectBindings.restore "published_before".toList
          (context "published_before".toList) result)) initializer
  simpa only [bindScalar, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind] using joined


private theorem scalar_slot_keeps_other (context : Context) (slot name : String)
    (type : CType) (value : CVal) (distinct : name ≠ slot) :
    (bindScalar context slot type value) name.toList = context name.toList := by
  unfold bindScalar
  apply Function.update_of_ne
  intro same
  exact distinct (String.toList_inj.mp same)


private def publishedStatements : List CStatement :=
  .declare (runType "CettaCount") "published_before".toList publishedInitializer :: needStatements

private theorem publication_is_actual_source_suffix :
    runSyntax.body.drop 10 = publishedStatements := rfl

/-- Publication initialization, Need cleanup and the saved evaluator scope
compose on the complete flow without erasing any local binding early. -/
private theorem publication_scope_keeps_complete_continuation (operations : Operations)
    (layout : RunLayout) (context : Context) (driver : Option Ptr) (task : Ptr) (fuel : Nat)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (knownBind : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList =
      some (.scalar (runType "int") (some (.i32 262))))
    (knownCall : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList =
      some (.scalar (runType "int") (some (.i32 263))))
    (knownNormalize : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList =
      some (.scalar (runType "int") (some (.i32 264))))
    (knownCapacity : context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4))))
    (outside : context "g_prime_need_evaluator_id".toList = none) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 11)
      context publishedStatements = publishedBody operations layout context driver task := by
  unfold publishedStatements
  rewrite [StatementBlock.scoped_initialized_declaration_keeps_continuation]
  have provider : (services operations layout).declaration =
      StatementBlock.ObjectBindings.declaration (profile operations layout) operations.region := rfl
  rewrite [provider, published_declaration_keeps_read_and_scope operations layout context task knownTask]
  unfold publishedBody
  apply congrArg (fun next => publicationStart layout task >>= next)
  funext published
  have driverIn : (bindScalar context "published_before" (runType "CettaCount") (.u64 published))
      "driver".toList = some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))) :=
    (scalar_slot_keeps_other context "published_before" "driver" _ _ (by decide)).trans knownDriver
  have taskIn : (bindScalar context "published_before" (runType "CettaCount") (.u64 published))
      "task".toList = some (.object (runType "PrimeEvalStackTask") task) :=
    (scalar_slot_keeps_other context "published_before" "task" _ _ (by decide)).trans knownTask
  have bindIn : (bindScalar context "published_before" (runType "CettaCount") (.u64 published))
      "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList = some (.scalar (runType "int") (some (.i32 262))) :=
    (scalar_slot_keeps_other context "published_before" "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND" _ _ (by decide)).trans knownBind
  have callIn : (bindScalar context "published_before" (runType "CettaCount") (.u64 published))
      "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList = some (.scalar (runType "int") (some (.i32 263))) :=
    (scalar_slot_keeps_other context "published_before" "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL" _ _ (by decide)).trans knownCall
  have normalizeIn : (bindScalar context "published_before" (runType "CettaCount") (.u64 published))
      "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList = some (.scalar (runType "int") (some (.i32 264))) :=
    (scalar_slot_keeps_other context "published_before" "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE" _ _ (by decide)).trans knownNormalize
  have capacityIn : (bindScalar context "published_before" (runType "CettaCount") (.u64 published))
      "CETTA_EVAL_INCOMPLETE_CAPACITY".toList = some (.scalar (runType "int") (some (.i32 4))) :=
    (scalar_slot_keeps_other context "published_before" "CETTA_EVAL_INCOMPLETE_CAPACITY" _ _ (by decide)).trans knownCapacity
  have outsideIn : (bindScalar context "published_before" (runType "CettaCount") (.u64 published))
      "g_prime_need_evaluator_id".toList = none :=
    (scalar_slot_keeps_other context "published_before" "g_prime_need_evaluator_id" _ _ (by decide)).trans outside
  have publishedIn : (bindScalar context "published_before" (runType "CettaCount") (.u64 published))
      "published_before".toList = some (.scalar (runType "CettaCount") (some (.u64 published))) := by
    unfold bindScalar
    exact Function.update_self _ _ _
  have agreement := need_scope_keeps_full_guard_and_flow operations layout
    (bindScalar context "published_before" (runType "CettaCount") (.u64 published)) driver task published fuel
    driverIn taskIn publishedIn bindIn callIn normalizeIn capacityIn outsideIn
  exact congrArg (fun program : CProg CVal (ReadBlock.Result Context) => program >>= fun result =>
    pure (StatementBlock.ObjectBindings.restore "published_before".toList
      (context "published_before".toList) result)) agreement


private theorem queued_task_address_keeps_driver_place (operations : Operations)
    (layout : RunLayout) (context : Context) (driver : Option Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver)))) :
    runRead operations layout context (.unary .address (TaskAdmission.driverField "task")) =
      (driverPlace layout driver "task" >>= fun address => pure (.ptr (some address))) := by
  rewrite [runRead, StatementBlock.ObjectBindings.read,
    TaskAdmission.driverField, TaskAdmission.ident, expressionWithNames.eq_def]
  change (runRead operations layout context (.identifier "driver".toList) >>= fun owner =>
    fieldAddress ((StatementBlock.ObjectBindings.objects (profile operations layout) context).fieldLayout
      emptyLayout (.identifier "driver".toList) true) owner "task".toList >>= fun address =>
        pure (CVal.ptr (some address))) = _
  rewrite [local_read operations layout context "driver".toList _ (.ptr driver) knownDriver,
    StatementBlock.ObjectBindings.local_pointer_keeps_field_inventory
      (profile operations layout) emptyLayout context (recordLayouts layout)
      "driver".toList "PrimeEvalStackDriver".toList 0 driver (by rfl) knownDriver]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rfl

private theorem queued_task_size_keeps_static_extent (operations : Operations) (layout : RunLayout)
    (context : Context) (driver : Option Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver)))) :
    runRead operations layout context (.sizeOfExpr (TaskAdmission.driverField "task")) =
      pure (.u64 (UInt64.ofNat layout.taskBytes)) := by
  change resolved (StatementBlock.ObjectBindings.size (profile operations layout) context
    (.sizeOfExpr (TaskAdmission.driverField "task"))) = _
  have inferred : ScalarBytes.typeOf?
      (StatementBlock.ObjectBindings.types context (profile operations layout).outsideTypes)
      (TaskAdmission.driverField "task") (profile operations layout).fieldTypes =
        some (runType "PrimeEvalStackTask") := by
    simp only [TaskAdmission.driverField, TaskAdmission.ident, ScalarBytes.typeOf?,
      StatementBlock.ObjectBindings.types, knownDriver, bind, Option.bind_some]
    rfl
  simp only [StatementBlock.ObjectBindings.size, inferred, bind, Option.bind_some]
  change resolved (if layout.taskBytes < 2 ^ 64 then
    some (CVal.u64 (UInt64.ofNat layout.taskBytes)) else none) = _
  simp only [layout.taskBytesBound, ↓reduceIte, resolved]

private theorem queued_task_zero_keeps_actual_place_and_bytes (operations : Operations)
    (layout : RunLayout) (context : Context) (driver : Option Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver)))) :
    (services operations layout).effect emptyLayout context (.call "memset".toList
      [.unary .address (TaskAdmission.driverField "task"), .decimal 0,
       .sizeOfExpr (TaskAdmission.driverField "task")]) =
      (driverPlace layout driver "task" >>= fun address =>
        operations.zeroTask address (UInt64.ofNat layout.taskBytes)) := by
  rewrite [effect_keeps_arguments operations layout context "memset".toList _ (by decide)]
  simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  change (runRead operations layout context (.unary .address (TaskAdmission.driverField "task")) >>=
    fun address => runRead operations layout context (.decimal 0) >>= fun zero =>
      runRead operations layout context (.sizeOfExpr (TaskAdmission.driverField "task")) >>= fun bytes =>
        effects operations "memset".toList [address, zero, bytes]) = _
  rewrite [queued_task_address_keeps_driver_place operations layout context driver knownDriver,
    queued_task_size_keeps_static_extent operations layout context driver knownDriver]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1

private theorem running_task_introduction_keeps_true_write (operations : Operations)
    (layout : RunLayout) (context : Context) (driver : Option Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver)))) :
    (services operations layout).assignment emptyLayout context
      (.assign (TaskAdmission.driverField "running_task") (.bool true)) =
      (driverStore layout driver "running_task" (.bool true) >>= fun _ => pure context) :=
  driver_assignment operations layout context driver "running_task" (runType "bool")
    (.bool true) (.bool true) knownDriver (by rfl) (by rfl) (by rfl) (by rfl)

private theorem ready_task_consumption_keeps_false_write (operations : Operations)
    (layout : RunLayout) (context : Context) (driver : Option Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver)))) :
    (services operations layout).assignment emptyLayout context
      (.assign (TaskAdmission.driverField "task_ready") (.bool false)) =
      (driverStore layout driver "task_ready" (.bool false) >>= fun _ => pure context) :=
  driver_assignment operations layout context driver "task_ready" (runType "bool")
    (.bool false) (.bool false) knownDriver (by rfl) (by rfl) (by rfl) (by rfl)

private theorem active_task_introduction_keeps_local_address (operations : Operations)
    (layout : RunLayout) (context : Context) (driver : Option Ptr) (task : Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task)) :
    (services operations layout).assignment emptyLayout context
      (.assign (TaskAdmission.driverField "active_task")
        (.unary .address (TaskAdmission.ident "task"))) =
      (driverStore layout driver "active_task" (.ptr (some task)) >>= fun _ => pure context) := by
  apply driver_assignment operations layout context driver "active_task" (runType "PrimeEvalStackTask" 1)
    (.unary .address (TaskAdmission.ident "task")) (.ptr (some task)) knownDriver
    (by rfl) (by rfl) (by rfl)
  exact StatementBlock.ObjectBindings.local_object_address_does_not_read_value
    (profile operations layout) emptyLayout context "task".toList
    (runType "PrimeEvalStackTask") task knownTask


private def preparationStatements : List CStatement :=
  [.assign (TaskAdmission.driverField "task_ready") (.bool false),
   .assign (TaskAdmission.driverField "active_task") (.unary .address (TaskAdmission.ident "task")),
   .assign (TaskAdmission.driverField "running_task") (.bool true)]

private def preparationAssignments (layout : RunLayout) (driver : Option Ptr) (task : Ptr) :
    List ((CExpr × CExpr) × CProg CVal Unit) :=
  [((TaskAdmission.driverField "task_ready", .bool false),
      driverStore layout driver "task_ready" (.bool false)),
   ((TaskAdmission.driverField "active_task", .unary .address (TaskAdmission.ident "task")),
      driverStore layout driver "active_task" (.ptr (some task))),
   ((TaskAdmission.driverField "running_task", .bool true),
      driverStore layout driver "running_task" (.bool true))]

private theorem preparation_assignments_keep_complete_context (operations : Operations)
    (layout : RunLayout) (context : Context) (driver : Option Ptr) (task : Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task)) :
    ∀ entry ∈ preparationAssignments layout driver task,
      (services operations layout).assignment emptyLayout context (.assign entry.1.1 entry.1.2) =
        (entry.2 >>= fun _ => pure context) := by
  intro entry member
  unfold preparationAssignments at member
  rcases List.mem_cons.mp member with same | member
  · subst entry
    exact ready_task_consumption_keeps_false_write operations layout context driver knownDriver
  · rcases List.mem_cons.mp member with same | member
    · subst entry
      exact active_task_introduction_keeps_local_address operations layout context driver task knownDriver knownTask
    · have same := List.mem_singleton.mp member
      subst entry
      exact running_task_introduction_keeps_true_write operations layout context driver knownDriver

private theorem preparation_writes_keep_original_order (operations : Operations)
    (layout : RunLayout) (context : Context) (driver : Option Ptr) (task : Ptr) (fuel : Nat)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task)) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 14)
      context (preparationStatements ++ publishedStatements) =
      (driverStore layout driver "task_ready" (.bool false) >>= fun _ =>
        driverStore layout driver "active_task" (.ptr (some task)) >>= fun _ =>
          driverStore layout driver "running_task" (.bool true) >>= fun _ =>
            StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 11)
              context publishedStatements) := by
  have agreement := StatementBlock.scoped_assignment_prefix_keeps_operations
    (services operations layout) emptyLayout 0 (fuel + 11) context
    (preparationAssignments layout driver task) publishedStatements
    (preparation_assignments_keep_complete_context operations layout context driver task knownDriver knownTask)
  exact agreement


private def prepareStatements : List CStatement :=
  .effect (.call "memset".toList [.unary .address (TaskAdmission.driverField "task"),
    .decimal 0, .sizeOfExpr (TaskAdmission.driverField "task")]) ::
      (preparationStatements ++ publishedStatements)

private theorem preparation_is_actual_source_suffix :
    runSyntax.body.drop 6 = prepareStatements := rfl

/-- Clearing the original queued record, installing the copied Task as active
and publication/Need scopes keep their exact source order and full flow. -/
private theorem prepare_scope_keeps_complete_continuation (operations : Operations)
    (layout : RunLayout) (context : Context) (driver : Option Ptr) (task : Ptr) (fuel : Nat)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (knownBind : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList =
      some (.scalar (runType "int") (some (.i32 262))))
    (knownCall : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList =
      some (.scalar (runType "int") (some (.i32 263))))
    (knownNormalize : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList =
      some (.scalar (runType "int") (some (.i32 264))))
    (knownCapacity : context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4))))
    (outside : context "g_prime_need_evaluator_id".toList = none) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 15)
      context prepareStatements = prepareBody operations layout context driver task := by
  unfold prepareStatements
  rewrite [StatementBlock.scoped_effect_keeps_continuation,
    queued_task_zero_keeps_actual_place_and_bytes operations layout context driver knownDriver]
  rewrite [preparation_writes_keep_original_order operations layout context driver task fuel knownDriver knownTask,
    publication_scope_keeps_complete_continuation operations layout context driver task fuel
      knownDriver knownTask knownBind knownCall knownNormalize knownCapacity outside]
  simp only [Prog.bind_eq, Prog.bind_assoc, prepareBody]

/-- Authority introduction keeps the two complete saved cells, Boolean input,
cleanup and the entire inner scope before restoring the old local binding. -/
private theorem authority_declaration_keeps_both_saved_cells (operations : Operations)
    (layout : RunLayout) (context : Context) (task : Ptr)
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (continuation : Context → CProg CVal (ReadBlock.Result Context)) :
    StatementBlock.ObjectBindings.declarationCleanup (profile operations layout)
      operations.region (cleanup operations layout) emptyLayout context
      (runType "PrimeEvalAuthorityGuard") "authority".toList (some authorityInitializer)
      "prime_eval_authority_leave".toList continuation =
      (StatementBlock.AutomaticRegion.withCleanup operations.region
        (fun _ address _ _ => Authority.leave layout.authority address)
        "authority".toList 2 (fun guard => do
          let incoming ← CProg.loadBool (task + layout.taskOffset "pure_authority".toList)
          let fields ← Authority.enter layout.authority incoming
          if fields.length = 2 then CProg.initializeCells guard fields else CProg.undefined
          continuation (bindObject context "authority" (runType "PrimeEvalAuthorityGuard") guard)) >>=
        fun result => pure (StatementBlock.ObjectBindings.restore "authority".toList
          (context "authority".toList) result)) := by
  rewrite [StatementBlock.ObjectBindings.cleanup_declaration_keeps_region_and_callback
    (profile operations layout) operations.region (cleanup operations layout) emptyLayout context
    (runType "PrimeEvalAuthorityGuard") "authority".toList "prime_eval_authority_leave".toList
    (some authorityInitializer) 2 (by rfl)]
  rewrite [StatementBlock.ObjectBindings.initialized_record_keeps_initializer_region_and_flow
    (profile operations layout)
    (StatementBlock.AutomaticRegion.withCleanup operations.region
      (fun _ address _ flow => cleanup operations layout "prime_eval_authority_leave".toList address flow))
    emptyLayout context (runType "PrimeEvalAuthorityGuard") "authority".toList 2
    authorityInitializer (by rfl)]
  apply congrArg (fun body =>
    StatementBlock.AutomaticRegion.withCleanup operations.region
      (fun _ address _ _ => Authority.leave layout.authority address)
      "authority".toList 2 body >>= fun result =>
        pure (StatementBlock.ObjectBindings.restore "authority".toList
          (context "authority".toList) result))
  funext guard
  have taskIn : (bindObject context "authority" (runType "PrimeEvalAuthorityGuard") guard)
      "task".toList = some (.object (runType "PrimeEvalStackTask") task) :=
    (object_slot_keeps_other context "authority" "task" _ guard (by decide)).trans knownTask
  change (StatementBlock.ObjectBindings.initializeRecord (profile operations layout) emptyLayout
    (bindObject context "authority" (runType "PrimeEvalAuthorityGuard") guard)
    (runType "PrimeEvalAuthorityGuard") 2 guard authorityInitializer >>= fun _ =>
      continuation (bindObject context "authority" (runType "PrimeEvalAuthorityGuard") guard)) = _
  rewrite [authority_initializer_retains_both_saved_cells operations layout
    (bindObject context "authority" (runType "PrimeEvalAuthorityGuard") guard) task guard taskIn]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  congr 1
  funext incoming
  congr 1
  funext fields
  split <;> rfl


private def authorityStatements : List CStatement :=
  .declareCleanup (runType "PrimeEvalAuthorityGuard") "authority".toList (some authorityInitializer)
    "prime_eval_authority_leave".toList :: prepareStatements

private theorem authority_is_actual_source_suffix :
    runSyntax.body.drop 5 = authorityStatements := rfl

/-- The complete saved authority region surrounds all preparation, dispatch,
Task retirement and Need cleanup; its own cleanup remains last in that scope. -/
private theorem authority_scope_keeps_complete_continuation (operations : Operations)
    (layout : RunLayout) (context : Context) (driver : Option Ptr) (task : Ptr) (fuel : Nat)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownTask : context "task".toList = some (.object (runType "PrimeEvalStackTask") task))
    (knownBind : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList =
      some (.scalar (runType "int") (some (.i32 262))))
    (knownCall : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList =
      some (.scalar (runType "int") (some (.i32 263))))
    (knownNormalize : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList =
      some (.scalar (runType "int") (some (.i32 264))))
    (knownCapacity : context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4))))
    (outside : context "g_prime_need_evaluator_id".toList = none) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 16)
      context authorityStatements = authorityBody operations layout context driver task := by
  unfold authorityStatements
  rewrite [StatementBlock.scoped_cleanup_declaration_retains_provider]
  have provider : (services operations layout).declarationCleanup =
      StatementBlock.ObjectBindings.declarationCleanup (profile operations layout)
        operations.region (cleanup operations layout) := rfl
  rewrite [provider, authority_declaration_keeps_both_saved_cells operations layout context task knownTask]
  unfold authorityBody
  apply congrArg (fun body => StatementBlock.AutomaticRegion.withCleanup operations.region
    (fun _ address _ _ => Authority.leave layout.authority address) "authority".toList 2 body >>=
      fun result => pure (StatementBlock.ObjectBindings.restore "authority".toList
        (context "authority".toList) result))
  funext guard
  have driverIn : (bindObject context "authority" (runType "PrimeEvalAuthorityGuard") guard)
      "driver".toList = some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))) :=
    (object_slot_keeps_other context "authority" "driver" _ guard (by decide)).trans knownDriver
  have taskIn : (bindObject context "authority" (runType "PrimeEvalAuthorityGuard") guard)
      "task".toList = some (.object (runType "PrimeEvalStackTask") task) :=
    (object_slot_keeps_other context "authority" "task" _ guard (by decide)).trans knownTask
  have bindIn : (bindObject context "authority" (runType "PrimeEvalAuthorityGuard") guard)
      "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList = some (.scalar (runType "int") (some (.i32 262))) :=
    (object_slot_keeps_other context "authority" "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND" _ guard (by decide)).trans knownBind
  have callIn : (bindObject context "authority" (runType "PrimeEvalAuthorityGuard") guard)
      "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList = some (.scalar (runType "int") (some (.i32 263))) :=
    (object_slot_keeps_other context "authority" "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL" _ guard (by decide)).trans knownCall
  have normalizeIn : (bindObject context "authority" (runType "PrimeEvalAuthorityGuard") guard)
      "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList = some (.scalar (runType "int") (some (.i32 264))) :=
    (object_slot_keeps_other context "authority" "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE" _ guard (by decide)).trans knownNormalize
  have capacityIn : (bindObject context "authority" (runType "PrimeEvalAuthorityGuard") guard)
      "CETTA_EVAL_INCOMPLETE_CAPACITY".toList = some (.scalar (runType "int") (some (.i32 4))) :=
    (object_slot_keeps_other context "authority" "CETTA_EVAL_INCOMPLETE_CAPACITY" _ guard (by decide)).trans knownCapacity
  have outsideIn : (bindObject context "authority" (runType "PrimeEvalAuthorityGuard") guard)
      "g_prime_need_evaluator_id".toList = none :=
    (object_slot_keeps_other context "authority" "g_prime_need_evaluator_id" _ guard (by decide)).trans outside
  apply congrArg (fun next : CProg CVal (ReadBlock.Result Context) =>
    CProg.loadBool (task + layout.taskOffset "pure_authority".toList) >>= fun incoming =>
      Authority.enter layout.authority incoming >>= fun fields =>
        if fields.length = 2 then CProg.initializeCells guard fields >>= fun _ => next
        else CProg.undefined >>= fun _ => next)
  exact prepare_scope_keeps_complete_continuation operations layout
    (bindObject context "authority" (runType "PrimeEvalAuthorityGuard") guard) driver task fuel
    driverIn taskIn bindIn callIn normalizeIn capacityIn outsideIn


/-- The full by-value Task initializer copies all cells from the queued record
before the automatic Task's complete inner continuation begins. -/
private theorem task_declaration_keeps_complete_copy (operations : Operations)
    (layout : RunLayout) (context : Context) (driver : Option Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (continuation : Context → CProg CVal (ReadBlock.Result Context)) :
    StatementBlock.ObjectBindings.declaration (profile operations layout) operations.region
      emptyLayout context (runType "PrimeEvalStackTask") "task".toList
      (some (TaskAdmission.driverField "task")) continuation =
      (operations.region "task".toList layout.taskCells (fun task => do
        let original ← driverPlace layout driver "task"
        CProg.copyCells original task layout.taskCells
        continuation (bindObject context "task" (runType "PrimeEvalStackTask") task)) >>=
          fun result => pure (StatementBlock.ObjectBindings.restore "task".toList
            (context "task".toList) result)) := by
  have sourceType : ∀ task : Ptr, ScalarBytes.typeOf?
      (StatementBlock.ObjectBindings.types
        (Function.update context "task".toList (some (.object (runType "PrimeEvalStackTask") task)))
        (profile operations layout).outsideTypes)
      (TaskAdmission.driverField "task") (profile operations layout).fieldTypes =
        some (runType "PrimeEvalStackTask") := by
    intro task
    have driverIn : (bindObject context "task" (runType "PrimeEvalStackTask") task)
        "driver".toList = some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))) :=
      (object_slot_keeps_other context "task" "driver" _ task (by decide)).trans knownDriver
    change ScalarBytes.typeOf? (StatementBlock.ObjectBindings.types
      (bindObject context "task" (runType "PrimeEvalStackTask") task)
      (profile operations layout).outsideTypes)
      (TaskAdmission.driverField "task") (profile operations layout).fieldTypes = _
    simp only [TaskAdmission.driverField, TaskAdmission.ident, ScalarBytes.typeOf?,
      StatementBlock.ObjectBindings.types, driverIn, bind, Option.bind_some]
    rfl
  rewrite [StatementBlock.ObjectBindings.initialized_record_keeps_scope_and_complete_copy
    (profile operations layout) operations.region emptyLayout context
    (runType "PrimeEvalStackTask") "task".toList layout.taskCells
    (TaskAdmission.driverField "task") (by rfl) sourceType]
  apply congrArg (fun body => operations.region "task".toList layout.taskCells body >>= fun result =>
    pure (StatementBlock.ObjectBindings.restore "task".toList (context "task".toList) result))
  funext task
  have driverIn : (bindObject context "task" (runType "PrimeEvalStackTask") task)
      "driver".toList = some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))) :=
    (object_slot_keeps_other context "task" "driver" _ task (by decide)).trans knownDriver
  change (StatementBlock.ObjectBindings.place (profile operations layout) emptyLayout
    (bindObject context "task" (runType "PrimeEvalStackTask") task)
    (TaskAdmission.driverField "task") >>= fun original =>
      CProg.copyCells original task layout.taskCells >>= fun _ =>
        continuation (bindObject context "task" (runType "PrimeEvalStackTask") task)) = _
  rewrite [driver_field_place operations layout
    (bindObject context "task" (runType "PrimeEvalStackTask") task) driver "task" driverIn]
  rfl


private def taskStatements : List CStatement :=
  .declare (runType "PrimeEvalStackTask") "task".toList (TaskAdmission.driverField "task") :: authorityStatements

private theorem task_is_actual_source_suffix :
    runSyntax.body.drop 4 = taskStatements := rfl

/-- By-value Task introduction preserves its complete cell snapshot, every
nested scope and the automatic region's inspection before lexical restoration. -/
private theorem task_scope_keeps_complete_continuation (operations : Operations)
    (layout : RunLayout) (context : Context) (driver : Option Ptr) (fuel : Nat)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownBind : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList =
      some (.scalar (runType "int") (some (.i32 262))))
    (knownCall : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList =
      some (.scalar (runType "int") (some (.i32 263))))
    (knownNormalize : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList =
      some (.scalar (runType "int") (some (.i32 264))))
    (knownCapacity : context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4))))
    (outside : context "g_prime_need_evaluator_id".toList = none) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 17)
      context taskStatements = taskBody operations layout context driver := by
  unfold taskStatements
  rewrite [StatementBlock.scoped_initialized_declaration_keeps_continuation]
  have provider : (services operations layout).declaration =
      StatementBlock.ObjectBindings.declaration (profile operations layout) operations.region := rfl
  rewrite [provider, task_declaration_keeps_complete_copy operations layout context driver knownDriver]
  unfold taskBody
  apply congrArg (fun body => operations.region "task".toList layout.taskCells body >>= fun result =>
    pure (StatementBlock.ObjectBindings.restore "task".toList (context "task".toList) result))
  funext task
  have driverIn : (bindObject context "task" (runType "PrimeEvalStackTask") task)
      "driver".toList = some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))) :=
    (object_slot_keeps_other context "task" "driver" _ task (by decide)).trans knownDriver
  have bindIn : (bindObject context "task" (runType "PrimeEvalStackTask") task)
      "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList = some (.scalar (runType "int") (some (.i32 262))) :=
    (object_slot_keeps_other context "task" "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND" _ task (by decide)).trans knownBind
  have callIn : (bindObject context "task" (runType "PrimeEvalStackTask") task)
      "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList = some (.scalar (runType "int") (some (.i32 263))) :=
    (object_slot_keeps_other context "task" "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL" _ task (by decide)).trans knownCall
  have normalizeIn : (bindObject context "task" (runType "PrimeEvalStackTask") task)
      "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList = some (.scalar (runType "int") (some (.i32 264))) :=
    (object_slot_keeps_other context "task" "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE" _ task (by decide)).trans knownNormalize
  have capacityIn : (bindObject context "task" (runType "PrimeEvalStackTask") task)
      "CETTA_EVAL_INCOMPLETE_CAPACITY".toList = some (.scalar (runType "int") (some (.i32 4))) :=
    (object_slot_keeps_other context "task" "CETTA_EVAL_INCOMPLETE_CAPACITY" _ task (by decide)).trans knownCapacity
  have outsideIn : (bindObject context "task" (runType "PrimeEvalStackTask") task)
      "g_prime_need_evaluator_id".toList = none :=
    (object_slot_keeps_other context "task" "g_prime_need_evaluator_id" _ task (by decide)).trans outside
  have taskIn : (bindObject context "task" (runType "PrimeEvalStackTask") task)
      "task".toList = some (.object (runType "PrimeEvalStackTask") task) := by
    unfold bindObject
    exact Function.update_self _ _ _
  apply congrArg (fun next : CProg CVal (ReadBlock.Result Context) =>
    driverPlace layout driver "task" >>= fun original =>
      CProg.copyCells original task layout.taskCells >>= fun _ => next)
  exact authority_scope_keeps_complete_continuation operations layout
    (bindObject context "task" (runType "PrimeEvalStackTask") task) driver task fuel
    driverIn taskIn bindIn callIn normalizeIn capacityIn outsideIn

private theorem assertion_keeps_macro_profile (operations : Operations) (layout : RunLayout)
    (context : Context) (operand : CExpr) :
    (services operations layout).effect emptyLayout context (.call "assert".toList [operand]) =
      (if operations.assertions then runRead operations layout context operand >>= fun value =>
        truth value >>= fun accepted => if accepted then pure () else CProg.undefined
       else pure ()) := by
  cases enabled : operations.assertions with
  | false =>
    change EffectStatements.withObjectMacros (profile operations layout) (effects operations)
      (omittedMacros operations) emptyLayout context (.call "assert".toList [operand]) = pure ()
    apply EffectStatements.omitted_macro_does_not_evaluate_arguments _ _ _ _ _ _ _ 1
    · simp only [omittedMacros, enabled]
      rfl
    · rfl
  | true =>
    change EffectStatements.withObjectMacros (profile operations layout) (effects operations)
      (omittedMacros operations) emptyLayout context (.call "assert".toList [operand]) =
        (runRead operations layout context operand >>= fun value =>
          truth value >>= fun accepted => if accepted then pure () else CProg.undefined)
    have ordinary : omittedMacros operations "assert".toList = none := by
      simp only [omittedMacros, enabled]
      rfl
    rewrite [EffectStatements.enabled_call_keeps_the_whole_argument_evaluation
      (profile operations layout) (effects operations) (omittedMacros operations)
      emptyLayout context "assert".toList [operand] ordinary]
    simp only [argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind,
      Prog.bind_assoc]
    rfl

private theorem driver_is_nonnull_read (operations : Operations) (layout : RunLayout)
    (context : Context) (driver : Option Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver)))) :
    runRead operations layout context (.binary .ne (.identifier "driver".toList) .null) =
      (CProg.ptrEq driver none >>= fun isNull => pure (.bool (!isNull))) := by
  change (runRead operations layout context (.identifier "driver".toList) >>= fun left =>
    pure (CVal.ptr none) >>= fun right => binary .ne left right) = _
  rewrite [local_read operations layout context "driver".toList _ _ knownDriver]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rfl

private def assertionStatements : List CStatement := [
  .effect (.call "assert".toList [.binary .ne (.identifier "driver".toList) .null]),
  .effect (.call "assert".toList [TaskAdmission.driverField "task_ready"]),
  .effect (.call "assert".toList [.unary .not (TaskAdmission.driverField "running_task")])]

private theorem assertions_are_actual_source_prefix :
    runSyntax.body.drop 1 = assertionStatements ++ taskStatements := rfl

private theorem assertion_effects_keep_original_order (operations : Operations) (layout : RunLayout)
    (context : Context) (driver : Option Ptr)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver)))) :
    ((services operations layout).effect emptyLayout context
        (.call "assert".toList [.binary .ne (.identifier "driver".toList) .null]) >>= fun _ =>
      (services operations layout).effect emptyLayout context
        (.call "assert".toList [TaskAdmission.driverField "task_ready"]) >>= fun _ =>
      (services operations layout).effect emptyLayout context
        (.call "assert".toList [.unary .not (TaskAdmission.driverField "running_task")])) =
        assertions operations layout driver := by
  rewrite [assertion_keeps_macro_profile, assertion_keeps_macro_profile,
    assertion_keeps_macro_profile]
  cases enabled : operations.assertions with
  | false =>
    simp only [enabled, assertions, Bool.false_eq_true, ↓reduceIte,
      Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  | true =>
    rewrite [driver_is_nonnull_read operations layout context driver knownDriver,
      driver_field_read operations layout context driver "task_ready" knownDriver,
      negated_read, driver_field_read operations layout context driver "running_task" knownDriver]
    simp only [enabled, assertions, ↓reduceIte,
      Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc, truth]
    apply congrArg (fun next => CProg.ptrEq driver none >>= next)
    funext isNull
    have failureBind {α β : Type} (next : α → CProg CVal β) :
        Prog.bind CProg.undefined next = CProg.undefined := undefined_bind next
    cases isNull with
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, failureBind]
    | false =>
      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, Prog.ret_bind]
      apply congrArg (fun next => driverRead layout driver "task_ready" >>= next)
      funext readyValue
      apply congrArg (fun next => truth readyValue >>= next)
      funext ready
      cases ready with
      | false => simp only [Bool.false_eq_true, ↓reduceIte, failureBind]
      | true =>
        simp only [↓reduceIte, Prog.ret_bind]
        apply congrArg (fun next => driverRead layout driver "running_task" >>= next)
        funext runningValue
        apply congrArg (fun next => truth runningValue >>= next)
        funext running
        cases running <;> rfl

/-- All three assertion effects retain the same context and occur before the
complete Task scope; macro omission never schedules an operand later. -/
private theorem assertion_scope_keeps_complete_continuation (operations : Operations)
    (layout : RunLayout) (context : Context) (driver : Option Ptr) (fuel : Nat)
    (knownDriver : context "driver".toList =
      some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))))
    (knownBind : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList =
      some (.scalar (runType "int") (some (.i32 262))))
    (knownCall : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList =
      some (.scalar (runType "int") (some (.i32 263))))
    (knownNormalize : context "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList =
      some (.scalar (runType "int") (some (.i32 264))))
    (knownCapacity : context "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4))))
    (outside : context "g_prime_need_evaluator_id".toList = none) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 20)
      context (assertionStatements ++ taskStatements) =
        (assertions operations layout driver >>= fun _ => taskBody operations layout context driver) := by
  unfold assertionStatements
  simp only [List.cons_append, List.nil_append]
  rewrite [StatementBlock.scoped_effect_keeps_continuation,
    StatementBlock.scoped_effect_keeps_continuation,
    StatementBlock.scoped_effect_keeps_continuation,
    task_scope_keeps_complete_continuation operations layout context driver fuel
      knownDriver knownBind knownCall knownNormalize knownCapacity outside]
  rewrite [← assertion_effects_keep_original_order operations layout context driver knownDriver]
  simp only [Prog.bind_eq, Prog.bind_assoc]

private theorem driver_read_keeps_global_pointer (operations : Operations) (layout : RunLayout)
    (context : Context) (outside : context "g_prime_eval_stack_driver".toList = none) :
    runRead operations layout context (TaskAdmission.ident "g_prime_eval_stack_driver") =
      (CProg.loadPtr layout.currentDriver >>= fun value => pure (.ptr value)) := by
  simp only [runRead, StatementBlock.ObjectBindings.read, TaskAdmission.ident,
    expressionWithNames.eq_def, localOrLocated, StatementBlock.ObjectBindings.values,
    StatementBlock.ObjectBindings.declared, outside, Option.isSome_none,
    Bool.false_eq_true, if_false]
  change field (fun _ => some ⟨0, .pointer⟩) (.ptr (some layout.currentDriver))
    "g_prime_eval_stack_driver".toList = _
  have zero : layout.currentDriver + 0 = layout.currentDriver := by
    cases layout.currentDriver
    rfl
  simp only [field, pointer, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, zero]

/-- Driver introduction keeps the actual nullable global read, declaration
conversion and whole continuation before restoring its previous local slot. -/
private theorem driver_declaration_keeps_read_and_scope (operations : Operations)
    (layout : RunLayout) (context : Context)
    (outside : context "g_prime_eval_stack_driver".toList = none)
    (continuation : Context → CProg CVal (ReadBlock.Result Context)) :
    StatementBlock.ObjectBindings.declaration (profile operations layout) operations.region
      emptyLayout context (runType "PrimeEvalStackDriver" 1) "driver".toList
      (some (TaskAdmission.ident "g_prime_eval_stack_driver")) continuation =
      (do
        let driver ← CProg.loadPtr layout.currentDriver
        let result ← continuation
          (bindScalar context "driver" (runType "PrimeEvalStackDriver" 1) (.ptr driver))
        pure (StatementBlock.ObjectBindings.restore "driver".toList
          (context "driver".toList) result)) := by
  rewrite [StatementBlock.ObjectBindings.initialized_scalar_keeps_read_conversion_and_flow
    (profile operations layout) operations.region emptyLayout context
    (runType "PrimeEvalStackDriver" 1) "driver".toList _ (by rfl)]
  have globalRead := driver_read_keeps_global_pointer operations layout context outside
  change StatementBlock.ObjectBindings.read (profile operations layout) emptyLayout context
    (TaskAdmission.ident "g_prime_eval_stack_driver") = _ at globalRead
  rewrite [globalRead]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  congr 1

private theorem name_keeps_string_distinction (left right : String) (distinct : left ≠ right) :
    left.toList ≠ right.toList := fun same => distinct (String.toList_inj.mp same)

private theorem initial_slot_absent (name : String)
    (notBind : name ≠ "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND")
    (notCall : name ≠ "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL")
    (notNormalize : name ≠ "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE")
    (notCapacity : name ≠ "CETTA_EVAL_INCOMPLETE_CAPACITY") :
    initialContext name.toList = none := by
  simp only [initialContext, name_keeps_string_distinction name _ notBind,
    name_keeps_string_distinction name _ notCall,
    name_keeps_string_distinction name _ notNormalize,
    name_keeps_string_distinction name _ notCapacity, ↓reduceIte]

private theorem initial_bind_enumeration :
    initialContext "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList =
      some (.scalar (runType "int") (some (.i32 262))) := rfl

private theorem initial_call_enumeration :
    initialContext "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList =
      some (.scalar (runType "int") (some (.i32 263))) := by
  unfold initialContext
  rewrite [if_neg (name_keeps_string_distinction _ _ (by decide)), if_pos rfl]
  rfl

private theorem initial_normalize_enumeration :
    initialContext "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList =
      some (.scalar (runType "int") (some (.i32 264))) := by
  unfold initialContext
  rewrite [if_neg (name_keeps_string_distinction _ _ (by decide)),
    if_neg (name_keeps_string_distinction _ _ (by decide)), if_pos rfl]
  rfl

private theorem initial_capacity_enumeration :
    initialContext "CETTA_EVAL_INCOMPLETE_CAPACITY".toList =
      some (.scalar (runType "int") (some (.i32 4))) := by
  unfold initialContext
  rewrite [if_neg (name_keeps_string_distinction _ _ (by decide)),
    if_neg (name_keeps_string_distinction _ _ (by decide)),
    if_neg (name_keeps_string_distinction _ _ (by decide)), if_pos rfl]
  rfl

/-- The original twenty-statement runner and the independently authored
operation tree agree before any endpoint projection. Every callback, by-value
copy, flow, scope inspection and restoration remains in the same computation.
This is a model-level source denotation, not compiled-provider verification. -/
theorem original_body_keeps_complete_operation_tree (operations : Operations)
    (layout : RunLayout) (fuel : Nat) :
    StatementBlock.executeScopedWith (services operations layout) emptyLayout 0 (fuel + 21)
      initialContext runSyntax.body = runOperations operations layout := by
  have body : runSyntax.body = .declare (runType "PrimeEvalStackDriver" 1) "driver".toList
      (TaskAdmission.ident "g_prime_eval_stack_driver") :: (assertionStatements ++ taskStatements) := rfl
  rewrite [body, StatementBlock.scoped_initialized_declaration_keeps_continuation]
  have provider : (services operations layout).declaration =
      StatementBlock.ObjectBindings.declaration (profile operations layout) operations.region := rfl
  rewrite [provider, driver_declaration_keeps_read_and_scope operations layout initialContext
    (initial_slot_absent "g_prime_eval_stack_driver" (by decide) (by decide) (by decide) (by decide))]
  unfold runOperations
  apply congrArg (fun next => CProg.loadPtr layout.currentDriver >>= next)
  funext driver
  have driverIn : (bindScalar initialContext "driver" (runType "PrimeEvalStackDriver" 1) (.ptr driver))
      "driver".toList = some (.scalar (runType "PrimeEvalStackDriver" 1) (some (.ptr driver))) := by
    unfold bindScalar
    exact Function.update_self _ _ _
  have bindIn : (bindScalar initialContext "driver" (runType "PrimeEvalStackDriver" 1) (.ptr driver))
      "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND".toList =
        some (.scalar (runType "int") (some (.i32 262))) :=
    (scalar_slot_keeps_other initialContext "driver" "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_BIND"
      _ (.ptr driver) (by decide)).trans initial_bind_enumeration
  have callIn : (bindScalar initialContext "driver" (runType "PrimeEvalStackDriver" 1) (.ptr driver))
      "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL".toList =
        some (.scalar (runType "int") (some (.i32 263))) :=
    (scalar_slot_keeps_other initialContext "driver" "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_CALL"
      _ (.ptr driver) (by decide)).trans initial_call_enumeration
  have normalizeIn : (bindScalar initialContext "driver" (runType "PrimeEvalStackDriver" 1) (.ptr driver))
      "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE".toList =
        some (.scalar (runType "int") (some (.i32 264))) :=
    (scalar_slot_keeps_other initialContext "driver" "CETTA_RUNTIME_COUNTER_PRIME_EVAL_STACK_TASK_NORMALIZE"
      _ (.ptr driver) (by decide)).trans initial_normalize_enumeration
  have capacityIn : (bindScalar initialContext "driver" (runType "PrimeEvalStackDriver" 1) (.ptr driver))
      "CETTA_EVAL_INCOMPLETE_CAPACITY".toList = some (.scalar (runType "int") (some (.i32 4))) :=
    (scalar_slot_keeps_other initialContext "driver" "CETTA_EVAL_INCOMPLETE_CAPACITY"
      _ (.ptr driver) (by decide)).trans initial_capacity_enumeration
  have outsideIn : (bindScalar initialContext "driver" (runType "PrimeEvalStackDriver" 1) (.ptr driver))
      "g_prime_need_evaluator_id".toList = none :=
    (scalar_slot_keeps_other initialContext "driver" "g_prime_need_evaluator_id"
      _ (.ptr driver) (by decide)).trans
      (initial_slot_absent "g_prime_need_evaluator_id" (by decide) (by decide) (by decide) (by decide))
  rewrite [assertion_scope_keeps_complete_continuation operations layout
    (bindScalar initialContext "driver" (runType "PrimeEvalStackDriver" 1) (.ptr driver))
    driver fuel driverIn bindIn callIn normalizeIn capacityIn outsideIn]
  simp only [Prog.bind_eq, Prog.bind_assoc]

/-- Parser admission and the full source comparison compose without changing
fuel, flow, service inventory or lexical scope. Provider realization remains
an explicit independent obligation. -/
theorem original_source_keeps_complete_operation_tree (operations : Operations)
    (layout : RunLayout) (fuel : Nat) :
    fromOriginal (services operations layout) emptyLayout 0 (fuel + 21) initialContext =
      runOperations operations layout := by
  rewrite [original_source_executes_retained_body]
  exact original_body_keeps_complete_operation_tree operations layout fuel

open Mettapedia.GSLT.Dynamics

/-- The full original source instantiates the common resumption construction.
Its independent runner retains every primitive, dependent response and scoped
result; actual physical provider realization remains a separate obligation. -/
theorem original_source_keeps_common_resumption (operations : Operations)
    (layout : RunLayout) (fuel : Nat) :
    Prog.toResumption
        (fromOriginal (services operations layout) (fun _ => none) 0 (fuel + 21) initialContext) =
      Prog.toResumption (runOperations operations layout) :=
  congrArg Prog.toResumption (original_source_keeps_complete_operation_tree operations layout fuel)

/-- This comparison is valid for stateful memory, cost and history primitives;
it does not collapse their permitted successor worlds to a returned value. -/
theorem original_source_has_common_stateful_denotation {State : Type}
    (act : (operation : Op CVal) → Action State (Op.Ret operation))
    (operations : Operations) (layout : RunLayout) (fuel : Nat) :
    Resumption.denote act (Prog.toResumption
        (fromOriginal (services operations layout) (fun _ => none) 0 (fuel + 21) initialContext)) =
      (runOperations operations layout).denote act := by
  rw [Resumption.denote_toResumption]
  exact congrArg (fun program => program.denote act)
    (original_source_keeps_complete_operation_tree operations layout fuel)

theorem original_source_keeps_common_fault_avoidance {State : Type}
    (act : (operation : Op CVal) → Action State (Op.Ret operation))
    (operations : Operations) (layout : RunLayout) (fuel : Nat) (before : State) :
    (Resumption.denote act (Prog.toResumption
        (fromOriginal (services operations layout) (fun _ => none) 0 (fuel + 21) initialContext))).Safe before ↔
      (runOperations operations layout).Safe act before := by
  rw [original_source_has_common_stateful_denotation]
  rfl

theorem original_source_keeps_common_whole_state_runs {State : Type}
    (act : (operation : Op CVal) → Action State (Op.Ret operation))
    (operations : Operations) (layout : RunLayout) (fuel : Nat)
    (before after : State) (result : ReadBlock.Result Context) :
    (Resumption.denote act (Prog.toResumption
        (fromOriginal (services operations layout) (fun _ => none) 0 (fuel + 21) initialContext))).Step
        before result after ↔ (runOperations operations layout).Runs act before result after := by
  rw [original_source_has_common_stateful_denotation]
  rfl

/-- A declared fold may read costs or evidence, but cannot change the tree that
it receives at this source boundary. Fold-specific erasure needs its own laws. -/
theorem original_source_keeps_common_handler {Observation : Type}
    (onReturn : ReadBlock.Result Context → Observation)
    (onOperation : (operation : Op CVal) → (Op.Ret operation → Observation) → Observation)
    (operations : Operations) (layout : RunLayout) (fuel : Nat) :
    ResumptionAlgebra.fold onReturn onOperation (Prog.toResumption
        (fromOriginal (services operations layout) (fun _ => none) 0 (fuel + 21) initialContext)) =
      ResumptionAlgebra.fold onReturn onOperation (Prog.toResumption (runOperations operations layout)) := by
  rw [original_source_keeps_common_resumption]

open Mettapedia.Machines

/-- Every bounded cursor account of the original task source agrees with its
independently authored runner. The result retains the actual continuation,
fault status, complete provider world and paid charge. Inspection allowance is
separate from source-parser fuel and native coordinator progress. -/
theorem original_source_keeps_cursor_account {State Fault : Type}
    (step : State → (operation : Op CVal) → State × Except Fault (Op.Ret operation))
    (cost : State → Op CVal → Nat) (operations : Operations) (layout : RunLayout)
    (sourceFuel inspections : Nat) (before : State) :
    Cursor.advance (Cursor.PrimitiveProgram.provider step)
        (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
        (Cursor.PrimitiveProgram.charge cost step) inspections (base := PUnit.unit)
        ⟨PUnit.unit, .ok (fromOriginal (services operations layout) (fun _ => none)
          0 (sourceFuel + 21) initialContext), before⟩ =
      Cursor.advance (Cursor.PrimitiveProgram.provider step)
        (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
        (Cursor.PrimitiveProgram.charge cost step) inspections (base := PUnit.unit)
        ⟨PUnit.unit, .ok (runOperations operations layout), before⟩ :=
  congrArg (fun program => Cursor.advance (Cursor.PrimitiveProgram.provider step)
    (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
    (Cursor.PrimitiveProgram.charge cost step) inspections (base := PUnit.unit)
    ⟨PUnit.unit, .ok program, before⟩)
    (original_source_keeps_complete_operation_tree operations layout sourceFuel)

/-- The common cursor executes the complete parsed source according to the
independent direct bounded interpretation of the original primitive tree.
This model law does not certify callback termination, physical memory or ABI. -/
theorem original_source_has_direct_bounded_interpretation {State Fault : Type}
    (step : State → (operation : Op CVal) → State × Except Fault (Op.Ret operation))
    (cost : State → Op CVal → Nat) (operations : Operations) (layout : RunLayout)
    (sourceFuel inspections : Nat) (before : State) :
    let result := Cursor.advance (Cursor.PrimitiveProgram.provider step)
      (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
      (Cursor.PrimitiveProgram.charge cost step) inspections (base := PUnit.unit)
      ⟨PUnit.unit, .ok (fromOriginal (services operations layout) (fun _ => none)
        0 (sourceFuel + 21) initialContext), before⟩
    (result.1, Cursor.PrimitiveProgram.readOutcome step result.2) =
      Cursor.PrimitiveProgram.direct step cost inspections
        (.ok (runOperations operations layout)) before := by
  rw [original_source_keeps_cursor_account]
  exact Cursor.PrimitiveProgram.advance_is_direct step cost inspections
    (.ok (runOperations operations layout)) before

/-- Local realization of independently specified primitives lifts to the
complete task-source account. A pause preserves a safe residual; successful
completion is an actual permitted whole-world run. -/
theorem original_source_cursor_keeps_safe_outcome {State Fault : Type}
    (act : (operation : Op CVal) → Action State (Op.Ret operation))
    (step : State → (operation : Op CVal) → State × Except Fault (Op.Ret operation))
    (localLaw : Cursor.PrimitiveProgram.ProviderSound act step)
    (cost : State → Op CVal → Nat) (operations : Operations) (layout : RunLayout)
    (sourceFuel inspections : Nat) (before : State)
    (safe : (runOperations operations layout).Safe act before) :
    Cursor.PrimitiveProgram.SafeOutcome act (runOperations operations layout) before
      (Cursor.PrimitiveProgram.readOutcome step
        (Cursor.advance (Cursor.PrimitiveProgram.provider step)
          (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
          (Cursor.PrimitiveProgram.charge cost step) inspections (base := PUnit.unit)
          ⟨PUnit.unit, .ok (fromOriginal (services operations layout) (fun _ => none)
            0 (sourceFuel + 21) initialContext), before⟩).2) := by
  rw [original_source_keeps_cursor_account]
  exact Cursor.PrimitiveProgram.advance_safe_outcome act step localLaw cost inspections
    (runOperations operations layout) before safe

/-- Cutting the common scheduler retains the complete actual source residual
and paid account. Resumption executes its suffix rather than rebuilding the
source program or repeating its prefix. -/
theorem original_source_cursor_split_retains_account {State Fault : Type}
    (step : State → (operation : Op CVal) → State × Except Fault (Op.Ret operation))
    (cost : State → Op CVal → Nat) (operations : Operations) (layout : RunLayout)
    (sourceFuel earlier later : Nat) (before : State) :
    Cursor.advance (Cursor.PrimitiveProgram.provider step)
        (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
        (Cursor.PrimitiveProgram.charge cost step) (earlier + later) (base := PUnit.unit)
        ⟨PUnit.unit, .ok (fromOriginal (services operations layout) (fun _ => none)
          0 (sourceFuel + 21) initialContext), before⟩ =
      Cursor.resume (Cursor.PrimitiveProgram.provider step)
        (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
        (Cursor.PrimitiveProgram.charge cost step) later (base := PUnit.unit)
        (Cursor.advance (Cursor.PrimitiveProgram.provider step)
          (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
          (Cursor.PrimitiveProgram.charge cost step) earlier (base := PUnit.unit)
          ⟨PUnit.unit, .ok (fromOriginal (services operations layout) (fun _ => none)
            0 (sourceFuel + 21) initialContext), before⟩) :=
  Cursor.advance_add (Cursor.PrimitiveProgram.provider step)
    (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
    (Cursor.PrimitiveProgram.charge cost step) earlier later (base := PUnit.unit) _

/-- Related provider representations execute the original task source with
the same retained account as its independent operation tree. The local step
law preserves replies and complete related states; metric calibration is a
separate premise. Neither premise follows from agreement of printed answers. -/
theorem original_source_keeps_related_cursor_account
    {State OtherState Fault : Type}
    (leftStep : State → (operation : Op CVal) → State × Except Fault (Op.Ret operation))
    (rightStep : OtherState → (operation : Op CVal) → OtherState × Except Fault (Op.Ret operation))
    (leftCost : State → Op CVal → Nat) (rightCost : OtherState → Op CVal → Nat)
    (rel : Cursor.StateRel (Cursor.PrimitiveProgram.provider leftStep)
      (Cursor.PrimitiveProgram.provider rightStep))
    (localLaw : Cursor.Bisimulation rel)
    (calibrated : Cursor.ChargeRelated rel (Cursor.PrimitiveProgram.charge leftCost leftStep)
      (Cursor.PrimitiveProgram.charge rightCost rightStep))
    (operations : Operations) (layout : RunLayout) (sourceFuel inspections : Nat)
    (before : State) (otherBefore : OtherState)
    (related : rel (base := PUnit.unit) (index := PUnit.unit) before otherBefore) :
    Cursor.AccountRel
      (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault) rel
      (Cursor.advance (Cursor.PrimitiveProgram.provider leftStep)
        (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
        (Cursor.PrimitiveProgram.charge leftCost leftStep) inspections (base := PUnit.unit)
        ⟨PUnit.unit, .ok (fromOriginal (services operations layout) (fun _ => none)
          0 (sourceFuel + 21) initialContext), before⟩)
      (Cursor.advance (Cursor.PrimitiveProgram.provider rightStep)
        (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
        (Cursor.PrimitiveProgram.charge rightCost rightStep) inspections (base := PUnit.unit)
        ⟨PUnit.unit, .ok (runOperations operations layout), otherBefore⟩) := by
  rw [original_source_keeps_cursor_account]
  exact Cursor.advance_account_related
    (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
    rel localLaw (Cursor.PrimitiveProgram.charge leftCost leftStep)
    (Cursor.PrimitiveProgram.charge rightCost rightStep) calibrated inspections
    (Cursor.PacketRel.same
      (C := Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
      (rel := rel) (base := PUnit.unit) (index := PUnit.unit)
      (Except.ok (runOperations operations layout)) related)

/-- A source account can be resumed in related provider representations
without repeating its paid prefix. The comparison retains the actual suffix,
fault status, provider worlds and charge through the existing resume law. -/
theorem original_source_related_cursor_split_retains_account
    {State OtherState Fault : Type}
    (leftStep : State → (operation : Op CVal) → State × Except Fault (Op.Ret operation))
    (rightStep : OtherState → (operation : Op CVal) → OtherState × Except Fault (Op.Ret operation))
    (leftCost : State → Op CVal → Nat) (rightCost : OtherState → Op CVal → Nat)
    (rel : Cursor.StateRel (Cursor.PrimitiveProgram.provider leftStep)
      (Cursor.PrimitiveProgram.provider rightStep))
    (localLaw : Cursor.Bisimulation rel)
    (calibrated : Cursor.ChargeRelated rel (Cursor.PrimitiveProgram.charge leftCost leftStep)
      (Cursor.PrimitiveProgram.charge rightCost rightStep))
    (operations : Operations) (layout : RunLayout) (sourceFuel earlier later : Nat)
    (before : State) (otherBefore : OtherState)
    (related : rel (base := PUnit.unit) (index := PUnit.unit) before otherBefore) :
    Cursor.AccountRel
      (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault) rel
      (Cursor.resume (Cursor.PrimitiveProgram.provider leftStep)
        (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
        (Cursor.PrimitiveProgram.charge leftCost leftStep) later (base := PUnit.unit)
        (Cursor.advance (Cursor.PrimitiveProgram.provider leftStep)
          (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
          (Cursor.PrimitiveProgram.charge leftCost leftStep) earlier (base := PUnit.unit)
          ⟨PUnit.unit, .ok (fromOriginal (services operations layout) (fun _ => none)
            0 (sourceFuel + 21) initialContext), before⟩))
      (Cursor.resume (Cursor.PrimitiveProgram.provider rightStep)
        (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
        (Cursor.PrimitiveProgram.charge rightCost rightStep) later (base := PUnit.unit)
        (Cursor.advance (Cursor.PrimitiveProgram.provider rightStep)
          (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
          (Cursor.PrimitiveProgram.charge rightCost rightStep) earlier (base := PUnit.unit)
          ⟨PUnit.unit, .ok (runOperations operations layout), otherBefore⟩)) :=
  Cursor.resume_account_related
    (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
    rel localLaw (Cursor.PrimitiveProgram.charge leftCost leftStep)
    (Cursor.PrimitiveProgram.charge rightCost rightStep) calibrated later
    (original_source_keeps_related_cursor_account leftStep rightStep leftCost rightCost
      rel localLaw calibrated operations layout sourceFuel earlier before otherBefore related)

open Mettapedia.GSLT.LanguageDef.NativeControlCursor

/-- The complete parsed task source and its independent operation tree have
one common generated protocol history in related provider representations.
Both projections retain each primitive response, world and continuation.
The relation may have several representatives; no representative is chosen
from equality of answers. Native event coverage and service realization
remain additional obligations. -/
theorem original_source_keeps_related_generated_histories
    {State OtherState Fault : Type}
    (leftStep : State → (operation : Op CVal) → State × Except Fault (Op.Ret operation))
    (rightStep : OtherState → (operation : Op CVal) → OtherState × Except Fault (Op.Ret operation))
    (leftCost : State → Op CVal → Nat) (rightCost : OtherState → Op CVal → Nat)
    (rel : Cursor.StateRel (Cursor.PrimitiveProgram.provider leftStep)
      (Cursor.PrimitiveProgram.provider rightStep))
    (localLaw : Cursor.Bisimulation rel)
    (commonCost : Cursor.Charge (Cursor.Bisimulation.coupledProvider rel localLaw))
    (operations : Operations) (layout : RunLayout) (sourceFuel inspections : Nat)
    (before : State) (otherBefore : OtherState)
    (related : rel (base := PUnit.unit) (index := PUnit.unit) before otherBefore) :
    let C := Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault
    let common : Cursor.Packet (Cursor.Bisimulation.coupledProvider rel localLaw) C PUnit.unit :=
      ⟨PUnit.unit, .ok (runOperations operations layout), ⟨(before,otherBefore),related⟩⟩
    let history := ProtocolHistory.advanceHistory
      (Cursor.Bisimulation.coupledProvider rel localLaw) C commonCost inspections common
    HEq ((ProtocolHistory.homForward C
        (Cursor.Bisimulation.leftProjection rel localLaw) PUnit.unit).histories.map history)
      (ProtocolHistory.advanceHistory (Cursor.PrimitiveProgram.provider leftStep) C
        (Cursor.PrimitiveProgram.charge leftCost leftStep) inspections (base := PUnit.unit)
        ⟨PUnit.unit, .ok (fromOriginal (services operations layout) (fun _ => none)
          0 (sourceFuel + 21) initialContext), before⟩) ∧
    HEq ((ProtocolHistory.homForward C
        (Cursor.Bisimulation.rightProjection rel localLaw) PUnit.unit).histories.map history)
      (ProtocolHistory.advanceHistory (Cursor.PrimitiveProgram.provider rightStep) C
        (Cursor.PrimitiveProgram.charge rightCost rightStep) inspections (base := PUnit.unit)
        ⟨PUnit.unit, .ok (runOperations operations layout), otherBefore⟩) := by
  dsimp only
  erw [original_source_keeps_complete_operation_tree]
  exact ProtocolHistory.coupled_advance_histories
    (Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault)
    rel localLaw commonCost (Cursor.PrimitiveProgram.charge leftCost leftStep)
    (Cursor.PrimitiveProgram.charge rightCost rightStep) inspections
    (base := PUnit.unit) (index := PUnit.unit)
    (.ok (runOperations operations layout)) before otherBefore related

/-- The actual generated history of the full parsed source pays the
independent runner's cursor account. The declared charge is a provider metric,
not a certification of compiled instruction count or physical elapsed time. -/
theorem original_source_generated_history_pays_runner_account {State Fault : Type}
    (step : State → (operation : Op CVal) → State × Except Fault (Op.Ret operation))
    (cost : State → Op CVal → Nat) (operations : Operations) (layout : RunLayout)
    (sourceFuel inspections : Nat) (before : State) :
    let C := Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault
    let M := Cursor.PrimitiveProgram.provider step
    let charge : Cursor.Charge M := Cursor.PrimitiveProgram.charge cost step
    Multiplicative.toAdd ((ProtocolHistory.providerAccount M C charge PUnit.unit).of
      (ProtocolHistory.advanceHistory M C charge inspections (base := PUnit.unit)
        ⟨PUnit.unit, .ok (fromOriginal (services operations layout) (fun _ => none)
          0 (sourceFuel + 21) initialContext), before⟩)) =
      (Cursor.advance M C charge inspections (base := PUnit.unit)
        ⟨PUnit.unit, .ok (runOperations operations layout), before⟩).1 := by
  dsimp only
  rw [ProtocolHistory.advanceHistory_paid, original_source_keeps_cursor_account]

/-- Any scheduler cut of the complete parsed source preserves the whole
chronological history, including repeated requests and fault replies. The
suffix starts at its retained outcome and does not replay its paid prefix. -/
theorem original_source_split_keeps_generated_history {State Fault : Type}
    (step : State → (operation : Op CVal) → State × Except Fault (Op.Ret operation))
    (cost : State → Op CVal → Nat) (operations : Operations) (layout : RunLayout)
    (sourceFuel earlier later : Nat) (before : State) :
    let C := Cursor.PrimitiveProgram.client (Op CVal) Op.Ret (ReadBlock.Result Context) Fault
    let M := Cursor.PrimitiveProgram.provider step
    let charge : Cursor.Charge M := Cursor.PrimitiveProgram.charge cost step
    let packet : Cursor.Packet M C PUnit.unit :=
      ⟨PUnit.unit, .ok (fromOriginal (services operations layout) (fun _ => none)
        0 (sourceFuel + 21) initialContext), before⟩
    HEq (ProtocolHistory.advanceHistory M C charge (earlier + later) packet)
      ((ProtocolHistory.advanceHistory M C charge earlier packet).comp
        (ProtocolHistory.resumeHistory M C charge later
          (Cursor.advance M C charge earlier packet))) :=
  ProtocolHistory.chunkHistory_exact _ _ _ earlier later _


end Mettapedia.Languages.MeTTa.CeTTaNativeCost.RunTaskSource.Execution.Tree

namespace Mettapedia.Languages.MeTTa.CeTTaNativeCost.CapturedRun.OverlayControls

abbrev SumViews := Views (Option Nat) (Option Nat) Nat (Option Nat)

/-- A numerical aggregate alone cannot distinguish no captured factors from
a captured factor whose coefficient is zero. This tempting replacement for
the native length/presence test therefore requires a separate comparison. -/
def sumPresence (view : SumViews) : Presence :=
  ⟨view.need.isSome, view.branch.isSome, view.weights != 0, view.receipt.isSome⟩

def zeroFactor : TestViews := { empty with weights := [0] }

theorem zero_factor_replaces_the_parent_factor_carrier :
    (overlay actualPresence (some (20, zeroFactor)) caller).weights = [0] := rfl

theorem aggregate_after_entry_keeps_the_zero_coefficient :
    ((overlay actualPresence (some (20, zeroFactor)) caller).map
      id id List.sum id id).weights = 0 := rfl

theorem aggregate_before_entry_inherits_the_parent_coefficients :
    (overlay sumPresence (some (20, zeroFactor.map id id List.sum id id))
      (caller.map id id List.sum id id)).weights = 26 := rfl

theorem numerical_aggregation_does_not_commute_with_task_entry :
    (overlay actualPresence (some (20, zeroFactor)) caller).map id id List.sum id id ≠
      overlay sumPresence (some (20, zeroFactor.map id id List.sum id id))
        (caller.map id id List.sum id id) := by
  intro equality
  have impossible := congrArg Views.weights equality
  change (0 : Nat) = 26 at impossible
  cases impossible

theorem numerical_aggregation_is_not_presence_preserving :
    sumPresence (zeroFactor.map id id List.sum id id) ≠ actualPresence zeroFactor := by
  intro equality
  have impossible := congrArg Presence.weights equality
  change false = true at impossible
  cases impossible

end Mettapedia.Languages.MeTTa.CeTTaNativeCost.CapturedRun.OverlayControls

namespace Mettapedia.Languages.MeTTa.CeTTaNativeCost.RunTaskSource.Authority

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Machines.CMemory
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u

/-- Initialize the guard from its actual by-value entry result, retaining the
complete extent check before either store. The automatic region separately
provides these writable cells and their native lifetime/representation. -/
def initializeGuard (layout : Layout) (incoming : Bool) (guard : Ptr) : CProg CVal Unit := do
  let fields ← enter layout incoming
  if fields.length = 2 then CProg.initializeCells guard fields else CProg.undefined

section Physical

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

theorem nonnull_guard_initialization (layout : Layout) (driver guard : Ptr) (cells : Nat)
    (previous incoming : Bool) (inside : driver.offset ≤ cells) :
    CTriple (L := L)
      (Cells guard ([none, none] : List (Option CVal)) ∗
        (PointsTo layout.currentDriver (.ptr (some driver)) ∗
          driverMemory layout driver cells previous))
      (initializeGuard layout incoming guard)
      (fun _ => Cells guard [some (.ptr (some driver)), some (.bool previous)] ∗
        (PointsTo layout.currentDriver (.ptr (some driver)) ∗
          driverMemory layout driver cells incoming)) := by
  unfold initializeGuard
  simp only [Prog.bind_eq]
  have first := frame_left
    (current_nonnull_entry (L := L) layout driver cells previous incoming inside)
    (Cells guard ([none, none] : List (Option CVal)))
  have first' := triple_post act first (fun fields heap held => by
    rw [sepConj_pure_right] at held
    exact held)
  refine triple_bind act first' fun fields => ?_
  apply triple_pure
  intro same
  subst fields
  simp only [List.length_cons, List.length_nil, ↓reduceIte]
  exact frame (initialize_cells (L := L) guard
    ([none, none] : List (Option CVal))
    [CVal.ptr (some driver), CVal.bool previous] (by rfl))
    (PointsTo layout.currentDriver (CVal.ptr (some driver)) ∗
      driverMemory layout driver cells incoming)

theorem null_guard_initialization (layout : Layout) (guard : Ptr) (incoming : Bool)
    (F : Heap L → Prop) :
    CTriple (L := L)
      (Cells guard ([none, none] : List (Option CVal)) ∗
        (PointsTo layout.currentDriver (.ptr none) ∗ F))
      (initializeGuard layout incoming guard)
      (fun _ => Cells guard [some (.ptr none), some (.bool false)] ∗
        (PointsTo layout.currentDriver (.ptr none) ∗ F)) := by
  unfold initializeGuard
  simp only [Prog.bind_eq]
  have first := frame_left (current_null_entry (L := L) layout incoming F)
    (Cells guard ([none, none] : List (Option CVal)))
  have first' := triple_post act first (fun fields heap held => by
    rw [sepConj_pure_right] at held
    exact held)
  refine triple_bind act first' fun fields => ?_
  apply triple_pure
  intro same
  subst fields
  simp only [List.length_cons, List.length_nil, ↓reduceIte]
  exact frame (initialize_cells (L := L) guard
    ([none, none] : List (Option CVal)) [CVal.ptr none, CVal.bool false] (by rfl))
    (PointsTo layout.currentDriver (CVal.ptr none) ∗ F)

/-- Initialization followed by its actual cleanup preserves the selected
reference, every saved field and the previous authority value. The live
storage remains owned until the enclosing automatic region exits. -/
theorem initialized_guard_cleans_up (layout : Layout) (driver guard : Ptr) (cells : Nat)
    (previous incoming : Bool) (inside : driver.offset ≤ cells) :
    CTriple (L := L)
      (Cells guard ([none, none] : List (Option CVal)) ∗
        (PointsTo layout.currentDriver (.ptr (some driver)) ∗
          driverMemory layout driver cells previous))
      (initializeGuard layout incoming guard >>= fun _ => leave layout guard)
      (fun _ => Cells guard [some (.ptr (some driver)), some (.bool previous)] ∗
        (PointsTo layout.currentDriver (.ptr (some driver)) ∗
          driverMemory layout driver cells previous)) := by
  simp only [Prog.bind_eq]
  refine triple_bind act (nonnull_guard_initialization layout driver guard cells previous incoming inside)
    fun _ => ?_
  have second := frame_left
    (cleanup_restores_the_saved_driver_and_preserves_guard (L := L)
      layout guard driver cells previous incoming inside)
    (PointsTo layout.currentDriver (CVal.ptr (some driver)))
  have rearrange (flag : Bool) :
      (Cells guard [some (CVal.ptr (some driver)), some (CVal.bool previous)] ∗
        (PointsTo layout.currentDriver (CVal.ptr (some driver)) ∗
          driverMemory (L := L) layout driver cells flag)) =
      (PointsTo layout.currentDriver (CVal.ptr (some driver)) ∗
        guardMemory layout guard driver cells previous flag) := by
    rw [guardMemory, ← sepConj_assoc,
      sepConj_comm (Cells guard [some (CVal.ptr (some driver)), some (CVal.bool previous)]),
      sepConj_assoc]
  rw [rearrange incoming]
  apply triple_post act second
  intro ignored heap held
  rw [rearrange previous]
  exact held

end Physical

end Mettapedia.Languages.MeTTa.CeTTaNativeCost.RunTaskSource.Authority


namespace Mettapedia.Languages.MeTTa.CeTTaNativeCost.GraphBoundSource

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Machines.CMemory

private def ident (name : String) : CExpr := .identifier name.toList
private def analysisField (name : String) : CExpr := .field (ident "analysis") name.toList true

def source : String := "bool cetta_cost_graph_bound(const CettaCostGraphAnalysis *analysis, uint64_t *bound) {\n    if (!analysis || !bound || analysis->status != CETTA_COST_GRAPH_BOUND)\n        return false;\n    *bound = analysis->bounds[analysis->root];\n    return true;\n}"

def characters : List Char := native_c_characters% "bool cetta_cost_graph_bound(const CettaCostGraphAnalysis *analysis, uint64_t *bound) {\n    if (!analysis || !bound || analysis->status != CETTA_COST_GRAPH_BOUND)\n        return false;\n    *bound = analysis->bounds[analysis->root];\n    return true;\n}"

def boundSyntax : CQualifiedFunction :=
  ⟨⟨"bool".toList, 0⟩, "cetta_cost_graph_bound".toList,
    [⟨⟨⟨"CettaCostGraphAnalysis".toList, 1⟩, "analysis".toList⟩, true⟩,
     ⟨⟨⟨"uint64_t".toList, 1⟩, "bound".toList⟩, false⟩],
    [.branch (.binary .or
      (.binary .or (.unary .not (ident "analysis")) (.unary .not (ident "bound")))
      (.binary .ne (analysisField "status") (ident "CETTA_COST_GRAPH_BOUND")))
      [.return (some (.bool false))] [],
     .assign (.unary .dereference (ident "bound"))
       (.index (analysisField "bounds") (analysisField "root")),
     .return (some (.bool true))]⟩

def names : TypeNames := ["bool".toList, "CettaCostGraphAnalysis".toList, "uint64_t".toList]

theorem characters_are_actual_source : source.toList = characters := by
  native_c_character_reflexivity

theorem actual_function_parses : qualifiedFunctionText? names characters = some boundSyntax := by
  native_c_parser_reflexivity

theorem original_source_recognized : qualifiedFunctionText? names source.toList = some boundSyntax := by
  rw [characters_are_actual_source]
  exact actual_function_parses

/-- Offsets count logical cells. The source adapter separately establishes
the declared enum, native size_t width, byte layout and held storage. -/
structure Layout where
  status : Nat
  bounds : Nat
  root : Nat

def Layout.fields (layout : Layout) : ReadExpressions.Layout := fun name =>
  if name = "status".toList then some ⟨layout.status, .signedWord⟩ else
  if name = "bounds".toList then some ⟨layout.bounds, .pointer⟩ else
  if name = "root".toList then some ⟨layout.root, .word64⟩ else none

def bindings (analysis bound : Option Ptr) (outside : ReadExpressions.Environment) :
    ReadExpressions.Environment := fun name =>
  if name = "analysis".toList then some (.ptr analysis) else
  if name = "bound".toList then some (.ptr bound) else
  if name = "CETTA_COST_GRAPH_BOUND".toList then some (.i32 1) else outside name

/-- Only the actual bounds-array operand has the declared uint64_t element
profile. A different array does not acquire that type from its value. -/
def objects : ReadExpressions.ObjectReads where
  indexKind := some fun
    | .field (.identifier owner) name true =>
        if owner = "analysis".toList ∧ name = "bounds".toList then some .word64 else none
    | _ => none

def read (layout : ReadExpressions.Layout) (environment : ReadExpressions.Environment)
    (operand : CExpr) : CProg CVal CVal :=
  ReadExpressions.expressionWithNames (fun name => ReadExpressions.resolved (environment name))
    (fun _ _ => CProg.undefined) layout operand objects

/-- The actual uint64_t destination is stored after reading the RHS. The
immutable destination operand has no competing effect; physical aliasing and
destination ownership are supplied by the memory contract. -/
def assignment : StatementBlock.Assignment := fun layout environment statement =>
  match statement with
  | .assign (.unary .dereference destination) operand => do
      let value ← read layout environment operand
      let pointer ← read layout environment destination
      let address ← ReadExpressions.pointer pointer
      match address, value with
      | some address, .u64 value =>
          CProg.store address (.u64 value) >>= fun _ => pure environment
      | _, _ => CProg.undefined
  | _ => CProg.undefined

def execute (layout : Layout) (analysis bound : Option Ptr)
    (outside : ReadExpressions.Environment) : CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith { read := read } assignment layout.fields 0 8
    (bindings analysis bound outside) boundSyntax.body

/-- The independent ordered primitive command keeps both nullable-pointer
tests before the status read, then reads the stored bounds pointer and the
full-width root before loading and publishing one uint64_t cell. -/
def command (layout : Layout) (analysis bound : Option Ptr) : CProg CVal Bool := do
  let missingAnalysis ← CProg.ptrEq analysis none
  if missingAnalysis then pure false else do
    let missingBound ← CProg.ptrEq bound none
    if missingBound then pure false else match analysis with
    | none => CProg.undefined
    | some analysis => do
        let status ← CProg.loadI32 (analysis + layout.status)
        if status != 1 then pure false else do
          let bounds ← CProg.loadPtr (analysis + layout.bounds)
          let root ← CProg.loadU64 (analysis + layout.root)
          match bounds with
          | none => CProg.undefined
          | some bounds => do
              let value ← CProg.loadU64 (bounds + root.toNat)
              match bound with
              | none => CProg.undefined
              | some bound => CProg.store bound (.u64 value) >>= fun _ => pure true

def report (environment : ReadExpressions.Environment) (accepted : Bool) : ReadBlock.Result :=
  .finished (.returned environment (some (.bool accepted)))


private theorem read_analysis (layout : Layout) (analysis bound : Option Ptr)
    (outside : ReadExpressions.Environment) :
    read layout.fields (bindings analysis bound outside) (ident "analysis") =
      pure (.ptr analysis) := rfl

private theorem read_bound (layout : Layout) (analysis bound : Option Ptr)
    (outside : ReadExpressions.Environment) :
    read layout.fields (bindings analysis bound outside) (ident "bound") =
      pure (.ptr bound) := rfl

private theorem read_field (layout : Layout) (analysis bound : Option Ptr)
    (outside : ReadExpressions.Environment) (name : String) :
    read layout.fields (bindings analysis bound outside) (analysisField name) =
      ReadExpressions.field layout.fields (.ptr analysis) name.toList := by
  change (read layout.fields (bindings analysis bound outside) (ident "analysis") >>=
    fun owner => ReadExpressions.field layout.fields owner name.toList) = _
  rw [read_analysis]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

private theorem read_pointer_not (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (name : String) (pointer : Option Ptr)
    (known : environment name.toList = some (.ptr pointer)) :
    read layout environment (.unary .not (ident name)) =
      (CProg.ptrEq pointer none >>= fun missing => pure (.bool missing)) := by
  change (ReadExpressions.resolved (environment name.toList) >>= fun value =>
    ReadExpressions.truth value >>= fun selected => pure (CVal.bool (!selected))) = _
  rw [known]
  simp only [ReadExpressions.resolved, ReadExpressions.truth, Prog.bind_eq,
    Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind, Bool.not_not]

private theorem read_or (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (left right : CExpr)
    (program : CProg CVal Bool)
    (actual : read layout environment left =
      (program >>= fun value => pure (.bool value))) :
    read layout environment (.binary .or left right) =
      (program >>= fun value => if value then pure (.bool true) else do
        let actual ← read layout environment right
        let selected ← ReadExpressions.truth actual
        pure (.bool selected)) := by
  change (read layout environment left >>= fun value =>
    ReadExpressions.truth value >>= fun selected =>
      if selected then pure (CVal.bool true) else do
        let second ← read layout environment right
        let selectedSecond ← ReadExpressions.truth second
        pure (CVal.bool selectedSecond)) = _
  rw [actual]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind,
    ReadExpressions.truth]

private def statusRefused (layout : Layout) (analysis : Option Ptr) : CProg CVal Bool :=
  match analysis with
  | none => CProg.undefined
  | some analysis => CProg.loadI32 (analysis + layout.status) >>= fun status => pure (status != 1)

private theorem read_status_ne (layout : Layout) (analysis bound : Option Ptr)
    (outside : ReadExpressions.Environment) :
    read layout.fields (bindings analysis bound outside)
      (.binary .ne (analysisField "status") (ident "CETTA_COST_GRAPH_BOUND")) =
      (statusRefused layout analysis >>= fun refused => pure (.bool refused)) := by
  change (read layout.fields (bindings analysis bound outside) (analysisField "status") >>=
    fun status => ReadExpressions.resolved ((bindings analysis bound outside) "CETTA_COST_GRAPH_BOUND".toList)
      >>= fun expected => ReadExpressions.binary .ne status expected) = _
  rw [read_field]
  have expected : (bindings analysis bound outside) "CETTA_COST_GRAPH_BOUND".toList = some (.i32 1) := rfl
  have descriptor : layout.fields "status".toList = some ⟨layout.status, .signedWord⟩ := rfl
  rw [expected]
  cases analysis with
  | none =>
      simp only [ReadExpressions.field, ReadExpressions.pointer, descriptor,
        ReadExpressions.resolved, statusRefused, Prog.bind_eq, Prog.pure_eq,
        Prog.ret_bind]
      exact (ReadExpressions.undefined_bind _).trans (ReadExpressions.undefined_bind _).symm
  | some address =>
      simp only [ReadExpressions.field, ReadExpressions.pointer, descriptor,
        ReadExpressions.resolved, ReadExpressions.binary, ReadExpressions.equal,
        ReadExpressions.scalar, ScalarRead.equal?, statusRefused,
        Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
      rfl

private def guardExpression : CExpr := .binary .or
  (.binary .or (.unary .not (ident "analysis")) (.unary .not (ident "bound")))
  (.binary .ne (analysisField "status") (ident "CETTA_COST_GRAPH_BOUND"))

private def rejected (layout : Layout) (analysis bound : Option Ptr) : CProg CVal Bool := do
  let missingAnalysis ← CProg.ptrEq analysis none
  if missingAnalysis then pure true else do
    let missingBound ← CProg.ptrEq bound none
    if missingBound then pure true else statusRefused layout analysis

private theorem read_guard (layout : Layout) (analysis bound : Option Ptr)
    (outside : ReadExpressions.Environment) :
    read layout.fields (bindings analysis bound outside) guardExpression =
      (rejected layout analysis bound >>= fun refused => pure (.bool refused)) := by
  let environment := bindings analysis bound outside
  have first := read_pointer_not layout.fields environment "analysis" analysis (by rfl)
  have second := read_pointer_not layout.fields environment "bound" bound (by rfl)
  have middle := read_or layout.fields environment
    (.unary .not (ident "analysis")) (.unary .not (ident "bound"))
    (CProg.ptrEq analysis none) first
  have final := read_or layout.fields environment
    (.binary .or (.unary .not (ident "analysis")) (.unary .not (ident "bound")))
    (.binary .ne (analysisField "status") (ident "CETTA_COST_GRAPH_BOUND"))
    (CProg.ptrEq analysis none >>= fun missingAnalysis =>
      if missingAnalysis then pure true else CProg.ptrEq bound none) (by
        rw [middle, second]
        simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind,
          ReadExpressions.truth, BindSchedule.bind_boolean_choice])
  change read layout.fields environment guardExpression = _
  unfold guardExpression
  rw [final, read_status_ne]
  simp only [rejected, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind,
    ReadExpressions.truth, BindSchedule.bind_boolean_choice, ↓reduceIte]

private theorem read_bounds (layout : Layout) (analysis bound : Option Ptr)
    (outside : ReadExpressions.Environment) :
    read layout.fields (bindings analysis bound outside) (analysisField "bounds") =
      match analysis with
      | none => CProg.undefined
      | some address => CProg.loadPtr (address + layout.bounds) >>= fun value => pure (.ptr value) := by
  rw [read_field]
  have descriptor : layout.fields "bounds".toList = some ⟨layout.bounds, .pointer⟩ := rfl
  cases analysis <;> simp only [ReadExpressions.field, ReadExpressions.pointer, descriptor,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

private theorem read_root (layout : Layout) (analysis bound : Option Ptr)
    (outside : ReadExpressions.Environment) :
    read layout.fields (bindings analysis bound outside) (analysisField "root") =
      match analysis with
      | none => CProg.undefined
      | some address => CProg.loadU64 (address + layout.root) >>= fun value => pure (.u64 value) := by
  rw [read_field]
  have descriptor : layout.fields "root".toList = some ⟨layout.root, .word64⟩ := rfl
  cases analysis <;> simp only [ReadExpressions.field, ReadExpressions.pointer, descriptor,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]


private def selectedValue (layout : Layout) (analysis : Option Ptr) : CProg CVal UInt64 :=
  match analysis with
  | none => CProg.undefined
  | some address => do
      let array ← CProg.loadPtr (address + layout.bounds)
      let root ← CProg.loadU64 (address + layout.root)
      match array with
      | none => CProg.undefined
      | some array => CProg.loadU64 (array + root.toNat)

private def publication (layout : Layout) (analysis bound : Option Ptr) : CProg CVal Unit := do
  let value ← selectedValue layout analysis
  match bound with
  | none => CProg.undefined
  | some bound => CProg.store bound (.u64 value)

private theorem read_selected_value (layout : Layout) (analysis bound : Option Ptr)
    (outside : ReadExpressions.Environment) :
    read layout.fields (bindings analysis bound outside)
      (.index (analysisField "bounds") (analysisField "root")) =
      (selectedValue layout analysis >>= fun value => pure (.u64 value)) := by
  change (read layout.fields (bindings analysis bound outside) (analysisField "bounds") >>=
    fun array => read layout.fields (bindings analysis bound outside) (analysisField "root")
      >>= fun root => ReadExpressions.indexedScalar .word64 array root) = _
  rw [read_bounds, read_root]
  cases analysis with
  | none =>
      change Prog.bind CProg.undefined _ = Prog.bind CProg.undefined _
      exact (ReadExpressions.undefined_bind _).trans (ReadExpressions.undefined_bind _).symm
  | some address =>
      simp only [selectedValue, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
      congr 1
      funext array
      congr 1
      funext root
      cases array with
      | none => exact (ReadExpressions.undefined_bind _).symm
      | some address => rfl

private theorem assignment_publishes_after_read (layout : Layout) (analysis bound : Option Ptr)
    (outside : ReadExpressions.Environment) :
    assignment layout.fields (bindings analysis bound outside)
      (.assign (.unary .dereference (ident "bound"))
        (.index (analysisField "bounds") (analysisField "root"))) =
      (publication layout analysis bound >>= fun _ => pure (bindings analysis bound outside)) := by
  change (read layout.fields (bindings analysis bound outside)
      (.index (analysisField "bounds") (analysisField "root")) >>= fun value =>
    read layout.fields (bindings analysis bound outside) (ident "bound") >>= fun pointer =>
    ReadExpressions.pointer pointer >>= fun address =>
      match address, value with
      | some address, .u64 value =>
          CProg.store address (.u64 value) >>= fun _ => pure (bindings analysis bound outside)
      | _, _ => CProg.undefined) = _
  rw [read_selected_value, read_bound]
  simp only [publication, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind,
    ReadExpressions.pointer]
  congr 1
  funext value
  cases bound with
  | none => exact (ReadExpressions.undefined_bind _).symm
  | some address => rfl

private theorem suffix_keeps_publication (layout : Layout) (analysis bound : Option Ptr)
    (outside : ReadExpressions.Environment) :
    StatementBlock.executeWith { read := read } assignment layout.fields 0 7
      (bindings analysis bound outside)
      [.assign (.unary .dereference (ident "bound"))
        (.index (analysisField "bounds") (analysisField "root")),
       .return (some (.bool true))] =
      (publication layout analysis bound >>= fun _ =>
        pure (report (bindings analysis bound outside) true)) := by
  rw [StatementBlock.executeWith_equation]
  dsimp only
  rw [assignment_publishes_after_read]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
  rfl

private theorem guard_keeps_selected_body (layout : Layout) (analysis bound : Option Ptr)
    (outside : ReadExpressions.Environment) :
    execute layout analysis bound outside =
      (rejected layout analysis bound >>= fun refused =>
        if refused then pure (report (bindings analysis bound outside) false)
        else publication layout analysis bound >>= fun _ =>
          pure (report (bindings analysis bound outside) true)) := by
  unfold execute
  change StatementBlock.executeWith { read := read } assignment layout.fields 0 8
    (bindings analysis bound outside)
    (.branch guardExpression [.return (some (.bool false))] [] ::
      [.assign (.unary .dereference (ident "bound"))
        (.index (analysisField "bounds") (analysisField "root")),
       .return (some (.bool true))]) = _
  rw [StatementBlock.executeWith_equation]
  change (read layout.fields (bindings analysis bound outside) guardExpression >>=
    fun actual => ReadExpressions.truth actual >>= fun selected =>
      StatementBlock.executeWith { read := read } assignment layout.fields 0 7
        (bindings analysis bound outside) (if selected then [.return (some (.bool false))] else []) >>=
      ReadBlock.resume (fun updated =>
        StatementBlock.executeWith { read := read } assignment layout.fields 0 7 updated
          [.assign (.unary .dereference (ident "bound"))
            (.index (analysisField "bounds") (analysisField "root")),
           .return (some (.bool true))])) = _
  rw [read_guard]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind, ReadExpressions.truth]
  congr 1
  funext refused
  cases refused with
  | true => rfl
  | false => exact suffix_keeps_publication layout analysis bound outside

private theorem command_keeps_guard_and_publication (layout : Layout)
    (analysis bound : Option Ptr) :
    command layout analysis bound =
      (rejected layout analysis bound >>= fun refused =>
        if refused then pure false else publication layout analysis bound >>= fun _ => pure true) := by
  unfold command rejected statusRefused publication selectedValue
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind,
    BindSchedule.bind_boolean_choice, ↓reduceIte]
  congr 1
  funext missingAnalysis
  cases missingAnalysis with
  | true => rfl
  | false =>
      apply congrArg (Prog.bind (CProg.ptrEq bound none))
      funext missingBound
      cases missingBound with
      | true => rfl
      | false =>
          cases analysis with
          | none => exact (ReadExpressions.undefined_bind _).symm
          | some address =>
              simp only [Prog.bind_assoc, Prog.ret_bind, Bool.false_eq_true, if_false]
              apply congrArg (Prog.bind (CProg.loadI32 (address + layout.status)))
              funext status
              by_cases refused : (status != 1) = true
              · simp only [if_pos refused]
              · simp only [if_neg refused]
                apply congrArg (Prog.bind (CProg.loadPtr (address + layout.bounds)))
                funext array
                apply congrArg (Prog.bind (CProg.loadU64 (address + layout.root)))
                funext root
                cases array with
                | none => exact (ReadExpressions.undefined_bind _).symm
                | some array =>
                    apply congrArg (Prog.bind (CProg.loadU64 (array + root.toNat)))
                    funext value
                    cases bound with
                    | none => exact (ReadExpressions.undefined_bind _).symm
                    | some bound => rfl

/-- The source function is compared with independently written primitives.
All early refusals, read ordering, full-width data and destination stores stay
in the operation tree; no answer-only observer supplies this equality. -/
theorem source_executes_ordered_command (layout : Layout) (analysis bound : Option Ptr)
    (outside : ReadExpressions.Environment) :
    execute layout analysis bound outside =
      (command layout analysis bound >>= fun accepted =>
        pure (report (bindings analysis bound outside) accepted)) := by
  rw [guard_keeps_selected_body, command_keeps_guard_and_publication]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind,
    BindSchedule.bind_boolean_choice]

def fromOriginal (layout : Layout) (analysis bound : Option Ptr)
    (outside : ReadExpressions.Environment) : CProg CVal ReadBlock.Result :=
  StatementBlock.executeParsedBody
    (StatementBlock.executeWith { read := read } assignment layout.fields 0 8
      (bindings analysis bound outside))
    (qualifiedFunctionText? names source.toList)

theorem original_source_executes_ordered_command (layout : Layout) (analysis bound : Option Ptr)
    (outside : ReadExpressions.Environment) :
    fromOriginal layout analysis bound outside =
      (command layout analysis bound >>= fun accepted =>
        pure (report (bindings analysis bound outside) accepted)) := by
  unfold fromOriginal
  rw [original_source_recognized, StatementBlock.execute_parsed_body_some]
  exact source_executes_ordered_command layout analysis bound outside


section Physical

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

variable {L : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- Held analysis header, exactly typed source fields and the selected memo
cell. A separate destination owns its whole cell even before initialization.
Native byte stride, alignment and the complete array extent remain adapter
obligations; the logical offsets are not invented byte addresses. -/
def dataMemory (layout : Layout) (analysis : Ptr) (cells : Nat) (status : Int32)
    (array : Ptr) (root value : UInt64) : Heap L → Prop :=
  LiveBlock analysis.block cells ∗
    (PointsTo (analysis + layout.status) (.i32 status) ∗
      (PointsTo (analysis + layout.bounds) (.ptr (some array)) ∗
        (PointsTo (analysis + layout.root) (.u64 root) ∗
          PointsTo (array + root.toNat) (.u64 value))))

private theorem data_status_read (layout : Layout) (analysis : Ptr) (cells : Nat)
    (status : Int32) (array : Ptr) (root value : UInt64) (heap : Heap L)
    (held : dataMemory layout analysis cells status array root value heap) :
    CellPermission.read ((heap (analysis + layout.status).block).2
      (analysis + layout.status).offset) = some (some (CVal.i32 status)) :=
  read_framed_right held (fun _ fields => read_of_pointsTo fields)

private theorem data_bounds_read (layout : Layout) (analysis : Ptr) (cells : Nat)
    (status : Int32) (array : Ptr) (root value : UInt64) (heap : Heap L)
    (held : dataMemory layout analysis cells status array root value heap) :
    CellPermission.read ((heap (analysis + layout.bounds).block).2
      (analysis + layout.bounds).offset) = some (some (CVal.ptr (some array))) :=
  read_framed_right held (fun _ fields =>
    read_framed_right fields (fun _ later => read_of_pointsTo later))

private theorem data_root_read (layout : Layout) (analysis : Ptr) (cells : Nat)
    (status : Int32) (array : Ptr) (root value : UInt64) (heap : Heap L)
    (held : dataMemory layout analysis cells status array root value heap) :
    CellPermission.read ((heap (analysis + layout.root).block).2
      (analysis + layout.root).offset) = some (some (CVal.u64 root)) :=
  read_framed_right held (fun _ fields =>
    read_framed_right fields (fun _ later =>
      read_framed_right later (fun _ last => read_of_pointsTo last)))

private theorem data_value_read (layout : Layout) (analysis : Ptr) (cells : Nat)
    (status : Int32) (array : Ptr) (root value : UInt64) (heap : Heap L)
    (held : dataMemory layout analysis cells status array root value heap) :
    CellPermission.read ((heap (array + root.toNat).block).2
      (array + root.toNat).offset) = some (some (CVal.u64 value)) :=
  read_framed_right held (fun _ fields =>
    read_framed_right fields (fun _ later =>
      read_framed_right later (fun _ last => read_of_pointsTo_right last)))

private theorem data_valid (layout : Layout) (analysis : Ptr) (cells : Nat)
    (status : Int32) (array : Ptr) (root value : UInt64) (bound : Ptr)
    (inside : analysis.offset ≤ cells) (heap : Heap L)
    (held : (dataMemory layout analysis cells status array root value ∗ PointsToAny bound) heap) :
    ValidOpt heap (some analysis) := by
  have rearranged : (LiveBlock analysis.block cells ∗
      ((PointsTo (analysis + layout.status) (.i32 status) ∗
        (PointsTo (analysis + layout.bounds) (.ptr (some array)) ∗
          (PointsTo (analysis + layout.root) (.u64 root) ∗
            PointsTo (array + root.toNat) (.u64 value)))) ∗ PointsToAny bound)) heap := by
    simpa only [dataMemory, sepConj_assoc] using held
  exact valid_of_liveBlock rearranged inside

private theorem destination_valid (layout : Layout) (analysis : Ptr) (cells : Nat)
    (status : Int32) (array : Ptr) (root value : UInt64) (bound : Ptr) (heap : Heap L)
    (held : (dataMemory layout analysis cells status array root value ∗ PointsToAny bound) heap) :
    ValidOpt heap (some bound) :=
  valid_of_pointsToAny (p := bound) (F := dataMemory layout analysis cells status array root value)
    (by rw [sepConj_comm]; exact held)

private theorem selected_value_rule (layout : Layout) (analysis : Ptr) (cells : Nat)
    (status : Int32) (array : Ptr) (root value : UInt64) (bound : Ptr) :
    CTriple (L := L)
      (dataMemory layout analysis cells status array root value ∗ PointsToAny bound)
      (selectedValue layout (some analysis))
      (fun actual heap => actual = value ∧
        (dataMemory layout analysis cells status array root value ∗ PointsToAny bound) heap) := by
  unfold selectedValue
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadPtr_rule (q := some array) fun _ held =>
    read_framed held (data_bounds_read layout analysis cells status array root value)) fun actualArray => ?_
  apply triple_pure
  intro sameArray
  subst actualArray
  refine triple_bind _ (loadU64_rule (n := root) fun _ held =>
    read_framed held (data_root_read layout analysis cells status array root value)) fun actualRoot => ?_
  apply triple_pure
  intro sameRoot
  subst actualRoot
  exact loadU64_rule (n := value) fun _ held =>
    read_framed held (data_value_read layout analysis cells status array root value)

private theorem publication_rule (layout : Layout) (analysis : Ptr) (cells : Nat)
    (status : Int32) (array : Ptr) (root value : UInt64) (bound : Ptr) :
    CTriple (L := L)
      (dataMemory layout analysis cells status array root value ∗ PointsToAny bound)
      (publication layout (some analysis) (some bound))
      (fun _ => dataMemory layout analysis cells status array root value ∗
        PointsTo bound (CVal.u64 value)) := by
  unfold publication
  simp only [Prog.bind_eq]
  refine triple_bind _ (selected_value_rule layout analysis cells status array root value bound)
    fun actualValue => ?_
  apply triple_pure
  intro sameValue
  subst actualValue
  exact frame_left (store_spec bound (CVal.u64 value))
    (dataMemory layout analysis cells status array root value)

private theorem rejected_rule (layout : Layout) (analysis : Ptr) (cells : Nat)
    (status : Int32) (array : Ptr) (root value : UInt64) (bound : Ptr)
    (inside : analysis.offset ≤ cells) :
    CTriple (L := L)
      (dataMemory layout analysis cells status array root value ∗ PointsToAny bound)
      (rejected layout (some analysis) (some bound))
      (fun refused heap => refused = (status != 1) ∧
        (dataMemory layout analysis cells status array root value ∗ PointsToAny bound) heap) := by
  unfold rejected statusRefused
  simp only [Prog.bind_eq]
  refine triple_bind _ (ptrEq_rule (p := some analysis) (q := none)
    (fun heap held => ⟨data_valid layout analysis cells status array root value bound inside heap held,
      trivial⟩)) fun missingAnalysis => ?_
  apply triple_pure
  intro actualMissing
  have nonnull : missingAnalysis = false := by simpa using actualMissing
  subst missingAnalysis
  refine triple_bind _ (ptrEq_rule (p := some bound) (q := none)
    (fun heap held => ⟨destination_valid layout analysis cells status array root value bound heap held,
      trivial⟩)) fun missingBound => ?_
  apply triple_pure
  intro actualMissing
  have nonnull : missingBound = false := by simpa using actualMissing
  subst missingBound
  refine triple_bind _ (loadI32_rule (n := status) fun _ held =>
    read_framed held (data_status_read layout analysis cells status array root value)) fun savedStatus => ?_
  apply triple_pure
  intro sameStatus
  subst savedStatus
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩)
    (triple_ret act (status != 1) (fun refused heap => refused = (status != 1) ∧
      (dataMemory layout analysis cells status array root value ∗ PointsToAny bound) heap))

/-- A completed cost state publishes the full stored uint64_t value while
retaining separately owned graph memory. The destination need not have an
initialized old value. This realizes the source interpreter's memory action,
not the compiler, ABI or whole traversal. -/
theorem completed_state_publishes_held_value (layout : Layout) (analysis : Ptr) (cells : Nat)
    (array : Ptr) (root value : UInt64) (bound : Ptr) (inside : analysis.offset ≤ cells) :
    CTriple (L := L)
      (dataMemory layout analysis cells 1 array root value ∗ PointsToAny bound)
      (command layout (some analysis) (some bound))
      (fun accepted heap => accepted = true ∧
        (dataMemory layout analysis cells 1 array root value ∗ PointsTo bound (CVal.u64 value)) heap) := by
  rw [command_keeps_guard_and_publication]
  simp only [Prog.bind_eq]
  refine triple_bind _ (rejected_rule layout analysis cells 1 array root value bound inside)
    fun refused => ?_
  apply triple_pure
  intro actualRefusal
  have accepted : refused = false := by simpa using actualRefusal
  subst refused
  refine triple_bind _ (publication_rule layout analysis cells 1 array root value bound) fun _ => ?_
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩)
    (triple_ret act true (fun accepted heap => accepted = true ∧
      (dataMemory layout analysis cells 1 array root value ∗ PointsTo bound (CVal.u64 value)) heap))

/-- Refusal preserves the entire owned destination and analysis assertions.
No initialized destination value or invented completed answer is read. -/
theorem unfinished_state_leaves_destination_unwritten (layout : Layout)
    (analysis : Ptr) (cells : Nat) (status : Int32) (array : Ptr) (root value : UInt64)
    (bound : Ptr) (inside : analysis.offset ≤ cells) (unfinished : (status != 1) = true) :
    CTriple (L := L)
      (dataMemory layout analysis cells status array root value ∗ PointsToAny bound)
      (command layout (some analysis) (some bound))
      (fun accepted heap => accepted = false ∧
        (dataMemory layout analysis cells status array root value ∗ PointsToAny bound) heap) := by
  rw [command_keeps_guard_and_publication]
  simp only [Prog.bind_eq]
  refine triple_bind _ (rejected_rule layout analysis cells status array root value bound inside)
    fun refused => ?_
  apply triple_pure
  intro actualRefusal
  have rejected : refused = true := actualRefusal.trans unfinished
  subst refused
  simp only [unfinished, ↓reduceIte]
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩)
    (triple_ret act false (fun accepted heap => accepted = false ∧
      (dataMemory layout analysis cells status array root value ∗ PointsToAny bound) heap))


/-- The complete source return retains its whole immutable lexical context,
while the physical store updates only the separately owned destination. -/
theorem completed_source_preserves_context_and_publishes (layout : Layout)
    (analysis : Ptr) (cells : Nat) (array : Ptr) (root value : UInt64) (bound : Ptr)
    (inside : analysis.offset ≤ cells) (outside : ReadExpressions.Environment) :
    CTriple (L := L)
      (dataMemory layout analysis cells 1 array root value ∗ PointsToAny bound)
      (fromOriginal layout (some analysis) (some bound) outside)
      (fun returned heap => returned = report (bindings (some analysis) (some bound) outside) true ∧
        (dataMemory layout analysis cells 1 array root value ∗ PointsTo bound (CVal.u64 value)) heap) := by
  rw [original_source_executes_ordered_command]
  simp only [Prog.bind_eq]
  refine triple_bind _ (completed_state_publishes_held_value layout analysis cells array root value bound inside)
    fun accepted => ?_
  apply triple_pure
  intro completed
  subst accepted
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩)
    (triple_ret act (report (bindings (some analysis) (some bound) outside) true)
      (fun returned heap => returned = report (bindings (some analysis) (some bound) outside) true ∧
        (dataMemory layout analysis cells 1 array root value ∗ PointsTo bound (CVal.u64 value)) heap))

/-- Given the separately established stored-state representation, the actual
source readout publishes an independently derived graph cost. The recurrence
certificate is supplied by the common graph machine, not by the returned word.
This theorem does not establish the native traversal's representation invariant. -/
theorem completed_source_reports_independently_derived_cost
    (graph : Mettapedia.Algorithms.WellFoundedServices.OccurrenceGraph.Graph)
    (maximum : Nat) (state : Mettapedia.Algorithms.WellFoundedServices.OccurrenceGraph.State)
    (layout : Layout) (analysis : Ptr) (cells : Nat) (array : Ptr) (root value : UInt64)
    (bound : Ptr) (inside : analysis.offset ≤ cells) (outside : ReadExpressions.Environment)
    (valid : Mettapedia.Algorithms.WellFoundedServices.OccurrenceGraph.Valid graph maximum state)
    (representedRoot : root.toNat = state.root)
    (reported : Mettapedia.Algorithms.WellFoundedServices.OccurrenceGraph.bound? state = some value.toNat) :
    CTriple (L := L)
      (dataMemory layout analysis cells 1 array root value ∗ PointsToAny bound)
      (fromOriginal layout (some analysis) (some bound) outside)
      (fun returned heap => returned = report (bindings (some analysis) (some bound) outside) true ∧
        graph.Derived root.toNat value.toNat ∧ value.toNat ≤ maximum ∧
        (dataMemory layout analysis cells 1 array root value ∗ PointsTo bound (CVal.u64 value)) heap) := by
  obtain ⟨derived, within⟩ :=
    Mettapedia.Algorithms.WellFoundedServices.OccurrenceGraph.bound_derived
      graph maximum state value.toNat valid reported
  refine triple_post _
    (completed_source_preserves_context_and_publishes layout analysis cells array root value bound inside outside) ?_
  rintro returned heap ⟨returnedSame, held⟩
  exact ⟨returnedSame, by simpa only [representedRoot] using derived, within, held⟩

/-- The independently defined complete-unfolding metric is justified under
acyclicity. Physical work with Need sharing and the event account are different
observers and receive no equality from this cost readout. -/
theorem completed_source_reports_unfolding_cost
    (graph : Mettapedia.Algorithms.WellFoundedServices.OccurrenceGraph.Graph)
    (maximum : Nat) (state : Mettapedia.Algorithms.WellFoundedServices.OccurrenceGraph.State)
    (layout : Layout) (analysis : Ptr) (cells : Nat) (array : Ptr) (root value : UInt64)
    (bound : Ptr) (inside : analysis.offset ≤ cells) (outside : ReadExpressions.Environment)
    (acyclic : graph.catalogue.Acyclic)
    (valid : Mettapedia.Algorithms.WellFoundedServices.OccurrenceGraph.Valid graph maximum state)
    (representedRoot : root.toNat = state.root)
    (reported : Mettapedia.Algorithms.WellFoundedServices.OccurrenceGraph.bound? state = some value.toNat) :
    CTriple (L := L)
      (dataMemory layout analysis cells 1 array root value ∗ PointsToAny bound)
      (fromOriginal layout (some analysis) (some bound) outside)
      (fun returned heap => returned = report (bindings (some analysis) (some bound) outside) true ∧
        value.toNat = graph.catalogue.unfoldingWork acyclic
          (fun node => (graph.rows node).length) root.toNat ∧ value.toNat ≤ maximum ∧
        (dataMemory layout analysis cells 1 array root value ∗ PointsTo bound (CVal.u64 value)) heap) := by
  obtain ⟨metric, within⟩ :=
    Mettapedia.Algorithms.WellFoundedServices.OccurrenceGraph.bound_unfoldingWork
      graph maximum state value.toNat acyclic valid reported
  refine triple_post _
    (completed_source_preserves_context_and_publishes layout analysis cells array root value bound inside outside) ?_
  rintro returned heap ⟨returnedSame, held⟩
  exact ⟨returnedSame, by simpa only [representedRoot] using metric, within, held⟩

/-- A separately owned initialized cell cannot also be a second copy of the
same memo cell. Textual names or const qualification cannot supply separation. -/
theorem alias_is_not_independent_ownership (address : Ptr) (memo destination : UInt64)
    (heap : Heap L) :
    ¬ (PointsTo address (CVal.u64 memo) ∗ PointsTo address (CVal.u64 destination)) heap :=
  pointsTo_sepConj_self_false address (CVal.u64 memo) (CVal.u64 destination) heap

end Physical


namespace PhysicalControls

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

abbrev Permission := Excl (Option CVal)

def layout : Layout := ⟨0, 1, 2⟩
def analysis : Ptr := ⟨71, 0⟩
def array : Ptr := ⟨71, 3⟩
def destination : Ptr := ⟨71, 4⟩
def value : UInt64 := UInt64.ofNat (2 ^ 63 + 17)
def outside : ReadExpressions.Environment := fun _ => none

def dataCells : List (Option CVal) :=
  [some (.i32 1), some (.ptr (some array)), some (.u64 0), some (.u64 value)]
def initialCells : List (Option CVal) := dataCells ++ [none]

def initialHeap : Heap Permission :=
  atBlock analysis.block (.own ⟨5, true⟩, segment analysis.offset (initialCells.map CellPermission.whole))

def held : Heap Permission → Prop :=
  dataMemory layout analysis 5 1 array 0 value ∗ PointsToAny destination

def resultMemory : Heap Permission → Prop :=
  dataMemory layout analysis 5 1 array 0 value ∗ PointsTo destination (CVal.u64 value)

private theorem four_cells_are_actual_fields :
    dataMemory (L := Permission) layout analysis 5 1 array 0 value =
      (LiveBlock analysis.block 5 ∗ Cells analysis dataCells) := by
  rw [show dataCells = [some (CVal.i32 1), some (.ptr (some array)),
      some (.u64 0), some (.u64 value)] from rfl]
  rw [cells_cons analysis (some (CVal.i32 1))
      [some (.ptr (some array)), some (.u64 0), some (.u64 value)],
    cells_cons (analysis + 1) (some (CVal.ptr (some array)))
      [some (.u64 0), some (.u64 value)],
    cells_cons (analysis + 1 + 1) (some (CVal.u64 0)) [some (.u64 value)]]
  rfl

/-- The qualified publication premise has an explicit nonempty heap. Its
last whole cell is indeterminate, not a fabricated initialized value. -/
theorem owned_precondition_is_inhabited : held initialHeap := by
  have whole : (LiveBlock (L := Permission) analysis.block 5 ∗
      Cells analysis initialCells) initialHeap := by
    change (LiveBlock (L := Permission) 71 5 ∗ Cells (⟨71, 0⟩ : Ptr) initialCells) initialHeap
    rw [liveBlock_cells_iff]
    rfl
  have split : Cells (L := Permission) analysis initialCells =
      (Cells analysis dataCells ∗ Cells destination [none]) := by
    rw [initialCells, cells_append]
    rfl
  rw [split, ← sepConj_assoc, ← four_cells_are_actual_fields] at whole
  obtain ⟨left, right, separate, total, first, last⟩ := whole
  exact ⟨left, right, separate, total, first, ⟨none, last⟩⟩

/-- The parsed source has an actual run on the inhabited heap. It publishes
the same wide value, returns the complete context and retains graph ownership. -/
theorem actual_source_runs_with_indeterminate_destination :
    ∃ finalHeap,
      (fromOriginal layout (some analysis) (some destination) outside).Runs act initialHeap
        (report (bindings (some analysis) (some destination) outside) true) finalHeap ∧
      resultMemory finalHeap := by
  have specification : CTriple (L := Permission) held
      (fromOriginal layout (some analysis) (some destination) outside)
      (fun returned heap => returned = report (bindings (some analysis) (some destination) outside) true ∧
        resultMemory heap) := completed_source_preserves_context_and_publishes
    (L := Permission) layout analysis 5 array 0 value destination
      (by change 0 ≤ (5 : Nat); exact Nat.zero_le _) outside
  rw [original_source_executes_ordered_command] at specification ⊢
  obtain ⟨returned, finalHeap, ran⟩ := Mettapedia.Machines.CMemory.exists_runs
    _ initialHeap (specification initialHeap owned_precondition_is_inhabited).1
  obtain ⟨same, kept⟩ := (specification initialHeap owned_precondition_is_inhabited).2 returned finalHeap ran
  subst returned
  exact ⟨finalHeap, ran, kept⟩

theorem published_word_is_above_narrow_range : value.toNat = 2 ^ 63 + 17 := by
  decide +kernel

/-- An alias to the same selected memo cell is not separate destination
ownership. The readout theorem cannot be invoked by renaming that alias. -/
theorem aliased_memo_does_not_supply_two_cells (heap : Heap Permission) :
    ¬ (PointsTo array (CVal.u64 value) ∗ PointsTo array (CVal.u64 0)) heap :=
  alias_is_not_independent_ownership array value 0 heap

end PhysicalControls

end Mettapedia.Languages.MeTTa.CeTTaNativeCost.GraphBoundSource
