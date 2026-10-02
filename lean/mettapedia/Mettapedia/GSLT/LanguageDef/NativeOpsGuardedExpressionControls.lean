import Mettapedia.GSLT.LanguageDef.NativeOpsGuardedExpressionCorrespondence

/-! Numeric refusal, ordered faults, and local-profile controls for actual lowering. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.GuardedExpressionControls

open NativeIR (Instruction)
open NativeWord64 (Word Fault WordOp)

def wordBinary (operation : WordOp) (left right : Word) : Expr :=
  .binary (.word operation) (.word left) (.word right)

def wordBinaryOutput (operation : WordOp) (left right : Word) : NativeLowering.Expression :=
  ⟨[.temporary 1 .word (.word (NativeWord64.encode left)),
      .temporary 2 .word (.word (NativeWord64.encode right))] ++
      NativeLowering.numericGuard (.word operation) (.temporary 2 .word) ++
      [.temporary 3 .word (.binary (.word operation) (.temporary 1 .word) (.temporary 2 .word))],
    .temporary 3 .word, ⟨3⟩⟩

theorem word_binary_guarded (operation : WordOp) (left right : Word) :
    SourceGuardedExpression (wordBinary operation left right) :=
  .binary (.word operation) (.leaf (.word left)) (.leaf (.word right))

theorem word_binary_actual_emission (interface : Interface) (scope : Scope)
    (operation : WordOp) (left right : Word) :
    NativeLowering.expression? interface scope (wordBinary operation left right) ⟨0⟩ =
      some (wordBinaryOutput operation left right) := by
  simp [wordBinary, wordBinaryOutput, NativeLowering.expression?, NativeLowering.prependCode,
    NativeLowering.pureTemporary, inferExpr, binaryType, NativeIR.fresh]

private theorem word_source_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (word : Word) (state : SourceState World) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame (.word word) state out ↔
      out = ⟨.ok (.word word), state⟩ :=
  source_operand_free_expression_exact _ rfl _ _

theorem word_binary_source_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (operation : WordOp) (left right : Word) (state : SourceState World)
    (clear : state.fault = none) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame (wordBinary operation left right) state out ↔
      out = sourceFinish state ((NativeWord64.sourceBinary operation left right).map SourceValue.word) := by
  unfold wordBinary
  rw [source_guarded_binary_exact (.word operation) (.leaf (.word left)) (.leaf (.word right)) state clear out]
  constructor
  · rintro (⟨first, second, computed, leftRan, rightRan, executed, same⟩ |
      ⟨fault, leftRan, same⟩ | ⟨first, fault, leftRan, rightRan, same⟩)
    · cases (word_source_exact interface heap calls frame left state _).mp leftRan
      cases (word_source_exact interface heap calls frame right state _).mp rightRan
      cases Option.some.inj executed
      exact same
    · cases (word_source_exact interface heap calls frame left state _).mp leftRan
    · cases (word_source_exact interface heap calls frame right state _).mp rightRan
  · intro same
    exact .inl ⟨.word left, .word right, _,
      .strict rfl (.nil state) rfl, .strict rfl (.nil state) rfl, rfl, same⟩

theorem word_binary_executes {SourceWorld TargetWorld : Type}
    {related : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated related source target)
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    (bounded : TemporaryNamesBound targetFrame 0) (result : NativeType)
    {default : TargetValue} (zero : TargetZero interface result default)
    (root : List Instruction) (operation : WordOp) (left right : Word) :
    ∃ out observed,
      TargetRun interface targetHeap targetCalls result root (wordBinaryOutput operation left right).code
        targetFrame target out ∧
      targetExpressionObservation interface (wordBinaryOutput operation left right).result out observed ∧
      OutcomeRelated related
        (sourceFinish source ((NativeWord64.sourceBinary operation left right).map SourceValue.word)) observed := by
  obtain ⟨out, observed, ran, observation, _, _, _, _, correspondence⟩ :=
    guarded_expression_preservation sourceHeap sourceCalls targetHeap targetCalls frames states clear tagged
      result zero root (word_binary_guarded operation left right)
      (word_binary_actual_emission interface (sourceFrameScope sourceFrame) operation left right) bounded
      ((word_binary_source_exact interface sourceHeap sourceCalls sourceFrame operation left right source clear _).mpr rfl)
  exact ⟨out, observed, ran, observation, correspondence⟩

theorem word_binary_has_no_extra_result {SourceWorld TargetWorld : Type}
    {related : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated related source target)
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    (bounded : TemporaryNamesBound targetFrame 0) (result : NativeType)
    {default : TargetValue} (zero : TargetZero interface result default)
    (root : List Instruction) (operation : WordOp) (left right : Word)
    {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root (wordBinaryOutput operation left right).code
      targetFrame target out)
    (observation : targetExpressionObservation interface (wordBinaryOutput operation left right).result out observed) :
    OutcomeRelated related
      (sourceFinish source ((NativeWord64.sourceBinary operation left right).map SourceValue.word)) observed := by
  obtain ⟨sourceOut, sourceRan, _, _, _, _, correspondence⟩ :=
    guarded_expression_reflection sourceHeap sourceCalls targetHeap targetCalls frames states clear tagged
      result zero root (word_binary_guarded operation left right)
      (word_binary_actual_emission interface (sourceFrameScope sourceFrame) operation left right)
      bounded ran observation
  cases (word_binary_source_exact interface sourceHeap sourceCalls sourceFrame operation left right source clear _).mp sourceRan
  exact correspondence

theorem near_word_boundary_and_guards :
    NativeWord64.sourceBinary .div (NativeWord64.bounded 64 (2 ^ 64 - 1)) 255 =
        .ok (NativeWord64.bounded 64 ((2 ^ 64 - 1) / 255)) ∧
    NativeWord64.sourceBinary .mod (NativeWord64.bounded 64 (2 ^ 64 - 1)) 255 = .ok 0 ∧
    NativeWord64.sourceBinary .shl 1 63 = .ok (NativeWord64.bounded 64 (2 ^ 63)) ∧
    NativeWord64.sourceBinary .shr (NativeWord64.bounded 64 (2 ^ 64 - 1)) 63 = .ok 1 ∧
    NativeWord64.sourceBinary .div 7 0 = .error .divisionByZero ∧
    NativeWord64.sourceBinary .mod 7 0 = .error .divisionByZero ∧
    NativeWord64.sourceBinary .shl 1 64 = .error .shiftOutOfRange ∧
    NativeWord64.sourceBinary .shr 1 64 = .error .shiftOutOfRange := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem division_zero_observable_refusal {SourceWorld TargetWorld : Type}
    {related : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated related source target)
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    (bounded : TemporaryNamesBound targetFrame 0) (result : NativeType)
    {default : TargetValue} (zero : TargetZero interface result default)
    (root : List Instruction) {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root (wordBinaryOutput .div 7 0).code
      targetFrame target out)
    (observation : targetExpressionObservation interface (wordBinaryOutput .div 7 0).result out observed) :
    observed.result = .error .divisionByZero := by
  have correspondence := word_binary_has_no_extra_result sourceHeap sourceCalls targetHeap targetCalls
    frames states clear tagged bounded result zero root .div 7 0 ran observation
  have computed : NativeWord64.sourceBinary .div 7 0 = .error .divisionByZero := rfl
  simpa only [computed, sourceFinish, sourceObserve, sourcePoison, clear, Except.map] using correspondence.result

theorem shift_64_observable_refusal {SourceWorld TargetWorld : Type}
    {related : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated related source target)
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    (bounded : TemporaryNamesBound targetFrame 0) (result : NativeType)
    {default : TargetValue} (zero : TargetZero interface result default)
    (root : List Instruction) {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root (wordBinaryOutput .shl 1 64).code
      targetFrame target out)
    (observation : targetExpressionObservation interface (wordBinaryOutput .shl 1 64).result out observed) :
    observed.result = .error .shiftOutOfRange := by
  have correspondence := word_binary_has_no_extra_result sourceHeap sourceCalls targetHeap targetCalls
    frames states clear tagged bounded result zero root .shl 1 64 ran observation
  have computed : NativeWord64.sourceBinary .shl 1 64 = .error .shiftOutOfRange := rfl
  simpa only [computed, sourceFinish, sourceObserve, sourcePoison, clear, Except.map] using correspondence.result

def divisionFirst : Expr := .binary (.word .add) (wordBinary .div 7 0) (wordBinary .shl 1 64)
def shiftFirst : Expr := .binary (.word .add) (wordBinary .shl 1 64) (wordBinary .div 7 0)

theorem division_first_guarded : SourceGuardedExpression divisionFirst :=
  .binary (.word .add) (word_binary_guarded _ _ _) (word_binary_guarded _ _ _)

theorem shift_first_guarded : SourceGuardedExpression shiftFirst :=
  .binary (.word .add) (word_binary_guarded _ _ _) (word_binary_guarded _ _ _)

private theorem left_fault_source_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {operation : Binary} (scalar : GuardedScalarBinary operation) {left right : Expr}
    (first : SourceGuardedExpression left) (second : SourceGuardedExpression right)
    (state : SourceState World) (clear : state.fault = none) (fault : Fault)
    (leftExact : ∀ out, SourceExprEval interface heap calls frame left state out ↔
      out = ⟨.error fault, sourcePoison state fault⟩) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame (.binary operation left right) state out ↔
      out = ⟨.error fault, sourcePoison state fault⟩ := by
  rw [source_guarded_binary_exact scalar first second state clear out]
  constructor
  · rintro (⟨firstValue, secondValue, computed, leftRan, _, _, same⟩ |
      ⟨actualFault, leftRan, same⟩ | ⟨firstValue, actualFault, leftRan, _, same⟩)
    · cases (leftExact _).mp leftRan
    · have actual := (leftExact _).mp leftRan
      cases Except.error.inj (congrArg SourceOutcome.result actual)
      exact same
    · cases (leftExact _).mp leftRan
  · intro same
    exact .inr (.inl ⟨fault, (leftExact _).mpr rfl, same⟩)

theorem division_first_source_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (state : SourceState World) (clear : state.fault = none) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame divisionFirst state out ↔
      out = ⟨.error .divisionByZero, sourcePoison state .divisionByZero⟩ := by
  apply left_fault_source_exact (.word .add) (word_binary_guarded _ _ _) (word_binary_guarded _ _ _)
    state clear .divisionByZero ?_ out
  intro outcome
  have computed : NativeWord64.sourceBinary .div 7 0 = .error .divisionByZero := rfl
  simpa only [computed, sourceFinish, Except.map, sourceObserve, sourcePoison, clear] using
    word_binary_source_exact interface heap calls frame .div 7 0 state clear outcome

theorem shift_first_source_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (state : SourceState World) (clear : state.fault = none) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame shiftFirst state out ↔
      out = ⟨.error .shiftOutOfRange, sourcePoison state .shiftOutOfRange⟩ := by
  apply left_fault_source_exact (.word .add) (word_binary_guarded _ _ _) (word_binary_guarded _ _ _)
    state clear .shiftOutOfRange ?_ out
  intro outcome
  have computed : NativeWord64.sourceBinary .shl 1 64 = .error .shiftOutOfRange := rfl
  simpa only [computed, sourceFinish, Except.map, sourceObserve, sourcePoison, clear] using
    word_binary_source_exact interface heap calls frame .shl 1 64 state clear outcome

/-- These are the two scalar guarded subexpressions in the authored kernel. -/
theorem term_number_shift_supported :
    SourceGuardedExpression (.binary (.word .shr) (.variable "rest") (.word 8)) :=
  .binary (.word .shr) (.leaf (.variable _)) (.leaf (.word _))

theorem literal_division_supported :
    SourceGuardedExpression (.binary (.word .div) (.variable "a") (.variable "b")) :=
  .binary (.word .div) (.leaf (.variable _)) (.leaf (.variable _))

/-- This is the JIT scalar suffix after a separately validated byte read. -/
theorem jit_scalar_byte_shift_supported (byte : NativeWord64.Byte) :
    SourceGuardedExpression (.binary (.word .shl) (.unary .toWord (.byte byte))
      (.binary (.word .mul) (.variable "i") (.word 8))) :=
  .binary (.word .shl) (.unary .toWord (.leaf (.byte byte)))
    (.binary (.word .mul) (.leaf (.variable _)) (.leaf (.word _)))

theorem indexed_jit_byte_requires_memory_composition :
    ¬ SourceGuardedExpression (.binary (.word .shl)
      (.unary .toWord (.index (.variable "length-bytes") (.variable "i")))
      (.binary (.word .mul) (.variable "i") (.word 8))) := by
  intro guarded
  cases guarded with
  | leaf leaf => cases leaf
  | binary _ first _ =>
      cases first with
      | leaf leaf => cases leaf
      | unary _ indexed =>
          cases indexed with
          | leaf leaf => cases leaf

def malformedSourceFrame : SourceFrame := ⟨0, 1, [⟨"lhs", .word, 0⟩]⟩
def malformedTargetFrame : TargetFrame :=
  ⟨0, 1, [⟨"lhs", .word, 0⟩], [], fun _ => none⟩

def malformedSource : SourceState Unit :=
  { memory := ⟨fun storage index => if storage = 0 ∧ index = 0 then some (.bool true) else none,
      fun storage => if storage = 0 then some 1 else none⟩,
    fault := none, allocatorAvailable := true, releaseAvailable := true, external := (),
    allocatorStats := AllocatorStats.sourceEmpty }

def malformedTarget : TargetState Unit :=
  { memory := ⟨fun storage index => if storage = 0 ∧ index = 0 then some (.bool true) else none,
      fun storage => if storage = 0 then some 1 else none⟩,
    fault := none, allocatorAvailable := true, releaseAvailable := true, external := (),
    allocatorStats := AllocatorStats.targetEmpty }

def malformedDivision : Expr := .binary (.word .div) (.variable "lhs") (.word 0)

theorem malformed_frames_related : FrameRelated malformedSourceFrame malformedTargetFrame :=
  ⟨rfl, rfl, rfl⟩

theorem malformed_states_related :
    StateRelated (fun (left right : Unit) => left = right) malformedSource malformedTarget := by
  refine ⟨⟨?_, ?_⟩, rfl, rfl, rfl, rfl, AllocatorStats.empty_related⟩
  · intro storage index
    by_cases selected : storage = 0 ∧ index = 0 <;>
      simp [malformedSource, malformedTarget, selected]
    rfl
  · intro storage
    by_cases selected : storage = 0 <;>
      simp only [malformedSource, malformedTarget, selected, if_true, if_false,
        Option.map_some, Option.map_none]
    rfl

def malformedOutput : NativeLowering.Expression :=
  ⟨[.temporary 1 .word (.readLocal "lhs"), .temporary 2 .word (.word 0),
    .checkedNumericGuard .div (.temporary 2 .word),
    .temporary 3 .word (.binary (.word .div) (.temporary 1 .word) (.temporary 2 .word))],
    .temporary 3 .word, ⟨3⟩⟩

theorem malformed_division_statically_admitted (interface : Interface) :
    NativeLowering.expression? interface (sourceFrameScope malformedSourceFrame) malformedDivision ⟨0⟩ =
      some malformedOutput := by
  simp [malformedDivision, malformedOutput, malformedSourceFrame, sourceFrameScope,
    NativeLowering.expression?, NativeLowering.prependCode, NativeLowering.pureTemporary,
    NativeLowering.numericGuard, inferExpr, binaryType, lookupVariable, NativeIR.fresh]
  rfl

private theorem malformed_local_source_exact (interface : Interface)
    (heap : SourceHeapSemantics Unit) (calls : SourceCalls Unit) (out : SourceOutcome Unit) :
    SourceExprEval interface heap calls malformedSourceFrame (.variable "lhs") malformedSource out ↔
      out = ⟨.ok (.bool true), malformedSource⟩ := by
  rw [source_operand_free_expression_exact _ rfl]
  change (∃ value, some (.bool true) = some value ∧
    out = ⟨.ok value, malformedSource⟩) ↔ _
  constructor
  · rintro ⟨value, same, exactOut⟩
    cases Option.some.inj same
    exact exactOut
  · intro exactOut
    exact ⟨.bool true, rfl, exactOut⟩

theorem malformed_division_source_stuck (interface : Interface)
    (heap : SourceHeapSemantics Unit) (calls : SourceCalls Unit) (out : SourceOutcome Unit) :
    ¬ SourceExprEval interface heap calls malformedSourceFrame malformedDivision malformedSource out := by
  intro ran
  rcases (source_guarded_binary_exact (.word .div) (.leaf (.variable "lhs")) (.leaf (.word 0))
    malformedSource rfl out).mp ran with
    ⟨first, second, computed, leftRan, rightRan, executed, same⟩ |
    ⟨fault, leftRan, same⟩ | ⟨first, fault, leftRan, rightRan, same⟩
  · cases (malformed_local_source_exact interface heap calls _).mp leftRan
    cases (word_source_exact interface heap calls malformedSourceFrame 0 malformedSource _).mp rightRan
    cases executed
  · cases (malformed_local_source_exact interface heap calls _).mp leftRan
  · cases (word_source_exact interface heap calls malformedSourceFrame 0 malformedSource _).mp rightRan

theorem malformed_locals_are_outside_profile :
    ¬ SourceLocalsTagged malformedSourceFrame malformedSource.memory := by
  intro tagged
  have impossible : SourceOuterTag .word (.bool true) :=
    tagged ⟨"lhs", .word, 0⟩ (by simp [malformedSourceFrame]) (.bool true) rfl
  cases impossible

/-- Without runtime tags, the emitted right guard can fault before an invalid left computation. -/
theorem malformed_division_target_faults (interface : Interface)
    (heap : TargetHeapSemantics Unit) (calls : TargetCalls Unit) (root : List Instruction) :
    ∃ after, TargetRun interface heap calls .word root malformedOutput.code
      malformedTargetFrame malformedTarget
      ⟨.returned (.word 0), after, targetPoison malformedTarget .divisionByZero⟩ := by
  let middle := targetDeclareTemporary malformedTargetFrame 1 (.bool true)
  let after := targetDeclareTemporary middle 2 (.word 0)
  refine ⟨after, .next (.temporary (by rfl) (.local (by rfl)))
    (.next (.temporary (by rfl) (.word 0)) ?_)⟩
  exact .return (.numericFault
    (declared_temporary_atom interface middle malformedTarget 2 .word (.word 0)) rfl .unsignedWord)

end Mettapedia.GSLT.LanguageDef.NativeOps.GuardedExpressionControls
