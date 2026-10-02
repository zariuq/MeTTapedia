import Mettapedia.GSLT.LanguageDef.NativeOpsScalarExpressionLowering

/-! Actual recursive lowering controls at unsigned-word and byte boundaries. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.ScalarExpressionControls

open NativeIR (Instruction)

def largestWord : NativeWord64.Word := NativeWord64.bounded 64 (2 ^ 64 - 1)

def wrapAddition : Expr := .binary (.word .add) (.word largestWord) (.word 1)

def wrapComparison : Expr := .binary (.compare .eq) wrapAddition (.word 0)

def wrapComparisonOutput : NativeLowering.Expression :=
  ⟨[.temporary 1 .word (.word (NativeWord64.encode largestWord)),
    .temporary 2 .word (.word 1),
    .temporary 3 .word (.binary (.word .add) (.temporary 1 .word) (.temporary 2 .word)),
    .temporary 4 .word (.word 0),
    .temporary 5 .bool (.binary (.compare .eq) (.temporary 3 .word) (.temporary 4 .word))],
    .temporary 5 .bool, ⟨5⟩⟩

theorem wrap_addition_scalar : SourceScalarExpression wrapAddition :=
  .binary .add (.leaf (.word _)) (.leaf (.word _))

theorem wrap_comparison_scalar : SourceScalarExpression wrapComparison :=
  .binary (.compare .eq) wrap_addition_scalar (.leaf (.word _))

theorem wrap_comparison_actual_emission (interface : Interface) (scope : Scope) :
    NativeLowering.expression? interface scope wrapComparison ⟨0⟩ = some wrapComparisonOutput := by
  simp [wrapComparison, wrapAddition, wrapComparisonOutput, NativeLowering.expression?,
    NativeLowering.prependCode, NativeLowering.pureTemporary, NativeLowering.numericGuard,
    inferExpr, binaryType, NativeIR.fresh]
  exact ⟨rfl, rfl⟩

private theorem word_source_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (word : NativeWord64.Word) (state : SourceState World) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame (.word word) state out ↔
      out = ⟨.ok (.word word), state⟩ :=
  source_operand_free_expression_exact _ rfl _ _

private theorem word_source {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (word : NativeWord64.Word) (state : SourceState World) :
    SourceExprEval interface heap calls frame (.word word) state ⟨.ok (.word word), state⟩ :=
  .strict rfl (.nil state) rfl

theorem wrap_addition_source_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (state : SourceState World) (clear : state.fault = none) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame wrapAddition state out ↔ out = ⟨.ok (.word 0), state⟩ := by
  have computed : sourceBinaryOp (.word .add) (.word largestWord) (.word 1) = some (.ok (.word 0)) :=
    by rfl
  unfold wrapAddition
  rw [source_scalar_binary_exact .add (.leaf (.word _)) (.leaf (.word _)) state clear out]
  constructor
  · rintro ⟨left, right, value, leftRun, rightRun, actual, same⟩
    cases (word_source_exact interface heap calls frame largestWord state _).mp leftRun
    cases (word_source_exact interface heap calls frame 1 state _).mp rightRun
    cases Option.some.inj (computed.symm.trans actual)
    exact same
  · intro same
    exact ⟨.word largestWord, .word 1, .word 0, word_source _ _ _ _ _ _,
      word_source _ _ _ _ _ _, computed, same⟩

theorem wrap_comparison_source_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (state : SourceState World) (clear : state.fault = none) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame wrapComparison state out ↔ out = ⟨.ok (.bool true), state⟩ := by
  unfold wrapComparison
  rw [source_scalar_binary_exact (.compare .eq) wrap_addition_scalar (.leaf (.word _)) state clear out]
  constructor
  · rintro ⟨left, right, value, leftRun, rightRun, computed, same⟩
    cases (wrap_addition_source_exact interface heap calls frame state clear _).mp leftRun
    cases (word_source_exact interface heap calls frame 0 state _).mp rightRun
    have actual : sourceBinaryOp (.compare .eq) (.word 0) (.word 0) = some (.ok (.bool true)) :=
      by rfl
    cases Option.some.inj (actual.symm.trans computed)
    exact same
  · intro same
    exact ⟨.word 0, .word 0, .bool true,
      (wrap_addition_source_exact _ _ _ _ _ clear _).mpr rfl, word_source _ _ _ _ _ _, rfl, same⟩

/-- The source expression tree emits a five-instruction target fragment. -/
theorem nested_wrap_comparison_executes {SourceWorld TargetWorld : Type}
    {related : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated related source target)
    (clear : source.fault = none) (bounded : TemporaryNamesBound targetFrame 0)
    (scope : Scope) (result : NativeType) (root : List Instruction) :
    ∃ after,
      TargetRun interface targetHeap targetCalls result root wrapComparisonOutput.code targetFrame target
        ⟨.normal, after, target⟩ ∧
      TargetAtomEval interface after target wrapComparisonOutput.result (.bool true) := by
  exact (scalar_expression_value_iff sourceHeap sourceCalls targetHeap targetCalls frames states clear
    result root wrap_comparison_scalar (wrap_comparison_actual_emission interface scope) bounded
    (.bool true)).mp ((wrap_comparison_source_exact _ _ _ _ _ clear _).mpr rfl)

/-- A successful extra result cannot be justified by the same emitted code. -/
theorem nested_wrap_false_has_no_run {SourceWorld TargetWorld : Type}
    {related : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated related source target)
    (clear : source.fault = none) (bounded : TemporaryNamesBound targetFrame 0)
    (scope : Scope) (result : NativeType) (root : List Instruction) :
    ¬ ∃ after,
      TargetRun interface targetHeap targetCalls result root wrapComparisonOutput.code targetFrame target
        ⟨.normal, after, target⟩ ∧
      TargetAtomEval interface after target wrapComparisonOutput.result (.bool false) := by
  intro ran
  have sourceRan := (scalar_expression_value_iff sourceHeap sourceCalls targetHeap targetCalls frames states clear
    result root wrap_comparison_scalar (wrap_comparison_actual_emission interface scope) bounded
    (.bool false)).mpr ran
  cases (wrap_comparison_source_exact interface sourceHeap sourceCalls sourceFrame source clear _).mp sourceRan

def castComparison : Expr := .unary .not
  (.binary (.compare .lt)
    (.unary .toWord (.unary .toByte (.unary .complement (.word 0)))) (.word 255))

def castComparisonOutput : NativeLowering.Expression :=
  ⟨[.temporary 1 .word (.word 0),
    .temporary 2 .word (.unary .complement (.temporary 1 .word)),
    .temporary 3 .byte (.unary .toByte (.temporary 2 .word)),
    .temporary 4 .word (.unary .toWord (.temporary 3 .byte)),
    .temporary 5 .word (.word 255),
    .temporary 6 .bool (.binary (.compare .lt) (.temporary 4 .word) (.temporary 5 .word)),
    .temporary 7 .bool (.unary .not (.temporary 6 .bool))], .temporary 7 .bool, ⟨7⟩⟩

theorem cast_comparison_scalar : SourceScalarExpression castComparison :=
  .unary .not (.binary (.compare .lt)
    (.unary .toWord (.unary .toByte (.unary .complement (.leaf (.word _))))) (.leaf (.word _)))

theorem cast_comparison_actual_emission (interface : Interface) (scope : Scope) :
    NativeLowering.expression? interface scope castComparison ⟨0⟩ = some castComparisonOutput := by
  simp [castComparison, castComparisonOutput, NativeLowering.expression?,
    NativeLowering.prependCode, NativeLowering.pureTemporary, NativeLowering.numericGuard,
    inferExpr, binaryType, unaryType, NativeIR.fresh]
  exact ⟨rfl, rfl⟩

theorem cast_comparison_source {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (state : SourceState World) (clear : state.fault = none) :
    SourceExprEval interface heap calls frame castComparison state ⟨.ok (.bool true), state⟩ := by
  have complement : SourceExprEval interface heap calls frame (.unary .complement (.word 0)) state
      ⟨.ok (.word largestWord), state⟩ :=
    .strict rfl (.cons (word_source _ _ _ _ _ _) (.nil state))
      ⟨.word largestWord, by rfl, rfl⟩
  have byte : SourceExprEval interface heap calls frame
      (.unary .toByte (.unary .complement (.word 0))) state ⟨.ok (.byte 255), state⟩ :=
    .strict rfl (.cons complement (.nil state)) ⟨.byte 255, by rfl, rfl⟩
  have word : SourceExprEval interface heap calls frame
      (.unary .toWord (.unary .toByte (.unary .complement (.word 0)))) state ⟨.ok (.word 255), state⟩ :=
    .strict rfl (.cons byte (.nil state)) ⟨.word 255, by rfl, rfl⟩
  have compared : SourceExprEval interface heap calls frame
      (.binary (.compare .lt) (.unary .toWord (.unary .toByte (.unary .complement (.word 0)))) (.word 255))
      state ⟨.ok (.bool false), state⟩ := by
    apply (source_scalar_binary_exact (.compare .lt)
      (.unary .toWord (.unary .toByte (.unary .complement (.leaf (.word _))))) (.leaf (.word _))
      state clear _).mpr
    exact ⟨.word 255, .word 255, .bool false, word, word_source _ _ _ _ _ _, rfl, rfl⟩
  exact .strict rfl (.cons compared (.nil state)) ⟨.bool true, rfl, rfl⟩

theorem nested_cast_comparison_executes {SourceWorld TargetWorld : Type}
    {related : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated related source target)
    (clear : source.fault = none) (bounded : TemporaryNamesBound targetFrame 0)
    (scope : Scope) (result : NativeType) (root : List Instruction) :
    ∃ after,
      TargetRun interface targetHeap targetCalls result root castComparisonOutput.code targetFrame target
        ⟨.normal, after, target⟩ ∧
      TargetAtomEval interface after target castComparisonOutput.result (.bool true) := by
  exact (scalar_expression_value_iff sourceHeap sourceCalls targetHeap targetCalls frames states clear
    result root cast_comparison_scalar (cast_comparison_actual_emission interface scope) bounded
    (.bool true)).mp (cast_comparison_source _ _ _ _ _ clear)

def orderedSubtraction : Expr := .binary (.word .sub) (.word 1) (.word 2)

def orderedSubtractionOutput : NativeLowering.Expression :=
  ⟨[.temporary 1 .word (.word 1), .temporary 2 .word (.word 2),
    .temporary 3 .word (.binary (.word .sub) (.temporary 1 .word) (.temporary 2 .word))],
    .temporary 3 .word, ⟨3⟩⟩

theorem ordered_subtraction_scalar : SourceScalarExpression orderedSubtraction :=
  .binary .sub (.leaf (.word _)) (.leaf (.word _))

theorem ordered_subtraction_actual_emission (interface : Interface) (scope : Scope) :
    NativeLowering.expression? interface scope orderedSubtraction ⟨0⟩ = some orderedSubtractionOutput := by
  simp [orderedSubtraction, orderedSubtractionOutput, NativeLowering.expression?,
    NativeLowering.prependCode, NativeLowering.pureTemporary, NativeLowering.numericGuard,
    inferExpr, binaryType, NativeIR.fresh]
  exact ⟨rfl, rfl⟩

theorem ordered_subtraction_source_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (state : SourceState World) (clear : state.fault = none) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame orderedSubtraction state out ↔
      out = ⟨.ok (.word largestWord), state⟩ := by
  have computed : sourceBinaryOp (.word .sub) (.word 1) (.word 2) = some (.ok (.word largestWord)) :=
    by rfl
  unfold orderedSubtraction
  rw [source_scalar_binary_exact .sub (.leaf (.word _)) (.leaf (.word _)) state clear out]
  constructor
  · rintro ⟨left, right, value, leftRun, rightRun, actual, same⟩
    cases (word_source_exact interface heap calls frame 1 state _).mp leftRun
    cases (word_source_exact interface heap calls frame 2 state _).mp rightRun
    cases Option.some.inj (computed.symm.trans actual)
    exact same
  · intro same
    exact ⟨.word 1, .word 2, .word largestWord, word_source _ _ _ _ _ _,
      word_source _ _ _ _ _ _, computed, same⟩

theorem actual_subtraction_preserves_operand_order {SourceWorld TargetWorld : Type}
    {related : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated related source target)
    (clear : source.fault = none) (bounded : TemporaryNamesBound targetFrame 0)
    (scope : Scope) (result : NativeType) (root : List Instruction) :
    (∃ after,
      TargetRun interface targetHeap targetCalls result root orderedSubtractionOutput.code targetFrame target
        ⟨.normal, after, target⟩ ∧
      TargetAtomEval interface after target orderedSubtractionOutput.result (.word (NativeWord64.encode largestWord))) ∧
    ¬ (∃ after,
      TargetRun interface targetHeap targetCalls result root orderedSubtractionOutput.code targetFrame target
        ⟨.normal, after, target⟩ ∧
      TargetAtomEval interface after target orderedSubtractionOutput.result (.word 1)) := by
  constructor
  · exact (scalar_expression_value_iff sourceHeap sourceCalls targetHeap targetCalls frames states clear
      result root ordered_subtraction_scalar (ordered_subtraction_actual_emission interface scope) bounded
      (.word largestWord)).mp ((ordered_subtraction_source_exact _ _ _ _ _ clear _).mpr rfl)
  · intro ran
    have sourceRan := (scalar_expression_value_iff sourceHeap sourceCalls targetHeap targetCalls frames states clear
      result root ordered_subtraction_scalar (ordered_subtraction_actual_emission interface scope) bounded
      (.word 1)).mpr ran
    have same := (ordered_subtraction_source_exact interface sourceHeap sourceCalls sourceFrame source clear _).mp sourceRan
    have different : largestWord ≠ (1 : NativeWord64.Word) := by decide +kernel
    exact different (SourceValue.word.inj (Except.ok.inj (congrArg SourceOutcome.result same))).symm

theorem scalar_fragment_cannot_add_return_or_state_effect {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (frame : TargetFrame)
    (state : TargetState World) (bounded : TemporaryNamesBound frame 0) (scope : Scope)
    (result : NativeType) (root : List Instruction) {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls result root castComparisonOutput.code frame state out) :
    out.flow = .normal ∧ out.state = state ∧ TemporaryProtection 0 frame out.frame := by
  have shape := scalar_target_run_shape cast_comparison_scalar (cast_comparison_actual_emission interface scope)
    bounded ran
  exact ⟨shape.1, shape.2.1, shape.2.2.1⟩

end Mettapedia.GSLT.LanguageDef.NativeOps.ScalarExpressionControls
