import Mettapedia.GSLT.LanguageDef.NativeOpsScalarExpressionFacts

/-!
# Two-sided lowering of recursive scalar expressions

The source's bounded natural arithmetic and the target's bit-vector operations
are independent. Operand runs retain their order and private by-value results.
All memory, ownership, allocator counters and external state are preserved by
this pure fragment. Clear entry is explicit at its public expression boundary;
raw target-state preservation does not require clear entry.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Atom)
open NativeLowering (Expression)

theorem unchecked_scalar_source_result {operation : Binary}
    (unchecked : UncheckedScalarBinary operation) (left right : SourceValue)
    {result : Except NativeWord64.Fault SourceValue}
    (computed : sourceBinaryOp operation left right = some result) :
    ∃ value, result = .ok value := by
  cases unchecked with
  | add | sub | mul | band | bor | bxor =>
      cases left <;> cases right <;>
        simp only [sourceBinaryOp, NativeWord64.sourceBinary, Except.map] at computed
      all_goals cases computed
      all_goals exact ⟨_, rfl⟩
  | compare comparison =>
      cases comparison <;> cases left <;> cases right <;>
        simp only [sourceBinaryOp] at computed
      all_goals cases computed
      all_goals exact ⟨_, rfl⟩

theorem unchecked_scalar_value_result_iff {operation : Binary}
    (unchecked : UncheckedScalarBinary operation) (left right value : SourceValue) :
    targetUncheckedBinary operation (encodeValue left) (encodeValue right) = some (encodeValue value) ↔
      sourceBinaryOp operation left right = some (.ok value) := by
  rw [targetUncheckedBinary, binary_value_correspondence]
  cases selected : sourceBinaryOp operation left right with
  | none => simp only [Option.map_none, Option.bind_none, reduceCtorEq]
  | some result =>
      obtain ⟨actual, same⟩ := unchecked_scalar_source_result unchecked left right selected
      subst result
      simp only [Option.map_some, Except.map, Option.bind_some, Except.toOption]
      constructor
      · intro encoded
        cases encodeValue_injective (Option.some.inj encoded)
        rfl
      · intro same
        cases Option.some.inj same
        rfl

theorem scalar_binary_operands {operation : Binary}
    (unchecked : UncheckedScalarBinary operation) (left right : Expr) :
    sourceStrictOperands? (.binary operation left right) = some [left, right] := by
  cases unchecked <;> rfl

theorem source_scalar_arguments_shape {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (arguments : List Expr) (state : SourceState World)
    (pure : ∀ expression ∈ arguments, ∀ out,
      SourceExprEval interface heap calls frame expression state out →
        ∃ value, out = ⟨.ok value, state⟩)
    {out : SourceArgumentsOutcome World}
    (ran : SourceArgumentsEval interface heap calls frame arguments state out) :
    ∃ values, out = ⟨.ok values, state⟩ ∧
      List.Forall₂ (fun expression value =>
        SourceExprEval interface heap calls frame expression state ⟨.ok value, state⟩) arguments values := by
  induction arguments generalizing out with
  | nil =>
      cases ran
      exact ⟨[], rfl, .nil⟩
  | cons expression rest ih =>
      cases ran with
      | cons first remaining =>
          obtain ⟨value, same⟩ := pure expression (by simp) _ first
          cases same
          obtain ⟨values, same, witnesses⟩ :=
            ih (fun child member => pure child (by simp [member])) remaining
          cases same
          exact ⟨_, rfl, .cons first witnesses⟩
      | consFault first =>
          obtain ⟨value, impossible⟩ := pure expression (by simp) _ first
          cases impossible

theorem source_scalar_primitive_shape {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {expression : Expr} (scalar : SourceScalarExpression expression)
    (arguments : List SourceValue) (state : SourceState World) (clear : state.fault = none)
    {out : SourceOutcome World}
    (ran : sourcePrimitive interface heap calls frame expression arguments state out) :
    ∃ value, out = ⟨.ok value, state⟩ := by
  cases scalar with
  | leaf leaf =>
      cases arguments with
      | nil =>
          cases leaf with
          | word | byte | bool | nullReference => exact ⟨_, ran⟩
          | «variable» | zero => rcases ran with ⟨value, _, same⟩; exact ⟨value, same⟩
      | cons head tail => cases leaf <;> cases ran
  | unary operation child =>
      cases arguments with
      | nil => cases ran
      | cons first rest =>
          cases rest with
          | nil => rcases ran with ⟨value, _, same⟩; exact ⟨value, same⟩
          | cons second tail => cases ran
  | binary unchecked first second =>
      cases arguments with
      | nil => cases ran
      | cons left rest =>
          cases rest with
          | nil => cases ran
          | cons right tail =>
              cases tail with
              | nil =>
                  rcases ran with ⟨result, _, _, computed, same⟩
                  obtain ⟨value, resultSame⟩ := unchecked_scalar_source_result unchecked left right computed
                  subst result
                  exact ⟨value, by simpa only [sourceFinish, sourceObserve, clear] using same⟩
              | cons extra remaining => cases ran

theorem source_scalar_run_shape {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {expression : Expr} (scalar : SourceScalarExpression expression)
    (state : SourceState World) (clear : state.fault = none) {out : SourceOutcome World}
    (ran : SourceExprEval interface heap calls frame expression state out) :
    ∃ value, out = ⟨.ok value, state⟩ := by
  induction scalar generalizing out with
  | leaf leaf =>
      have primitive := (source_operand_free_expression_exact _ (source_leaf_has_no_operands leaf) _ _).mp ran
      exact source_scalar_primitive_shape (.leaf leaf) [] state clear primitive
  | unary operation child ih =>
      rename_i operand
      have operands : sourceStrictOperands? (.unary operation operand) = some [operand] := rfl
      rcases (source_strict_expression_exact _ _ operands _ _).mp ran with
        ⟨values, middle, evaluated, primitive⟩ | ⟨fault, after, evaluated, _⟩
      · have pure : ∀ expression ∈ [operand], ∀ out,
            SourceExprEval interface heap calls frame expression state out →
              ∃ value, out = ⟨.ok value, state⟩ := by
          intro expression member
          cases List.mem_singleton.mp member
          exact fun _ => ih
        obtain ⟨_, same, _⟩ := source_scalar_arguments_shape _ state pure evaluated
        cases same
        exact source_scalar_primitive_shape (.unary operation child) _ state clear primitive
      · have pure : ∀ expression ∈ [operand], ∀ out,
            SourceExprEval interface heap calls frame expression state out →
              ∃ value, out = ⟨.ok value, state⟩ := by
          intro expression member
          cases List.mem_singleton.mp member
          exact fun _ => ih
        obtain ⟨_, impossible, _⟩ := source_scalar_arguments_shape _ state pure evaluated
        cases impossible
  | binary unchecked first second firstIH secondIH =>
      rename_i operation left right
      have pure : ∀ expression ∈ [left, right], ∀ out,
          SourceExprEval interface heap calls frame expression state out →
            ∃ value, out = ⟨.ok value, state⟩ := by
        intro expression member
        rcases List.mem_cons.mp member with same | rest
        · subst expression; exact fun _ => firstIH
        · cases List.mem_singleton.mp rest; exact fun _ => secondIH
      rcases (source_strict_expression_exact _ _ (scalar_binary_operands unchecked _ _) _ _).mp ran with
        ⟨values, middle, evaluated, primitive⟩ | ⟨fault, after, evaluated, _⟩
      · obtain ⟨_, same, _⟩ := source_scalar_arguments_shape _ state pure evaluated
        cases same
        exact source_scalar_primitive_shape (.binary unchecked first second) _ state clear primitive
      · obtain ⟨_, impossible, _⟩ := source_scalar_arguments_shape _ state pure evaluated
        cases impossible

theorem source_scalar_unary_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (operation : Unary) {operand : Expr} (scalar : SourceScalarExpression operand)
    (state : SourceState World) (clear : state.fault = none) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame (.unary operation operand) state out ↔
      ∃ value result,
        SourceExprEval interface heap calls frame operand state ⟨.ok value, state⟩ ∧
        sourceUnaryOp operation value = some result ∧ out = ⟨.ok result, state⟩ := by
  constructor
  · intro ran
    rcases (source_strict_expression_exact _ _ rfl _ _).mp ran with
      ⟨values, middle, evaluated, primitive⟩ | ⟨fault, after, evaluated, _⟩
    · have pure : ∀ expression ∈ [operand], ∀ out,
          SourceExprEval interface heap calls frame expression state out →
            ∃ value, out = ⟨.ok value, state⟩ := by
        intro expression member
        cases List.mem_singleton.mp member
        exact fun _ => source_scalar_run_shape scalar state clear
      obtain ⟨actual, same, witnesses⟩ := source_scalar_arguments_shape _ state pure evaluated
      cases same
      cases witnesses with
      | cons first rest =>
          cases rest
          rcases primitive with ⟨result, computed, same⟩
          exact ⟨_, result, first, computed, same⟩
    · rcases (source_arguments_cons_fault_exact operand [] _ _ _).mp evaluated with
        first | ⟨value, middle, _, rest⟩
      · obtain ⟨_, impossible⟩ := source_scalar_run_shape scalar state clear first
        cases impossible
      · cases (source_arguments_nil_exact _ _).mp rest
  · rintro ⟨value, result, first, computed, same⟩
    subst out
    exact .strict rfl (.cons first (.nil state)) ⟨result, computed, rfl⟩

theorem source_scalar_binary_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {operation : Binary} (unchecked : UncheckedScalarBinary operation)
    {left right : Expr} (first : SourceScalarExpression left) (second : SourceScalarExpression right)
    (state : SourceState World) (clear : state.fault = none) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame (.binary operation left right) state out ↔
      ∃ leftValue rightValue result,
        SourceExprEval interface heap calls frame left state ⟨.ok leftValue, state⟩ ∧
        SourceExprEval interface heap calls frame right state ⟨.ok rightValue, state⟩ ∧
        sourceBinaryOp operation leftValue rightValue = some (.ok result) ∧ out = ⟨.ok result, state⟩ := by
  have pure : ∀ expression ∈ [left, right], ∀ out,
      SourceExprEval interface heap calls frame expression state out →
        ∃ value, out = ⟨.ok value, state⟩ := by
    intro expression member
    rcases List.mem_cons.mp member with same | rest
    · subst expression; exact fun _ => source_scalar_run_shape first state clear
    · cases List.mem_singleton.mp rest; exact fun _ => source_scalar_run_shape second state clear
  constructor
  · intro ran
    rcases (source_strict_expression_exact _ _ (scalar_binary_operands unchecked _ _) _ _).mp ran with
      ⟨values, middle, evaluated, primitive⟩ | ⟨fault, after, evaluated, _⟩
    · obtain ⟨actual, same, witnesses⟩ := source_scalar_arguments_shape _ state pure evaluated
      cases same
      cases witnesses with
      | cons firstRun rest =>
          cases rest with
          | cons secondRun rest =>
              cases rest
              rcases primitive with ⟨result, _, _, computed, same⟩
              obtain ⟨value, resultSame⟩ := unchecked_scalar_source_result unchecked _ _ computed
              subst result
              exact ⟨_, _, value, firstRun, secondRun, computed,
                by simpa only [sourceFinish, sourceObserve, clear] using same⟩
    · obtain ⟨_, impossible, _⟩ := source_scalar_arguments_shape _ state pure evaluated
      cases impossible
  · rintro ⟨leftValue, rightValue, result, firstRun, secondRun, computed, same⟩
    subst out
    refine .strict (scalar_binary_operands unchecked _ _) (.cons firstRun (.cons secondRun (.nil state))) ?_
    exact ⟨.ok result, unchecked_scalar_not_and unchecked, unchecked_scalar_not_or unchecked,
      computed, by simp only [sourceFinish, sourceObserve, clear]⟩

theorem scalar_target_split {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {scope : Scope} {expression : Expr} (scalar : SourceScalarExpression expression)
    {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output)
    (root suffix : List Instruction) {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World} (bounded : TemporaryNamesBound frame supply.next)
    (ran : TargetRun interface heap calls result root (output.code ++ suffix) frame state out) :
    ∃ middle,
      TargetRun interface heap calls result root output.code frame state ⟨.normal, middle, state⟩ ∧
      TargetRun interface heap calls result root suffix middle state out := by
  rcases target_split_jump_free_prefix root output.code suffix
    (expression_lowering_jump_free interface scope expression supply output compiled) ran with
    ⟨middle, post, initialRun, remaining⟩ | ⟨value, after, post, initialRun, same⟩
  · have unchanged := (scalar_target_run_shape scalar compiled bounded initialRun).2.1
    change post = state at unchanged
    subst post
    exact ⟨middle, initialRun, remaining⟩
  · have impossible := (scalar_target_run_shape scalar compiled bounded initialRun).1
    cases impossible

/-- Every source value has an actual run of the admitted emitted fragment. -/
theorem scalar_expression_value_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    (result : NativeType) (root : List Instruction) {scope : Scope} {expression : Expr}
    (scalar : SourceScalarExpression expression) :
    ∀ {supply : NativeIR.Supply} {output : Expression} {targetFrame : TargetFrame},
      NativeLowering.expression? interface scope expression supply = some output →
      FrameRelated sourceFrame targetFrame → TemporaryNamesBound targetFrame supply.next →
      ∀ {value : SourceValue},
      SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source ⟨.ok value, source⟩ →
      ∃ after,
        TargetRun interface targetHeap targetCalls result root output.code targetFrame target
          ⟨.normal, after, target⟩ ∧
        TargetAtomEval interface after target output.result (encodeValue value) ∧
        TemporaryProtection supply.next targetFrame after ∧ TemporaryNamesBound after output.supply.next := by
  induction scalar with
  | leaf leaf =>
      intro supply output targetFrame compiled frames bounded value sourceRan
      have unused := temporary_bound_fresh bounded (NativeIR.fresh_strict supply)
      let after := targetDeclareTemporary targetFrame (NativeIR.fresh supply).1 (encodeValue value)
      have ran := (actual_leaf_expression_run_exact sourceHeap sourceCalls targetHeap targetCalls
        frames states leaf scope supply output compiled unused result root _).mpr ⟨value, sourceRan, rfl⟩
      have shape := scalar_target_run_shape (.leaf leaf) compiled bounded ran
      obtain ⟨type, resultShape⟩ := actual_leaf_result_atom leaf scope supply output compiled
      refine ⟨after, ran, ?_, shape.2.2.1, shape.2.2.2⟩
      rw [resultShape]
      exact declared_temporary_atom _ _ _ _ _ _
  | unary operation child ih =>
      intro supply output targetFrame compiled frames bounded value sourceRan
      obtain ⟨operandValue, actual, operandRan, computed, same⟩ :=
        (source_scalar_unary_exact operation child source clear _).mp sourceRan
      cases same
      obtain ⟨type, operandOutput, _, operandCompiled, outputShape⟩ := scalar_unary_lowering_exact compiled
      subst output
      obtain ⟨middle, operandTarget, operandRead, _, middleBounded⟩ :=
        ih operandCompiled frames bounded operandRan
      let after := targetDeclareTemporary middle (NativeIR.fresh operandOutput.supply).1 (encodeValue value)
      have pure : TargetPureEval interface middle target (.unary operation operandOutput.result)
          (encodeValue value) :=
        .unary operandRead ((unary_value_result_iff operation operandValue value).mpr computed)
      have tail : TargetRun interface targetHeap targetCalls result root
          (NativeLowering.pureTemporary operandOutput.supply type (.unary operation operandOutput.result)).code
          middle target ⟨.normal, after, target⟩ :=
        .next (.temporary (temporary_bound_fresh middleBounded (NativeIR.fresh_strict _)) pure) (.nil _ _ _)
      have ran := target_append_normal root _ _
        (expression_lowering_jump_free interface scope _ supply operandOutput operandCompiled) operandTarget tail
      have shape := scalar_target_run_shape (.unary operation child) compiled bounded ran
      exact ⟨after, ran, declared_temporary_atom interface middle target
        (NativeIR.fresh operandOutput.supply).1 type (encodeValue value), shape.2.2.1, shape.2.2.2⟩
  | binary unchecked first second firstIH secondIH =>
      rename_i operation left right
      intro supply output targetFrame compiled frames bounded value sourceRan
      obtain ⟨leftValue, rightValue, actual, leftRan, rightRan, computed, same⟩ :=
        (source_scalar_binary_exact unchecked first second source clear _).mp sourceRan
      cases same
      obtain ⟨type, leftOutput, rightOutput, _, leftCompiled, rightCompiled, outputShape⟩ :=
        scalar_binary_lowering_exact unchecked compiled
      subst output
      obtain ⟨middle, leftTarget, leftRead, leftProtection, middleBounded⟩ :=
        firstIH leftCompiled frames bounded leftRan
      obtain ⟨last, rightTarget, rightRead, rightProtection, lastBounded⟩ :=
        secondIH rightCompiled (temporary_protection_preserves_source_frame frames leftProtection)
          middleBounded rightRan
      have leftReadAtLast := (protection_atom_evaluation rightProtection leftOutput.result
        (scalar_result_atom_within first leftCompiled) target target (encodeValue leftValue)).mp leftRead
      let after := targetDeclareTemporary last (NativeIR.fresh rightOutput.supply).1 (encodeValue value)
      have pure : TargetPureEval interface last target
          (.binary operation leftOutput.result rightOutput.result) (encodeValue value) :=
        .binary leftReadAtLast rightRead
          ((unchecked_scalar_value_result_iff unchecked leftValue rightValue value).mpr computed)
      have tail : TargetRun interface targetHeap targetCalls result root
          (NativeLowering.pureTemporary rightOutput.supply type
            (.binary operation leftOutput.result rightOutput.result)).code last target ⟨.normal, after, target⟩ :=
        .next (.temporary (temporary_bound_fresh lastBounded (NativeIR.fresh_strict _)) pure) (.nil _ _ _)
      have rightAndTail := target_append_normal root _ _
        (expression_lowering_jump_free interface scope _ _ rightOutput rightCompiled) rightTarget tail
      have both := target_append_normal root _ _
        (expression_lowering_jump_free interface scope _ _ leftOutput leftCompiled) leftTarget rightAndTail
      have ran : TargetRun interface targetHeap targetCalls result root
          (NativeLowering.prependCode (leftOutput.code ++ rightOutput.code)
            (NativeLowering.pureTemporary rightOutput.supply type
              (.binary operation leftOutput.result rightOutput.result))).code targetFrame target
          ⟨.normal, after, target⟩ := by
        simpa only [NativeLowering.prependCode, List.append_assoc] using both
      have shape := scalar_target_run_shape (.binary unchecked first second) compiled bounded ran
      exact ⟨after, ran, declared_temporary_atom interface last target
        (NativeIR.fresh rightOutput.supply).1 type (encodeValue value), shape.2.2.1, shape.2.2.2⟩

/-- Every actual target run determines a source-authorized value, without a success premise. -/
theorem scalar_expression_value_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    (result : NativeType) (root : List Instruction) {scope : Scope} {expression : Expr}
    (scalar : SourceScalarExpression expression) :
    ∀ {supply : NativeIR.Supply} {output : Expression} {targetFrame : TargetFrame},
      NativeLowering.expression? interface scope expression supply = some output →
      FrameRelated sourceFrame targetFrame → TemporaryNamesBound targetFrame supply.next →
      ∀ {out : TargetBlockOutcome TargetWorld},
      TargetRun interface targetHeap targetCalls result root output.code targetFrame target out →
      ∃ value,
        SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source ⟨.ok value, source⟩ ∧
        TargetAtomEval interface out.frame out.state output.result (encodeValue value) := by
  induction scalar with
  | leaf leaf =>
      intro supply output targetFrame compiled frames bounded out ran
      have unused := temporary_bound_fresh bounded (NativeIR.fresh_strict supply)
      obtain ⟨value, sourceRan, same⟩ := (actual_leaf_expression_run_exact sourceHeap sourceCalls
        targetHeap targetCalls frames states leaf scope supply output compiled unused result root out).mp ran
      subst out
      obtain ⟨type, resultShape⟩ := actual_leaf_result_atom leaf scope supply output compiled
      refine ⟨value, sourceRan, ?_⟩
      rw [resultShape]
      exact declared_temporary_atom _ _ _ _ _ _
  | unary operation child ih =>
      intro supply output targetFrame compiled frames bounded out ran
      obtain ⟨type, operandOutput, _, operandCompiled, outputShape⟩ := scalar_unary_lowering_exact compiled
      subst output
      obtain ⟨middle, initialRun, tail⟩ := scalar_target_split child operandCompiled root _ bounded ran
      have middleBounded := (scalar_target_run_shape child operandCompiled bounded initialRun).2.2.2
      obtain ⟨operandValue, operandSource, operandRead⟩ := ih operandCompiled frames bounded initialRun
      obtain ⟨actual, pure, same⟩ := (target_pure_temporary_any_exact interface targetHeap targetCalls
        result root middle target (NativeIR.fresh operandOutput.supply).1 type
        (.unary operation operandOutput.result)
        (temporary_bound_fresh middleBounded (NativeIR.fresh_strict _)) out).mp tail
      cases pure with
      | unary otherRead computed =>
          cases target_atom_unique operandRead otherRead
          let value := decodeValue actual
          have sourceComputed : sourceUnaryOp operation operandValue = some value := by
            apply (unary_value_result_iff operation operandValue value).mp
            simpa only [value, encode_decode_value] using computed
          subst out
          refine ⟨value,
            (source_scalar_unary_exact operation child source clear _).mpr
              ⟨operandValue, value, operandSource, sourceComputed, rfl⟩, ?_⟩
          simpa only [value, encode_decode_value, NativeLowering.prependCode, NativeLowering.pureTemporary] using
            declared_temporary_atom interface middle target (NativeIR.fresh operandOutput.supply).1 type actual
  | binary unchecked first second firstIH secondIH =>
      rename_i operation left right
      intro supply output targetFrame compiled frames bounded out ran
      obtain ⟨type, leftOutput, rightOutput, _, leftCompiled, rightCompiled, outputShape⟩ :=
        scalar_binary_lowering_exact unchecked compiled
      subst output
      have ordered : TargetRun interface targetHeap targetCalls result root
          (leftOutput.code ++ (rightOutput.code ++
            (NativeLowering.pureTemporary rightOutput.supply type
              (.binary operation leftOutput.result rightOutput.result)).code)) targetFrame target out := by
        simpa only [NativeLowering.prependCode, List.append_assoc] using ran
      obtain ⟨middle, leftTarget, rest⟩ := scalar_target_split first leftCompiled root _ bounded ordered
      have leftShape := scalar_target_run_shape first leftCompiled bounded leftTarget
      obtain ⟨last, rightTarget, tail⟩ := scalar_target_split second rightCompiled root _ leftShape.2.2.2 rest
      have rightShape := scalar_target_run_shape second rightCompiled leftShape.2.2.2 rightTarget
      obtain ⟨leftValue, leftSource, leftRead⟩ := firstIH leftCompiled frames bounded leftTarget
      obtain ⟨rightValue, rightSource, rightRead⟩ :=
        secondIH rightCompiled (temporary_protection_preserves_source_frame frames leftShape.2.2.1)
          leftShape.2.2.2 rightTarget
      have leftReadAtLast := (protection_atom_evaluation rightShape.2.2.1 leftOutput.result
        (scalar_result_atom_within first leftCompiled) target target (encodeValue leftValue)).mp leftRead
      obtain ⟨actual, pure, same⟩ := (target_pure_temporary_any_exact interface targetHeap targetCalls
        result root last target (NativeIR.fresh rightOutput.supply).1 type
        (.binary operation leftOutput.result rightOutput.result)
        (temporary_bound_fresh rightShape.2.2.2 (NativeIR.fresh_strict _)) out).mp tail
      cases pure with
      | binary otherLeft otherRight computed =>
          cases target_atom_unique leftReadAtLast otherLeft
          cases target_atom_unique rightRead otherRight
          let value := decodeValue actual
          have sourceComputed : sourceBinaryOp operation leftValue rightValue = some (.ok value) := by
            apply (unchecked_scalar_value_result_iff unchecked leftValue rightValue value).mp
            simpa only [value, encode_decode_value] using computed
          subst out
          refine ⟨value,
            (source_scalar_binary_exact unchecked first second source clear _).mpr
              ⟨leftValue, rightValue, value, leftSource, rightSource, sourceComputed, rfl⟩, ?_⟩
          simpa only [value, encode_decode_value, NativeLowering.prependCode, NativeLowering.pureTemporary] using
            declared_temporary_atom interface last target (NativeIR.fresh rightOutput.supply).1 type actual

/-- Value equality includes a real run, rather than only a projected result/frame. -/
theorem scalar_expression_value_iff {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    (result : NativeType) (root : List Instruction) {scope : Scope} {expression : Expr}
    (scalar : SourceScalarExpression expression) {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output)
    (bounded : TemporaryNamesBound targetFrame supply.next) (value : SourceValue) :
    SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source ⟨.ok value, source⟩ ↔
      ∃ after,
        TargetRun interface targetHeap targetCalls result root output.code targetFrame target
          ⟨.normal, after, target⟩ ∧
        TargetAtomEval interface after target output.result (encodeValue value) := by
  constructor
  · intro sourceRan
    obtain ⟨after, ran, read, _, _⟩ := scalar_expression_value_preservation sourceHeap sourceCalls
      targetHeap targetCalls states clear result root scalar compiled frames bounded sourceRan
    exact ⟨after, ran, read⟩
  · rintro ⟨after, ran, read⟩
    obtain ⟨actual, sourceRan, otherRead⟩ := scalar_expression_value_reflection sourceHeap sourceCalls
      targetHeap targetCalls states clear result root scalar compiled frames bounded ran
    cases encodeValue_injective (target_atom_unique otherRead read)
    exact sourceRan

theorem scalar_expression_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    (result : NativeType) (root : List Instruction) {scope : Scope} {expression : Expr}
    (scalar : SourceScalarExpression expression) {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output)
    (bounded : TemporaryNamesBound targetFrame supply.next) {sourceOut : SourceOutcome SourceWorld}
    (sourceRan : SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source sourceOut) :
    ∃ out observed,
      TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      targetExpressionObservation interface output.result out observed ∧
      out.flow = .normal ∧ out.state = target ∧ FrameRelated sourceFrame out.frame ∧
      TemporaryProtection supply.next targetFrame out.frame ∧ TemporaryNamesBound out.frame output.supply.next ∧
      OutcomeRelated worldRelated sourceOut observed := by
  obtain ⟨value, sourceShape⟩ := source_scalar_run_shape scalar source clear sourceRan
  subst sourceOut
  obtain ⟨after, ran, read, protection, afterBounded⟩ :=
    scalar_expression_value_preservation sourceHeap sourceCalls targetHeap targetCalls states clear
      result root scalar compiled frames bounded sourceRan
  refine ⟨⟨.normal, after, target⟩, targetObserve target (encodeValue value), ran,
    ⟨encodeValue value, read, rfl⟩, rfl, rfl,
    temporary_protection_preserves_source_frame frames protection, protection, afterBounded, ?_⟩
  simpa only [sourceObserve, clear] using observation_correspondence states value

theorem scalar_expression_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    (result : NativeType) (root : List Instruction) {scope : Scope} {expression : Expr}
    (scalar : SourceScalarExpression expression) {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output)
    (bounded : TemporaryNamesBound targetFrame supply.next)
    {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out)
    (observation : targetExpressionObservation interface output.result out observed) :
    ∃ sourceOut,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source sourceOut ∧
      out.flow = .normal ∧ out.state = target ∧ FrameRelated sourceFrame out.frame ∧
      TemporaryProtection supply.next targetFrame out.frame ∧ TemporaryNamesBound out.frame output.supply.next ∧
      OutcomeRelated worldRelated sourceOut observed := by
  obtain ⟨value, sourceRan, read⟩ := scalar_expression_value_reflection sourceHeap sourceCalls
    targetHeap targetCalls states clear result root scalar compiled frames bounded ran
  rcases scalar_target_run_shape scalar compiled bounded ran with ⟨normal, unchanged, protection, afterBounded⟩
  have observedValue : observed = targetObserve target (encodeValue value) := by
    unfold targetExpressionObservation at observation
    rw [normal] at observation
    obtain ⟨actual, actualRead, same⟩ := observation
    cases target_atom_unique read actualRead
    simpa only [unchanged] using same
  subst observed
  refine ⟨⟨.ok value, source⟩, sourceRan, normal, unchanged,
    temporary_protection_preserves_source_frame frames protection, protection, afterBounded, ?_⟩
  simpa only [sourceObserve, clear] using observation_correspondence states value

end Mettapedia.GSLT.LanguageDef.NativeOps
