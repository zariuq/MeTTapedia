import Mettapedia.GSLT.LanguageDef.NativeOpsShortCircuitCorrespondence

/-!
# Strict binary composition over proved children

Operands may include independently justified reads. Their established state,
type and frame laws are composed in the actual left-to-right evaluation order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Atom Instruction)
open NativeLowering (Expression)

variable {SourceWorld TargetWorld : Type}
  {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
  {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
  {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
  {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
  {result : NativeType} {default : TargetValue} {operation : Binary} {left right : Expr}

theorem strict_binary_children_source_exact (scalar : GuardedScalarBinary operation)
    (first : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default left)
    (second : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default right) (out : SourceOutcome SourceWorld) :
    SourceExprEval interface sourceHeap sourceCalls sourceFrame (.binary operation left right) source out ↔
      (∃ firstValue secondValue computed,
        SourceExprEval interface sourceHeap sourceCalls sourceFrame left source ⟨.ok firstValue, source⟩ ∧
        SourceExprEval interface sourceHeap sourceCalls sourceFrame right source ⟨.ok secondValue, source⟩ ∧
        sourceBinaryOp operation firstValue secondValue = some computed ∧
        out = sourceFinish source computed) ∨
      (∃ fault, SourceExprEval interface sourceHeap sourceCalls sourceFrame left source
        ⟨.error fault, sourcePoison source fault⟩ ∧ out = ⟨.error fault, sourcePoison source fault⟩) ∨
      (∃ firstValue fault,
        SourceExprEval interface sourceHeap sourceCalls sourceFrame left source ⟨.ok firstValue, source⟩ ∧
        SourceExprEval interface sourceHeap sourceCalls sourceFrame right source ⟨.error fault, sourcePoison source fault⟩ ∧
        out = ⟨.error fault, sourcePoison source fault⟩) := by
  rw [source_strict_expression_exact _ _ (guarded_scalar_operands scalar _ _)]
  constructor
  · rintro (⟨values, middle, evaluated, primitive⟩ | ⟨fault, after, evaluated, same⟩)
    · cases values with
      | nil => cases primitive
      | cons firstValue rest =>
          cases rest with
          | nil => cases primitive
          | cons secondValue rest =>
              cases rest with
              | nil =>
                  obtain ⟨between, leftRan, tail⟩ :=
                    (source_arguments_cons_success_exact left [right] source middle firstValue [secondValue]).mp evaluated
                  have leftUnchanged : between = source := first.sourceState leftRan
                  subst between
                  obtain ⟨last, rightRan, ending⟩ :=
                    (source_arguments_cons_success_exact right [] source middle secondValue []).mp tail
                  cases (source_arguments_nil_exact last _).mp ending
                  have rightUnchanged : middle = source := second.sourceState rightRan
                  subst middle
                  obtain ⟨computed, _, _, computedSame, same⟩ := primitive
                  exact .inl ⟨firstValue, secondValue, computed, leftRan, rightRan, computedSame, same⟩
              | cons extra rest => cases primitive
    · rcases (source_arguments_cons_fault_exact left [right] source after fault).mp evaluated with
        failed | ⟨firstValue, middle, leftRan, tail⟩
      · have exactState : after = sourcePoison source fault := first.sourceState failed
        subst after
        exact .inr (.inl ⟨fault, failed, same⟩)
      · have leftUnchanged : middle = source := first.sourceState leftRan
        subst middle
        rcases (source_arguments_cons_fault_exact right [] source after fault).mp tail with
          failed | ⟨secondValue, last, _, ending⟩
        · have exactState : after = sourcePoison source fault := second.sourceState failed
          subst after
          exact .inr (.inr ⟨firstValue, fault, leftRan, failed, same⟩)
        · cases (source_arguments_nil_exact last _).mp ending
  · rintro (⟨firstValue, secondValue, computed, leftRan, rightRan, computedSame, same⟩ |
      ⟨fault, failed, same⟩ | ⟨firstValue, fault, leftRan, failed, same⟩)
    · exact .inl ⟨[firstValue, secondValue], source, .cons leftRan (.cons rightRan (.nil source)),
        computed, guarded_scalar_not_and scalar, guarded_scalar_not_or scalar, computedSame, same⟩
    · exact .inr ⟨fault, sourcePoison source fault, .consFault failed, same⟩
    · exact .inr ⟨fault, sourcePoison source fault, .cons leftRan (.consFault failed), same⟩


theorem strict_binary_children_source_state (scalar : GuardedScalarBinary operation)
    (first : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default left)
    (second : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default right) (clear : source.fault = none)
    {out : SourceOutcome SourceWorld}
    (ran : SourceExprEval interface sourceHeap sourceCalls sourceFrame (.binary operation left right) source out) :
    SourceScalarResultState source out.result out.state := by
  rcases (strict_binary_children_source_exact scalar first second out).mp ran with
    ⟨firstValue, secondValue, computed, _, _, _, same⟩ | ⟨fault, _, same⟩ | ⟨firstValue, fault, _, _, same⟩
  · subst out
    exact source_finish_scalar_state source clear computed
  · subst out; rfl
  · subst out; rfl

theorem strict_binary_children_source_tag (scalar : GuardedScalarBinary operation)
    (first : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default left)
    (second : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default right) (clear : source.fault = none)
    {type : NativeType} {value : SourceValue}
    (typing : inferExpr interface (sourceFrameScope sourceFrame) (.binary operation left right) = some type)
    (ran : SourceExprEval interface sourceHeap sourceCalls sourceFrame (.binary operation left right) source
      ⟨.ok value, source⟩) : SourceOuterTag type value := by
  rcases (strict_binary_children_source_exact scalar first second _).mp ran with
    ⟨leftValue, rightValue, computed, leftRan, rightRan, executed, same⟩ |
    ⟨fault, _, impossible⟩ | ⟨leftValue, fault, _, _, impossible⟩
  · obtain ⟨input, leftTyping, rightTyping, operationTyping⟩ := guarded_binary_inferred typing
    obtain ⟨answer, resultSame, answerTag⟩ := source_binary_typed_defined operationTyping
      (first.sourceTag leftTyping leftRan) (second.sourceTag rightTyping rightRan)
    cases Option.some.inj (resultSame.symm.trans executed)
    cases computed with
    | ok actual =>
        have exactValue : actual = value := by
          simpa only [sourceFinish, sourceObserve, clear, SourceOutcome.mk.injEq,
            Except.ok.injEq, and_true] using same.symm
        cases exactValue
        exact answerTag value rfl
    | error fault =>
        simp only [sourceFinish, sourceObserve, sourcePoison, clear, SourceOutcome.mk.injEq,
          reduceCtorEq, false_and] at same
  · cases impossible
  · cases impossible

theorem strict_binary_children_bounds (scalar : GuardedScalarBinary operation)
    (first : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default left)
    (second : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default right) {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.binary operation left right)
      supply = some output) :
    supply.next < output.supply.next ∧ atomWithin output.supply.next output.result := by
  obtain ⟨type, leftOutput, rightOutput, _, leftCompiled, rightCompiled, same⟩ :=
    guarded_binary_lowering_exact scalar compiled
  subst output
  exact ⟨((first.bounds leftCompiled).1.trans (second.bounds rightCompiled).1).trans
    (NativeIR.fresh_strict rightOutput.supply), Nat.le_refl _⟩

theorem strict_binary_tail_fresh (operation : Binary) (left right : Atom) (type : NativeType)
    (supply : NativeIR.Supply) :
    FreshGuardedCode supply.next (NativeIR.fresh supply).2.next
      (NativeLowering.numericGuard operation right ++
        (NativeLowering.pureTemporary supply type (.binary operation left right)).code) := by
  apply fresh_guarded_code_append (numeric_guard_has_no_temporary operation right _ _)
  intro instruction member
  cases List.mem_singleton.mp member
  exact .inl ⟨_, _, _, rfl, NativeIR.fresh_strict supply, Nat.le_refl _⟩

theorem source_guarded_binary_stateful_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {operation : Binary} (scalar : GuardedScalarBinary operation) (left right : Expr)
    (before : SourceState World) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame (.binary operation left right) before out ↔
      (∃ first second middle computed,
        SourceArgumentsEval interface heap calls frame [left, right] before ⟨.ok [first, second], middle⟩ ∧
        sourceBinaryOp operation first second = some computed ∧ out = sourceFinish middle computed) ∨
      (∃ fault after,
        SourceArgumentsEval interface heap calls frame [left, right] before ⟨.error fault, after⟩ ∧
        out = ⟨.error fault, after⟩) := by
  rw [source_strict_expression_exact _ _ (guarded_scalar_operands scalar _ _)]
  constructor
  · rintro (⟨values, middle, arguments, primitive⟩ | ⟨fault, after, arguments, same⟩)
    · cases values with
      | nil => cases primitive
      | cons first rest =>
          cases rest with
          | nil => cases primitive
          | cons second tail =>
              cases tail with
              | nil =>
                  obtain ⟨computed, _, _, executed, same⟩ := primitive
                  exact .inl ⟨first, second, middle, computed, arguments, executed, same⟩
              | cons extra rest => cases primitive
    · exact .inr ⟨fault, after, arguments, same⟩
  · rintro (⟨first, second, middle, computed, arguments, executed, same⟩ | ⟨fault, after, arguments, same⟩)
    · exact .inl ⟨[first, second], middle, arguments, computed,
        guarded_scalar_not_and scalar, guarded_scalar_not_or scalar, executed, same⟩
    · exact .inr ⟨fault, after, arguments, same⟩

theorem source_two_arguments_success_tags {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {left right : Expr} {before after : SourceState World} {first second : SourceValue} {type : NativeType}
    (tagged : ∀ expression ∈ [left, right], ∀ initial post value input,
      inferExpr interface (sourceFrameScope frame) expression = some input →
      SourceExprEval interface heap calls frame expression initial ⟨.ok value, post⟩ →
      SourceOuterTag input value)
    (firstTyping : inferExpr interface (sourceFrameScope frame) left = some type)
    (secondTyping : inferExpr interface (sourceFrameScope frame) right = some type)
    (arguments : SourceArgumentsEval interface heap calls frame [left, right] before
      ⟨.ok [first, second], after⟩) : SourceOuterTag type first ∧ SourceOuterTag type second := by
  obtain ⟨middle, leftRan, tail⟩ :=
    (source_arguments_cons_success_exact left [right] before after first [second]).mp arguments
  obtain ⟨last, rightRan, ending⟩ :=
    (source_arguments_cons_success_exact right [] middle after second []).mp tail
  cases (source_arguments_nil_exact last _).mp ending
  exact ⟨tagged left (by simp) before middle first type firstTyping leftRan,
    tagged right (by simp) middle after second type secondTyping rightRan⟩


theorem source_guarded_binary_stateful_success_tag {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {operation : Binary} (scalar : GuardedScalarBinary operation) {left right : Expr}
    {before after : SourceState World} {value : SourceValue} {type : NativeType}
    (typed : inferExpr interface (sourceFrameScope frame) (.binary operation left right) = some type)
    (tagged : ∀ expression ∈ [left, right], ∀ initial post raw input,
      inferExpr interface (sourceFrameScope frame) expression = some input →
      SourceExprEval interface heap calls frame expression initial ⟨.ok raw, post⟩ →
      SourceOuterTag input raw)
    (ran : SourceExprEval interface heap calls frame (.binary operation left right) before ⟨.ok value, after⟩) :
    SourceOuterTag type value := by
  obtain ⟨input, firstTyping, secondTyping, operationTyping⟩ := guarded_binary_inferred typed
  rcases (source_guarded_binary_stateful_exact scalar left right before _).mp ran with
    ⟨first, second, middle, computed, arguments, executed, same⟩ | ⟨fault, post, _, same⟩
  · obtain ⟨firstTag, secondTag⟩ := source_two_arguments_success_tags tagged firstTyping secondTyping arguments
    obtain ⟨actual, defined, resultTag⟩ := source_binary_typed_defined operationTyping firstTag secondTag
    have equality : actual = computed := Option.some.inj (defined.symm.trans executed)
    subst actual
    have result := congrArg SourceOutcome.result same
    cases computed with
    | ok raw =>
        cases current : middle.fault with
        | none =>
            simp only [sourceFinish, sourceObserve, current, Except.ok.injEq] at result
            cases result
            exact resultTag _ rfl
        | some fault => simp only [sourceFinish, sourceObserve, current, reduceCtorEq] at result
    | error fault =>
        cases current : middle.fault <;>
          simp only [sourceFinish, sourcePoison, sourceObserve, current, reduceCtorEq] at result
  · cases same

end Mettapedia.GSLT.LanguageDef.NativeOps
