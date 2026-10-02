import Mettapedia.GSLT.LanguageDef.NativeOpsGuardedExpressionFacts

/-!
# Exact outcomes of recursive guarded scalar lowering

The source relation evaluates bounded natural values. The target relation
executes the actual emitted instruction lists. Numeric refusals retain their
early return and sticky context fault, with complete memory and caller state.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Atom Instruction)
open NativeLowering (Expression)
open NativeWord64 (Fault)

def SourceScalarResultState {World α : Type} (before : SourceState World)
    (result : Except Fault α) (after : SourceState World) : Prop :=
  match result with
  | .ok _ => after = before
  | .error fault => after = sourcePoison before fault

theorem source_finish_scalar_state {World : Type} (state : SourceState World)
    (clear : state.fault = none) (computed : Except Fault SourceValue) :
    SourceScalarResultState state (sourceFinish state computed).result
      (sourceFinish state computed).state := by
  cases computed <;> simp only [sourceFinish, sourceObserve, sourcePoison, clear,
    SourceScalarResultState]

theorem source_guarded_primitive_state {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {expression : Expr} (guarded : SourceGuardedExpression expression)
    (arguments : List SourceValue) (state : SourceState World) (clear : state.fault = none)
    {out : SourceOutcome World}
    (ran : sourcePrimitive interface heap calls frame expression arguments state out) :
    SourceScalarResultState state out.result out.state := by
  cases guarded with
  | leaf leaf =>
      obtain ⟨value, same⟩ := source_scalar_primitive_shape (.leaf leaf) arguments state clear ran
      cases same
      rfl
  | unary operation child =>
      cases arguments with
      | nil => cases ran
      | cons value rest =>
          cases rest with
          | nil =>
              obtain ⟨computed, _, same⟩ := ran
              cases same
              rfl
          | cons extra rest => cases ran
  | binary scalar first second =>
      cases arguments with
      | nil => cases ran
      | cons left rest =>
          cases rest with
          | nil => cases ran
          | cons right rest =>
              cases rest with
              | nil =>
                  obtain ⟨computed, _, _, _, same⟩ := ran
                  cases same
                  exact source_finish_scalar_state state clear computed
              | cons extra rest => cases ran

theorem source_arguments_scalar_state {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (arguments : List Expr) (state : SourceState World)
    (every : ∀ expression ∈ arguments, ∀ out,
      SourceExprEval interface heap calls frame expression state out →
      SourceScalarResultState state out.result out.state)
    {out : SourceArgumentsOutcome World}
    (ran : SourceArgumentsEval interface heap calls frame arguments state out) :
    SourceScalarResultState state out.result out.state := by
  induction arguments generalizing out with
  | nil => cases ran; rfl
  | cons expression rest ih =>
      cases ran with
      | cons first remaining =>
          rename_i value middle remainingOut
          have unchanged := every expression (List.mem_cons.mpr (.inl rfl)) _ first
          change _ = state at unchanged
          cases unchanged
          have tail := ih (fun child member => every child (List.mem_cons.mpr (.inr member))) remaining
          cases result : remainingOut.result <;>
            simpa only [SourceScalarResultState, result, Except.map] using tail
      | consFault first =>
          exact every expression (List.mem_cons.mpr (.inl rfl)) _ first

theorem source_guarded_run_state {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {expression : Expr} (guarded : SourceGuardedExpression expression)
    (state : SourceState World) (clear : state.fault = none) {out : SourceOutcome World}
    (ran : SourceExprEval interface heap calls frame expression state out) :
    SourceScalarResultState state out.result out.state := by
  induction guarded generalizing out with
  | leaf leaf =>
      obtain ⟨value, same⟩ := source_scalar_run_shape (.leaf leaf) state clear ran
      cases same
      rfl
  | unary operation child ih =>
      rename_i operand
      have every : ∀ expression ∈ [operand], ∀ out,
          SourceExprEval interface heap calls frame expression state out →
          SourceScalarResultState state out.result out.state := by
        intro expression member
        cases List.mem_singleton.mp member
        exact fun _ => ih
      rcases (source_strict_expression_exact _ _ (rfl :
        sourceStrictOperands? (.unary operation operand) = some [operand]) state out).mp ran with
        ⟨values, middle, evaluated, primitive⟩ | ⟨fault, after, evaluated, same⟩
      · have unchanged := source_arguments_scalar_state _ state every evaluated
        change middle = state at unchanged
        subst middle
        exact source_guarded_primitive_state (.unary operation child) _ state clear primitive
      · cases same
        exact source_arguments_scalar_state _ state every evaluated
  | binary scalar first second firstIH secondIH =>
      rename_i operation left right
      have every : ∀ expression ∈ [left, right], ∀ out,
          SourceExprEval interface heap calls frame expression state out →
          SourceScalarResultState state out.result out.state := by
        intro expression member
        rcases List.mem_cons.mp member with same | last
        · subst expression; exact fun _ => firstIH
        · cases List.mem_singleton.mp last; exact fun _ => secondIH
      rcases (source_strict_expression_exact _ _ (guarded_scalar_operands scalar _ _) state out).mp ran with
        ⟨values, middle, evaluated, primitive⟩ | ⟨fault, after, evaluated, same⟩
      · have unchanged := source_arguments_scalar_state _ state every evaluated
        change middle = state at unchanged
        subst middle
        exact source_guarded_primitive_state (.binary scalar first second) _ state clear primitive
      · cases same
        exact source_arguments_scalar_state _ state every evaluated

theorem source_guarded_success_state {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {expression : Expr} (guarded : SourceGuardedExpression expression)
    (state : SourceState World) (clear : state.fault = none) {value : SourceValue} {after : SourceState World}
    (ran : SourceExprEval interface heap calls frame expression state ⟨.ok value, after⟩) :
    after = state := source_guarded_run_state guarded state clear ran

theorem source_guarded_fault_state {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {expression : Expr} (guarded : SourceGuardedExpression expression)
    (state : SourceState World) (clear : state.fault = none) {fault : Fault} {after : SourceState World}
    (ran : SourceExprEval interface heap calls frame expression state ⟨.error fault, after⟩) :
    after = sourcePoison state fault := source_guarded_run_state guarded state clear ran

theorem source_leaf_success_tag {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {expression : Expr} (leaf : SourceLeaf expression) (state : SourceState World)
    (tagged : SourceLocalsTagged frame state.memory) {type : NativeType} {value : SourceValue}
    (typing : inferExpr interface (sourceFrameScope frame) expression = some type)
    (ran : SourceExprEval interface heap calls frame expression state ⟨.ok value, state⟩) :
    SourceOuterTag type value := by
  have primitive := (source_operand_free_expression_exact _ (source_leaf_has_no_operands leaf) state _).mp ran
  cases leaf with
  | word number =>
      have same : NativeType.word = type := by simpa only [inferExpr, Option.some.injEq] using typing
      cases same
      cases primitive
      exact .word number
  | byte number =>
      have same : NativeType.byte = type := by simpa only [inferExpr, Option.some.injEq] using typing
      cases same
      cases primitive
      exact .byte number
  | bool boolean =>
      have same : NativeType.bool = type := by simpa only [inferExpr, Option.some.injEq] using typing
      cases same
      cases primitive
      exact .bool boolean
  | «variable» name =>
      obtain ⟨actual, read, same⟩ := primitive
      cases same
      exact source_local_read_tag tagged (by simpa only [inferExpr] using typing) read
  | zero zeroType =>
      obtain ⟨actual, zero, same⟩ := primitive
      cases same
      rw [inferExpr] at typing
      split at typing
      · cases Option.some.inj typing
        exact source_zero_outer_tag zero
      · cases typing
  | nullReference element =>
      cases primitive
      rw [inferExpr] at typing
      split at typing
      · cases Option.some.inj typing
        exact .reference element none
      · cases typing

theorem source_guarded_unary_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (operation : Unary) {operand : Expr} (guarded : SourceGuardedExpression operand)
    (state : SourceState World) (clear : state.fault = none) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame (.unary operation operand) state out ↔
      (∃ first value, SourceExprEval interface heap calls frame operand state ⟨.ok first, state⟩ ∧
        sourceUnaryOp operation first = some value ∧ out = ⟨.ok value, state⟩) ∨
      (∃ fault, SourceExprEval interface heap calls frame operand state
        ⟨.error fault, sourcePoison state fault⟩ ∧ out = ⟨.error fault, sourcePoison state fault⟩) := by
  rw [source_strict_expression_exact _ _ (rfl :
    sourceStrictOperands? (.unary operation operand) = some [operand])]
  constructor
  · rintro (⟨values, middle, evaluated, primitive⟩ | ⟨fault, after, evaluated, same⟩)
    · cases values with
      | nil => cases primitive
      | cons first rest =>
          cases rest with
          | nil =>
              obtain ⟨between, child, remaining⟩ :=
                (source_arguments_cons_success_exact operand [] state middle first []).mp evaluated
              cases (source_arguments_nil_exact between _).mp remaining
              have unchanged := source_guarded_success_state guarded state clear child
              subst middle
              obtain ⟨value, computed, same⟩ := primitive
              exact .inl ⟨first, value, child, computed, same⟩
          | cons extra rest => cases primitive
    · rcases (source_arguments_cons_fault_exact operand [] state after fault).mp evaluated with
        failed | ⟨value, middle, _, remaining⟩
      · have exactState := source_guarded_fault_state guarded state clear failed
        subst after
        exact .inr ⟨fault, failed, same⟩
      · cases (source_arguments_nil_exact middle _).mp remaining
  · rintro (⟨first, value, child, computed, same⟩ | ⟨fault, failed, same⟩)
    · exact .inl ⟨[first], state, .cons child (.nil state), value, computed, same⟩
    · exact .inr ⟨fault, sourcePoison state fault, .consFault failed, same⟩

theorem source_guarded_binary_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {operation : Binary} (scalar : GuardedScalarBinary operation) {left right : Expr}
    (first : SourceGuardedExpression left) (second : SourceGuardedExpression right)
    (state : SourceState World) (clear : state.fault = none) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame (.binary operation left right) state out ↔
      (∃ firstValue secondValue computed,
        SourceExprEval interface heap calls frame left state ⟨.ok firstValue, state⟩ ∧
        SourceExprEval interface heap calls frame right state ⟨.ok secondValue, state⟩ ∧
        sourceBinaryOp operation firstValue secondValue = some computed ∧
        out = sourceFinish state computed) ∨
      (∃ fault, SourceExprEval interface heap calls frame left state
        ⟨.error fault, sourcePoison state fault⟩ ∧ out = ⟨.error fault, sourcePoison state fault⟩) ∨
      (∃ firstValue fault,
        SourceExprEval interface heap calls frame left state ⟨.ok firstValue, state⟩ ∧
        SourceExprEval interface heap calls frame right state ⟨.error fault, sourcePoison state fault⟩ ∧
        out = ⟨.error fault, sourcePoison state fault⟩) := by
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
                    (source_arguments_cons_success_exact left [right] state middle firstValue [secondValue]).mp evaluated
                  have leftUnchanged := source_guarded_success_state first state clear leftRan
                  subst between
                  obtain ⟨last, rightRan, ending⟩ :=
                    (source_arguments_cons_success_exact right [] state middle secondValue []).mp tail
                  cases (source_arguments_nil_exact last _).mp ending
                  have rightUnchanged := source_guarded_success_state second state clear rightRan
                  subst middle
                  obtain ⟨computed, _, _, computedSame, same⟩ := primitive
                  exact .inl ⟨firstValue, secondValue, computed, leftRan, rightRan, computedSame, same⟩
              | cons extra rest => cases primitive
    · rcases (source_arguments_cons_fault_exact left [right] state after fault).mp evaluated with
        failed | ⟨firstValue, middle, leftRan, tail⟩
      · have exactState := source_guarded_fault_state first state clear failed
        subst after
        exact .inr (.inl ⟨fault, failed, same⟩)
      · have leftUnchanged := source_guarded_success_state first state clear leftRan
        subst middle
        rcases (source_arguments_cons_fault_exact right [] state after fault).mp tail with
          failed | ⟨secondValue, last, _, ending⟩
        · have exactState := source_guarded_fault_state second state clear failed
          subst after
          exact .inr (.inr ⟨firstValue, fault, leftRan, failed, same⟩)
        · cases (source_arguments_nil_exact last _).mp ending
  · rintro (⟨firstValue, secondValue, computed, leftRan, rightRan, computedSame, same⟩ |
      ⟨fault, failed, same⟩ | ⟨firstValue, fault, leftRan, failed, same⟩)
    · exact .inl ⟨[firstValue, secondValue], state, .cons leftRan (.cons rightRan (.nil state)),
        computed, guarded_scalar_not_and scalar, guarded_scalar_not_or scalar, computedSame, same⟩
    · exact .inr ⟨fault, sourcePoison state fault, .consFault failed, same⟩
    · exact .inr ⟨fault, sourcePoison state fault, .cons leftRan (.consFault failed), same⟩

theorem source_guarded_success_tag {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {expression : Expr} (guarded : SourceGuardedExpression expression)
    (state : SourceState World) (clear : state.fault = none)
    (tagged : SourceLocalsTagged frame state.memory) {type : NativeType} {value : SourceValue}
    (typing : inferExpr interface (sourceFrameScope frame) expression = some type)
    (ran : SourceExprEval interface heap calls frame expression state ⟨.ok value, state⟩) :
    SourceOuterTag type value := by
  induction guarded generalizing type value with
  | leaf leaf => exact source_leaf_success_tag leaf state tagged typing ran
  | unary operation child ih =>
      rcases (source_guarded_unary_exact operation child state clear _).mp ran with
        ⟨first, actual, evaluated, computed, same⟩ | ⟨fault, _, impossible⟩
      · cases same
        obtain ⟨input, inferred, operandTyping⟩ := guarded_unary_inferred typing
        obtain ⟨answer, executed, answerTag⟩ := source_unary_typed_defined operandTyping (ih inferred evaluated)
        cases Option.some.inj (executed.symm.trans computed)
        exact answerTag
      · cases impossible
  | binary scalar first second firstIH secondIH =>
      rcases (source_guarded_binary_exact scalar first second state clear _).mp ran with
        ⟨leftValue, rightValue, computed, leftRan, rightRan, executed, same⟩ |
        ⟨fault, _, impossible⟩ | ⟨leftValue, fault, _, _, impossible⟩
      · obtain ⟨input, leftTyping, rightTyping, operationTyping⟩ := guarded_binary_inferred typing
        obtain ⟨answer, resultSame, answerTag⟩ := source_binary_typed_defined operationTyping
          (firstIH leftTyping leftRan) (secondIH rightTyping rightRan)
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

/-- Raw target paths preserve all runtime state except the first numeric fault. -/
def GuardedTargetState {World : Type} (default : TargetValue) (before : TargetState World)
    (out : TargetBlockOutcome World) : Prop :=
  (out.flow = .normal ∧ out.state = before) ∨
    (∃ fault, out.flow = .returned default ∧ out.state = targetPoison before fault)

theorem fresh_guarded_run_shape {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {default : TargetValue} (zero : TargetZero interface result default)
    {root code : List Instruction} {lower upper : Nat} (fresh : FreshGuardedCode lower upper code)
    {frame : TargetFrame} {state : TargetState World} {out : TargetBlockOutcome World}
    (bounded : TemporaryNamesBound frame upper)
    (ran : TargetRun interface heap calls result root code frame state out) :
    GuardedTargetState default state out ∧
      TemporaryProtection lower frame out.frame ∧ TemporaryNamesBound out.frame upper := by
  induction code generalizing frame state with
  | nil =>
      cases ran
      exact ⟨.inl ⟨rfl, rfl⟩, temporary_protection_refl lower frame, bounded⟩
  | cons instruction rest ih =>
      have tailFresh : FreshGuardedCode lower upper rest :=
        fun item member => fresh item (List.mem_cons.mpr (.inr member))
      rcases fresh instruction (List.mem_cons.mpr (.inl rfl)) with
        ⟨identity, type, operation, same, above, within⟩ | ⟨operation, right, same⟩
      · subst instruction
        cases ran with
        | next first tail =>
            cases first with
            | temporary unused computed =>
                rename_i value
                have nextBounded := declared_temporary_bound bounded (Nat.le_refl _) within value
                obtain ⟨shape, protection, finalBounded⟩ := ih tailFresh nextBounded tail
                exact ⟨shape, temporary_protection_trans
                  (declare_temporary_protects frame _ above) protection, finalBounded⟩
        | «return» first | resume first _ _ | escape first _ => cases first
      · subst instruction
        cases ran with
        | next first tail =>
            cases first with
            | numericClear read clear => exact ih tailFresh bounded tail
        | «return» first =>
            cases first with
            | numericFault read failed otherZero =>
                cases target_zero_unique zero otherZero
                exact ⟨.inr ⟨_, rfl, rfl⟩, temporary_protection_refl lower frame, bounded⟩
        | resume first _ _ | escape first _ => cases first

theorem guarded_target_run_shape {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {default : TargetValue} (zero : TargetZero interface result default)
    {root : List Instruction} {scope : Scope} {expression : Expr}
    (guarded : SourceGuardedExpression expression) {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output)
    {frame : TargetFrame} {state : TargetState World} {out : TargetBlockOutcome World}
    (bounded : TemporaryNamesBound frame supply.next)
    (ran : TargetRun interface heap calls result root output.code frame state out) :
    GuardedTargetState default state out ∧ TemporaryProtection supply.next frame out.frame ∧
      TemporaryNamesBound out.frame output.supply.next := by
  obtain ⟨advanced, fresh, _⟩ := guarded_lowering_bounds guarded compiled
  exact fresh_guarded_run_shape zero fresh
    (guarded_temporary_bound_mono bounded (Nat.le_of_lt advanced)) ran

/-- The suffix tests the actual right operand and then computes the admitted operation. -/
theorem guarded_binary_fragment_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {result input type : NativeType} {default : TargetValue} (zero : TargetZero interface result default)
    {operation : Binary} (scalar : GuardedScalarBinary operation)
    {first second : SourceValue} (typing : binaryType operation input = some type)
    (firstTag : SourceOuterTag input first) (secondTag : SourceOuterTag input second)
    {computed : Except Fault SourceValue}
    (executed : sourceBinaryOp operation first second = some computed)
    {frame : TargetFrame} {state : TargetState World} {identity : Nat} {left right : Atom}
    (readLeft : TargetAtomEval interface frame state left (encodeValue first))
    (readRight : TargetAtomEval interface frame state right (encodeValue second))
    (unused : frame.temporaryNames.contains identity = false)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      (NativeLowering.numericGuard operation right ++ [.temporary identity type (.binary operation left right)])
      frame state out ↔
      match computed with
      | .ok value => out = ⟨.normal, targetDeclareTemporary frame identity (encodeValue value), state⟩
      | .error fault => out = ⟨.returned default, frame, targetPoison state fault⟩ := by
  cases scalar with
  | word operation =>
      cases firstTag <;> simp only [binaryType, reduceCtorEq] at typing
      rename_i firstWord
      cases secondTag
      rename_i secondWord
      cases typing
      change some ((NativeWord64.sourceBinary operation firstWord secondWord).map SourceValue.word) =
        some computed at executed
      cases selected : NativeWord64.sourceBinary operation firstWord secondWord with
      | ok value =>
          rw [selected] at executed
          cases Option.some.inj executed
          exact lowered_word_success_exact operation firstWord secondWord value readLeft readRight
            unused selected root out
      | error fault =>
          rw [selected] at executed
          cases Option.some.inj executed
          exact lowered_word_fault_exact operation firstWord secondWord fault readRight selected zero root out
  | compare comparison =>
      obtain ⟨value, same⟩ := unchecked_scalar_source_result (.compare comparison) first second executed
      subst computed
      have pure : TargetPureEval interface frame state (.binary (.compare comparison) left right)
          (encodeValue value) := .binary readLeft readRight
        ((unchecked_scalar_value_result_iff (.compare comparison) first second value).mpr executed)
      exact target_run_temporary_exact unused pure root out

/-- Success reads the computed atom; a refusal returns the enclosing typed zero. -/
def GuardedEvaluationRelated {SourceWorld TargetWorld : Type} (interface : Interface)
    (default : TargetValue) (atom : Atom) (source : SourceState SourceWorld)
    (target : TargetState TargetWorld) (sourceOut : SourceOutcome SourceWorld)
    (targetOut : TargetBlockOutcome TargetWorld) : Prop :=
  match sourceOut.result with
  | .ok value => sourceOut.state = source ∧ targetOut.flow = .normal ∧ targetOut.state = target ∧
      TargetAtomEval interface targetOut.frame targetOut.state atom (encodeValue value)
  | .error fault => sourceOut.state = sourcePoison source fault ∧ targetOut.flow = .returned default ∧
      targetOut.state = targetPoison target fault

theorem guarded_related_normal {SourceWorld TargetWorld : Type} {interface : Interface}
    {default : TargetValue} {atom : Atom} {source : SourceState SourceWorld}
    {target : TargetState TargetWorld} {sourceOut : SourceOutcome SourceWorld}
    {out : TargetBlockOutcome TargetWorld}
    (related : GuardedEvaluationRelated interface default atom source target sourceOut out)
    (normal : out.flow = .normal) :
    ∃ value, sourceOut = ⟨.ok value, source⟩ ∧ out.state = target ∧
      TargetAtomEval interface out.frame out.state atom (encodeValue value) := by
  rcases sourceOut with ⟨answer, post⟩
  cases answer with
  | ok value =>
      rcases related with ⟨same, _, unchanged, read⟩
      change post = source at same
      subst post
      exact ⟨value, rfl, unchanged, read⟩
  | error fault =>
      have impossible := related.2.1
      rw [normal] at impossible
      cases impossible

theorem guarded_related_returned {SourceWorld TargetWorld : Type} {interface : Interface}
    {default value : TargetValue} {atom : Atom} {source : SourceState SourceWorld}
    {target : TargetState TargetWorld} {sourceOut : SourceOutcome SourceWorld}
    {out : TargetBlockOutcome TargetWorld}
    (related : GuardedEvaluationRelated interface default atom source target sourceOut out)
    (returned : out.flow = .returned value) :
    ∃ fault, sourceOut = ⟨.error fault, sourcePoison source fault⟩ ∧ value = default ∧
      out.state = targetPoison target fault := by
  rcases sourceOut with ⟨answer, post⟩
  cases answer with
  | ok value =>
      have impossible := related.2.1
      rw [returned] at impossible
      cases impossible
  | error fault =>
      rcases related with ⟨same, flow, poisoned⟩
      change post = sourcePoison source fault at same
      subst post
      have sameValue := TargetFlow.returned.inj (returned.symm.trans flow)
      exact ⟨fault, rfl, sameValue, poisoned⟩

theorem guarded_target_normal_state {World : Type} {default : TargetValue}
    {before : TargetState World} {out : TargetBlockOutcome World}
    (shape : GuardedTargetState default before out) (normal : out.flow = .normal) :
    out.state = before := by
  rcases shape with ⟨_, same⟩ | ⟨fault, returned, _⟩
  · exact same
  · rw [normal] at returned
    cases returned

end Mettapedia.GSLT.LanguageDef.NativeOps
