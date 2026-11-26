import Mettapedia.GSLT.LanguageDef.NativeOpsStrictBinaryChildren
import Mettapedia.GSLT.LanguageDef.NativeOpsReferenceFieldProfiles

/-!
# Strict binary execution over established child implementations

This composition retains operand order, numeric guards, first-fault returns
and temporary values. It applies to justified memory reads as well as scalars.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Atom Instruction)
open NativeLowering (Expression)
open NativeWord64 (Fault)

variable {SourceWorld TargetWorld : Type}
  {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
  {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
  {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
  {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
  {result : NativeType} {default : TargetValue} {operation : Binary} {left right : Expr}

/-- Read the result and temporary-frame facts from one execution of the guarded suffix. -/
private theorem guarded_binary_suffix_readout {SourceWorld TargetWorld : Type}
    {interface : Interface} {heap : TargetHeapSemantics TargetWorld} {calls : TargetCalls TargetWorld}
    {result type : NativeType} {default : TargetValue} (zero : TargetZero interface result default)
    {operation : Binary} {computed : Except Fault SourceValue}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld} (clear : source.fault = none)
    {frame : TargetFrame} {left right : Atom} {supply : NativeIR.Supply}
    (bounded : TemporaryNamesBound frame supply.next) (hScoped : TemporariesScoped frame)
    {root : List Instruction} {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface heap calls result root
      (NativeLowering.numericGuard operation right ++
        (NativeLowering.pureTemporary supply type (.binary operation left right)).code) frame target out)
    (shape : match computed with
      | .ok value => out = ⟨.normal, targetDeclareTemporary frame (NativeIR.fresh supply).1
          (encodeValue value), target⟩
      | .error fault => out = ⟨.returned default, frame, targetPoison target fault⟩) :
    GuardedEvaluationRelated interface default
      (NativeLowering.pureTemporary supply type (.binary operation left right)).result
      source target (sourceFinish source computed) out ∧
    TemporaryProtection supply.next frame out.frame ∧
    TemporaryNamesBound out.frame (NativeIR.fresh supply).2.next ∧ TemporariesScoped out.frame := by
  have fresh := strict_binary_tail_fresh operation left right type supply
  obtain ⟨_, protection, finalBounded⟩ := fresh_guarded_run_shape zero fresh
    (temporary_names_bound_weaken (Nat.le_of_lt (NativeIR.fresh_strict supply)) bounded) ran
  refine ⟨?_, protection, finalBounded, fresh_guarded_run_scoped fresh hScoped ran⟩
  cases computed with
  | ok value =>
      subst out
      simp only [sourceFinish, sourceObserve, clear, GuardedEvaluationRelated, true_and]
      exact declared_temporary_atom interface frame target (NativeIR.fresh supply).1 type (encodeValue value)
  | error fault =>
      subst out
      simp only [sourceFinish, sourceObserve, sourcePoison, clear, GuardedEvaluationRelated, true_and]

private theorem prefix_and_suffix_protected {initial middle final : Nat}
    {before leftFrame rightFrame after : TargetFrame} (advanceLeft : initial ≤ middle)
    (advanceRight : middle ≤ final) (left : TemporaryProtection initial before leftFrame)
    (right : TemporaryProtection middle leftFrame rightFrame)
    (tail : TemporaryProtection final rightFrame after) :
    TemporaryProtection initial before after :=
  temporary_protection_trans left
    (temporary_protection_weaken advanceLeft (temporary_protection_trans right
      (temporary_protection_weaken advanceRight tail)))

theorem strict_binary_children_strong_preservation (scalar : GuardedScalarBinary operation)
    (first : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default left)
    (second : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default right) (clear : source.fault = none)
    (zero : TargetZero interface result default) (root : List Instruction)
    {supply : NativeIR.Supply} {output : Expression} {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.binary operation left right)
      supply = some output) (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceOutcome SourceWorld}
    (sourceRan : SourceExprEval interface sourceHeap sourceCalls sourceFrame (.binary operation left right)
      source sourceOut) :
    ∃ out, TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      GuardedEvaluationRelated interface default output.result source target sourceOut out ∧
      TemporaryProtection supply.next targetFrame out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  obtain ⟨type, leftOutput, rightOutput, inferred, leftCompiled, rightCompiled, outputShape⟩ :=
    guarded_binary_lowering_exact scalar compiled
  subst output
  obtain ⟨input, leftTyping, rightTyping, operationTyping⟩ := guarded_binary_inferred inferred
  have advanceLeft := (first.bounds leftCompiled).1
  have advanceRight := (second.bounds rightCompiled).1
  have next := NativeIR.fresh_strict rightOutput.supply
  rcases (strict_binary_children_source_exact scalar first second _).mp sourceRan with
    ⟨leftValue, rightValue, computed, leftRan, rightRan, executed, same⟩ |
    ⟨fault, leftRan, same⟩ | ⟨leftValue, fault, leftRan, rightRan, same⟩
  · subst sourceOut
    obtain ⟨⟨leftFlow, middle, middleState⟩, leftTarget, leftRelated, leftProtection, middleBounded, middleScoped⟩ :=
      first.forward root leftCompiled frames states bounded hscope leftRan
    rcases leftRelated with ⟨_, leftNormal, leftUnchanged, leftRead⟩
    cases leftNormal
    change middleState = target at leftUnchanged
    subst middleState
    obtain ⟨⟨rightFlow, last, lastState⟩, rightTarget, rightRelated, rightProtection, lastBounded, lastScoped⟩ :=
      second.forward root rightCompiled (temporary_protection_preserves_source_frame frames leftProtection)
        states middleBounded middleScoped rightRan
    rcases rightRelated with ⟨_, rightNormal, rightUnchanged, rightRead⟩
    cases rightNormal
    change lastState = target at rightUnchanged
    subst lastState
    have leftReadAtLast := (protection_atom_evaluation rightProtection leftOutput.result
      (first.bounds leftCompiled).2 target target (encodeValue leftValue)).mp leftRead
    have firstTag := first.sourceTag leftTyping leftRan
    have secondTag := second.sourceTag rightTyping rightRan
    have suffixExact := guarded_binary_fragment_exact (heap := targetHeap) (calls := targetCalls)
      zero scalar operationTyping firstTag secondTag executed
      leftReadAtLast rightRead (temporary_bound_fresh lastBounded (NativeIR.fresh_strict _)) root
    let out : TargetBlockOutcome TargetWorld := match computed with
      | .ok value => ⟨.normal, targetDeclareTemporary last (NativeIR.fresh rightOutput.supply).1
          (encodeValue value), target⟩
      | .error fault => ⟨.returned default, last, targetPoison target fault⟩
    have tail : TargetRun interface targetHeap targetCalls result root
        (NativeLowering.numericGuard operation rightOutput.result ++
          (NativeLowering.pureTemporary rightOutput.supply type
            (.binary operation leftOutput.result rightOutput.result)).code) last target out :=
      (suffixExact out).mpr (by cases computed <;> rfl)
    have rest := target_append_normal root _ _
      (expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ rightOutput rightCompiled)
      rightTarget tail
    have all := target_append_normal root _ _
      (expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ leftOutput leftCompiled)
      leftTarget rest
    obtain ⟨related, kept, finalBounded, finalScoped⟩ :=
      guarded_binary_suffix_readout (computed := computed) zero clear lastBounded lastScoped tail (by cases computed <;> rfl)
    refine ⟨out, ?_, related,
      prefix_and_suffix_protected (Nat.le_of_lt advanceLeft) (Nat.le_of_lt advanceRight)
        leftProtection rightProtection kept, finalBounded, finalScoped⟩
    simpa only [NativeLowering.prependCode, List.append_assoc] using all
  · subst sourceOut
    obtain ⟨⟨flow, after, post⟩, initialRun, related, kept, afterBounded, afterScoped⟩ :=
      first.forward root leftCompiled frames states bounded hscope leftRan
    rcases related with ⟨_, returned, poisoned⟩
    cases returned
    change post = targetPoison target fault at poisoned
    subst post
    have all := target_append_returned root _
      (rightOutput.code ++ NativeLowering.numericGuard operation rightOutput.result ++
        (NativeLowering.pureTemporary rightOutput.supply type
          (.binary operation leftOutput.result rightOutput.result)).code)
      (expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ leftOutput leftCompiled)
      initialRun
    refine ⟨⟨.returned default, after, targetPoison target fault⟩, ?_,
      ⟨rfl, rfl, rfl⟩, kept,
      guarded_temporary_bound_mono afterBounded (Nat.le_of_lt (advanceRight.trans next)), afterScoped⟩
    simpa only [NativeLowering.prependCode, List.append_assoc] using all
  · subst sourceOut
    obtain ⟨⟨flow, middle, post⟩, leftTarget, leftRelated, leftProtection, middleBounded, middleScoped⟩ :=
      first.forward root leftCompiled frames states bounded hscope leftRan
    rcases leftRelated with ⟨_, normal, unchanged, _⟩
    cases normal
    change post = target at unchanged
    subst post
    obtain ⟨⟨flow, after, post⟩, rightTarget, rightRelated, kept, afterBounded, afterScoped⟩ :=
      second.forward root rightCompiled (temporary_protection_preserves_source_frame frames leftProtection)
        states middleBounded middleScoped rightRan
    rcases rightRelated with ⟨_, returned, poisoned⟩
    cases returned
    change post = targetPoison target fault at poisoned
    subst post
    have rest := target_append_returned root rightOutput.code
      (NativeLowering.numericGuard operation rightOutput.result ++
        (NativeLowering.pureTemporary rightOutput.supply type
          (.binary operation leftOutput.result rightOutput.result)).code)
      (expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ rightOutput rightCompiled)
      rightTarget
    have all := target_append_normal root _ _
      (expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ leftOutput leftCompiled)
      leftTarget rest
    refine ⟨⟨.returned default, after, targetPoison target fault⟩, ?_,
      ⟨rfl, rfl, rfl⟩,
      temporary_protection_trans leftProtection (temporary_protection_weaken (Nat.le_of_lt advanceLeft) kept),
      guarded_temporary_bound_mono afterBounded (Nat.le_of_lt next), afterScoped⟩
    simpa only [NativeLowering.prependCode, List.append_assoc] using all

theorem strict_binary_children_preservation (scalar : GuardedScalarBinary operation)
    (first : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default left)
    (second : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default right) (clear : source.fault = none)
    (zero : TargetZero interface result default) (root : List Instruction)
    {supply : NativeIR.Supply} {output : Expression} {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.binary operation left right)
      supply = some output) (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceOutcome SourceWorld}
    (sourceRan : SourceExprEval interface sourceHeap sourceCalls sourceFrame (.binary operation left right)
      source sourceOut) :
    ∃ out, TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      GuardedEvaluationRelated interface default output.result source target sourceOut out := by
  obtain ⟨out, ran, related, _, _, _⟩ :=
    strict_binary_children_strong_preservation scalar first second clear zero
      root compiled frames states bounded hscope sourceRan
  exact ⟨out, ran, related⟩

theorem strict_binary_children_reflection (scalar : GuardedScalarBinary operation)
    (first : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default left)
    (second : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default right) (clear : source.fault = none)
    (zero : TargetZero interface result default) (root : List Instruction)
    {supply : NativeIR.Supply} {output : Expression} {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.binary operation left right)
      supply = some output) (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out) :
    ∃ sourceOut, SourceExprEval interface sourceHeap sourceCalls sourceFrame (.binary operation left right) source sourceOut ∧
      GuardedEvaluationRelated interface default output.result source target sourceOut out ∧
      TemporaryProtection supply.next targetFrame out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  obtain ⟨type, leftOutput, rightOutput, inferred, leftCompiled, rightCompiled, outputShape⟩ :=
    guarded_binary_lowering_exact scalar compiled
  subst output
  obtain ⟨input, leftTyping, rightTyping, operationTyping⟩ := guarded_binary_inferred inferred
  have advanceLeft := (first.bounds leftCompiled).1
  have advanceRight := (second.bounds rightCompiled).1
  have next := NativeIR.fresh_strict rightOutput.supply
  have ordered : TargetRun interface targetHeap targetCalls result root
      (leftOutput.code ++ (rightOutput.code ++ (NativeLowering.numericGuard operation rightOutput.result ++
        (NativeLowering.pureTemporary rightOutput.supply type
          (.binary operation leftOutput.result rightOutput.result)).code))) targetFrame target out := by
    simpa only [NativeLowering.prependCode, List.append_assoc] using ran
  rcases target_split_jump_free_prefix root leftOutput.code _
      (expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ leftOutput leftCompiled)
      ordered with ⟨middle, post, leftTarget, rest⟩ | ⟨value, after, post, leftTarget, same⟩
  · obtain ⟨leftOut, leftSource, leftRelated, leftProtection, middleBounded, middleScoped⟩ :=
      first.backward root leftCompiled frames states bounded hscope leftTarget
    obtain ⟨leftValue, exactLeft, unchanged, leftRead⟩ := guarded_related_normal leftRelated rfl
    subst leftOut
    change post = target at unchanged
    subst post
    rcases target_split_jump_free_prefix root rightOutput.code _
        (expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ rightOutput rightCompiled)
        rest with ⟨last, post, rightTarget, tail⟩ | ⟨value, after, post, rightTarget, same⟩
    · obtain ⟨rightOut, rightSource, rightRelated, rightProtection, lastBounded, lastScoped⟩ :=
        second.backward root rightCompiled (temporary_protection_preserves_source_frame frames leftProtection)
          states middleBounded middleScoped rightTarget
      obtain ⟨rightValue, exactRight, unchanged, rightRead⟩ := guarded_related_normal rightRelated rfl
      subst rightOut
      change post = target at unchanged
      subst post
      have leftReadAtLast := (protection_atom_evaluation rightProtection leftOutput.result
        (first.bounds leftCompiled).2 target target (encodeValue leftValue)).mp leftRead
      have firstTag := first.sourceTag leftTyping leftSource
      have secondTag := second.sourceTag rightTyping rightSource
      obtain ⟨computed, executed, _⟩ := source_binary_typed_defined operationTyping firstTag secondTag
      have suffixExact := (guarded_binary_fragment_exact zero scalar operationTyping firstTag secondTag
        executed leftReadAtLast rightRead (temporary_bound_fresh lastBounded next) root out).mp tail
      obtain ⟨related, tailProtection, finalBounded, finalScoped⟩ :=
        guarded_binary_suffix_readout (computed := computed) zero clear lastBounded lastScoped tail (by cases computed <;> exact suffixExact)
      have protection := prefix_and_suffix_protected (Nat.le_of_lt advanceLeft)
        (Nat.le_of_lt advanceRight) leftProtection rightProtection tailProtection
      have sourceRan : SourceExprEval interface sourceHeap sourceCalls sourceFrame
          (.binary operation left right) source (sourceFinish source computed) :=
        (strict_binary_children_source_exact scalar first second _).mpr
          (.inl ⟨leftValue, rightValue, computed, leftSource, rightSource, executed, rfl⟩)
      exact ⟨sourceFinish source computed, sourceRan, related, protection, finalBounded, finalScoped⟩
    · obtain ⟨sourceOut, sourceRan, related, protection, afterBounded, afterScoped⟩ :=
        second.backward root rightCompiled (temporary_protection_preserves_source_frame frames leftProtection)
          states middleBounded middleScoped rightTarget
      obtain ⟨fault, exactSource, exactDefault, poisoned⟩ := guarded_related_returned related rfl
      subst sourceOut
      subst value
      change post = targetPoison target fault at poisoned
      subst post
      subst out
      exact ⟨⟨.error fault, sourcePoison source fault⟩,
        (strict_binary_children_source_exact scalar first second _).mpr
          (.inr (.inr ⟨leftValue, fault, leftSource, sourceRan, rfl⟩)), ⟨rfl, rfl, rfl⟩,
        temporary_protection_trans leftProtection (temporary_protection_weaken (Nat.le_of_lt advanceLeft) protection),
        guarded_temporary_bound_mono afterBounded (Nat.le_of_lt next), afterScoped⟩
  · obtain ⟨sourceOut, sourceRan, related, protection, afterBounded, afterScoped⟩ :=
      first.backward root leftCompiled frames states bounded hscope leftTarget
    obtain ⟨fault, exactSource, exactDefault, poisoned⟩ := guarded_related_returned related rfl
    subst sourceOut
    subst value
    change post = targetPoison target fault at poisoned
    subst post
    subst out
    exact ⟨⟨.error fault, sourcePoison source fault⟩,
      (strict_binary_children_source_exact scalar first second _).mpr
        (.inr (.inl ⟨fault, sourceRan, rfl⟩)), ⟨rfl, rfl, rfl⟩, protection,
      guarded_temporary_bound_mono afterBounded (Nat.le_of_lt (advanceRight.trans next)), afterScoped⟩

theorem strict_binary_children_laws (scalar : GuardedScalarBinary operation)
    (first : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default left)
    (second : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default right) (clear : source.fault = none)
    (zero : TargetZero interface result default) :
    ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.binary operation left right) :=
  ⟨strict_binary_children_source_state scalar first second clear,
    strict_binary_children_source_tag scalar first second clear,
    strict_binary_children_bounds scalar first second,
    strict_binary_children_strong_preservation scalar first second clear zero,
    strict_binary_children_reflection scalar first second clear zero⟩

theorem stateful_guarded_binary_fragment_profile {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {heap : TargetHeapSemantics TargetWorld} {calls : TargetCalls TargetWorld}
    {result input type : NativeType} {default : TargetValue} (zero : TargetZero interface result default)
    {operation : Binary} (scalar : GuardedScalarBinary operation)
    {first second : SourceValue} (typing : binaryType operation input = some type)
    (firstTag : SourceOuterTag input first) (secondTag : SourceOuterTag input second)
    {computed : Except Fault SourceValue} (executed : sourceBinaryOp operation first second = some computed)
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    {frame : TargetFrame} {left right : Atom} {supply : NativeIR.Supply}
    (readLeft : TargetAtomEval interface frame target left (encodeValue first))
    (readRight : TargetAtomEval interface frame target right (encodeValue second))
    (bounded : TemporaryNamesBound frame supply.next) (hscope : TemporariesScoped frame)
    (root : List Instruction) {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface heap calls result root
      (NativeLowering.numericGuard operation right ++
        (NativeLowering.pureTemporary supply type (.binary operation left right)).code) frame target out) :
    CheckedExpressionRelated worldRelated interface default
      (NativeLowering.pureTemporary supply type (.binary operation left right)).result
      (sourceFinish source computed) out ∧
    TemporaryProtection supply.next frame out.frame ∧
    TemporaryNamesBound out.frame (NativeIR.fresh supply).2.next ∧ TemporariesScoped out.frame := by
  have same := (guarded_binary_fragment_exact zero scalar typing firstTag secondTag executed readLeft readRight
    (temporary_bound_fresh bounded (NativeIR.fresh_strict supply)) root out).mp ran
  obtain ⟨related, protection, outBounded, finalScoped⟩ :=
    guarded_binary_suffix_readout (computed := computed) zero clear bounded hscope ran (by cases computed <;> exact same)
  exact ⟨guarded_related_checked states clear related, protection, outBounded, finalScoped⟩

theorem stateful_guarded_binary_primitive_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld)
    (result : NativeType) (default : TargetValue) {operation : Binary}
    (scalar : GuardedScalarBinary operation) (zero : TargetZero interface result default)
    (left right : Expr) {input type : NativeType}
    (firstTyping : inferExpr interface (sourceFrameScope sourceFrame) left = some input)
    (secondTyping : inferExpr interface (sourceFrameScope sourceFrame) right = some input)
    (operationTyping : binaryType operation input = some type)
    (tagged : ∀ expression ∈ [left, right], ∀ before post value type,
      inferExpr interface (sourceFrameScope sourceFrame) expression = some type →
      SourceExprEval interface sourceHeap sourceCalls sourceFrame expression before ⟨.ok value, post⟩ →
      SourceOuterTag type value)
    (first second : NativeLowering.Expression) :
    StatefulPrimitiveLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.binary operation left right) [left, right]
      ⟨first.code ++ second.code, [first.result, second.result], second.supply⟩
      (NativeLowering.prependCode (NativeLowering.numericGuard operation second.result)
        (NativeLowering.pureTemporary second.supply type (.binary operation first.result second.result))) := by
  refine ⟨⟨Nat.le_of_lt (NativeIR.fresh_strict second.supply), Nat.le_refl _⟩, ?_, ?_⟩
  · intro root values middle argsRan clear frame target _ states bounded hscope reads sourceOut primitiveRan
    obtain ⟨rawLeft, rawRight, valuesSame, readLeft, readRight⟩ := target_two_encoded_arguments reads
    subst values
    obtain ⟨computed, _, _, executed, same⟩ := primitiveRan
    subst sourceOut
    have tags := source_two_arguments_success_tags tagged firstTyping secondTyping argsRan
    let out : TargetBlockOutcome TargetWorld := match computed with
      | .ok value => ⟨.normal, targetDeclareTemporary frame (NativeIR.fresh second.supply).1
          (encodeValue value), target⟩
      | .error fault => ⟨.returned default, frame, targetPoison target fault⟩
    have suffix : TargetRun interface targetHeap targetCalls result root
        (NativeLowering.numericGuard operation second.result ++
          (NativeLowering.pureTemporary second.supply type (.binary operation first.result second.result)).code)
        frame target out :=
      (guarded_binary_fragment_exact zero scalar operationTyping tags.1 tags.2 executed readLeft readRight
        (temporary_bound_fresh bounded (NativeIR.fresh_strict second.supply)) root out).mpr
        (by cases computed <;> rfl)
    obtain ⟨checked, protection, finalBounded, finalScoped⟩ := stateful_guarded_binary_fragment_profile
      zero scalar operationTyping tags.1 tags.2 executed states clear readLeft readRight bounded hscope root suffix
    exact ⟨out, suffix, checked, protection, finalBounded, finalScoped⟩
  · intro root values middle argsRan clear frame target _ states bounded hscope reads out ran
    obtain ⟨rawLeft, rawRight, valuesSame, readLeft, readRight⟩ := target_two_encoded_arguments reads
    subst values
    have tags := source_two_arguments_success_tags tagged firstTyping secondTyping argsRan
    obtain ⟨computed, executed, _⟩ := source_binary_typed_defined operationTyping tags.1 tags.2
    obtain ⟨checked, protection, finalBounded, finalScoped⟩ := stateful_guarded_binary_fragment_profile
      zero scalar operationTyping tags.1 tags.2 executed states clear readLeft readRight bounded hscope root ran
    exact ⟨sourceFinish middle computed,
      ⟨computed, guarded_scalar_not_and scalar, guarded_scalar_not_or scalar, executed, rfl⟩,
      checked, protection, finalBounded, finalScoped⟩

theorem stateful_guarded_binary_child_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld) (clear : source.fault = none)
    (result : NativeType) (default : TargetValue) {operation : Binary}
    (scalar : GuardedScalarBinary operation) (zero : TargetZero interface result default) (left right : Expr)
    (children : ∀ expression ∈ [left, right], ∀ before, before.fault = none →
      StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
        sourceFrame before result default expression)
    (tagged : ∀ expression ∈ [left, right], ∀ before post value type,
      inferExpr interface (sourceFrameScope sourceFrame) expression = some type →
      SourceExprEval interface sourceHeap sourceCalls sourceFrame expression before ⟨.ok value, post⟩ →
      SourceOuterTag type value) :
    StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.binary operation left right) := by
  apply stateful_strict_child_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
    sourceFrame source clear result default (.binary operation left right) [left, right]
    (guarded_scalar_operands scalar left right) children
  intro supply output compiled
  obtain ⟨type, first, second, inferred, firstCompiled, secondCompiled, shape⟩ :=
    guarded_binary_lowering_exact scalar compiled
  obtain ⟨input, firstTyping, secondTyping, operationTyping⟩ := guarded_binary_inferred inferred
  refine ⟨⟨first.code ++ second.code, [first.result, second.result], second.supply⟩,
    NativeLowering.prependCode (NativeLowering.numericGuard operation second.result)
      (NativeLowering.pureTemporary second.supply type (.binary operation first.result second.result)),
    arguments_lowering_pair interface (sourceFrameScope sourceFrame) left right firstCompiled secondCompiled,
    ?_, stateful_guarded_binary_primitive_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default scalar zero left right firstTyping secondTyping operationTyping tagged first second⟩
  simpa only [NativeLowering.prependCode, List.append_assoc] using shape

end Mettapedia.GSLT.LanguageDef.NativeOps
