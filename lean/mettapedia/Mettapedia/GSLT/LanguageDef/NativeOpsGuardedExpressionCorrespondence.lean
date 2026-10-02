import Mettapedia.GSLT.LanguageDef.NativeOpsGuardedExpressionLowering

/-!
# Two-sided execution of admitted guarded scalar expressions

Successful local setup supplies the scalar tags used here. The compilation
environment is the actual source frame's declared scope. Target paths execute
the emitted guards and private temporaries, including ordered early returns.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Atom)
open NativeLowering (Expression)
open NativeWord64 (Fault)

theorem guarded_expression_run_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    (tagged : SourceLocalsTagged sourceFrame source.memory)
    (result : NativeType) {default : TargetValue} (zero : TargetZero interface result default)
    (root : List Instruction) {expression : Expr} (guarded : SourceGuardedExpression expression) :
    ∀ {supply : NativeIR.Supply} {output : Expression} {targetFrame : TargetFrame},
      NativeLowering.expression? interface (sourceFrameScope sourceFrame) expression supply = some output →
      FrameRelated sourceFrame targetFrame → TemporaryNamesBound targetFrame supply.next →
      ∀ {sourceOut : SourceOutcome SourceWorld},
      SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source sourceOut →
      ∃ out,
        TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
        GuardedEvaluationRelated interface default output.result source target sourceOut out ∧
        TemporaryProtection supply.next targetFrame out.frame ∧ TemporaryNamesBound out.frame output.supply.next := by
  induction guarded with
  | leaf leaf =>
      intro supply output targetFrame compiled frames bounded sourceOut sourceRan
      obtain ⟨value, same⟩ := source_scalar_run_shape (.leaf leaf) source clear sourceRan
      subst sourceOut
      obtain ⟨after, ran, read, protection, afterBounded⟩ :=
        scalar_expression_value_preservation sourceHeap sourceCalls targetHeap targetCalls states clear
          result root (.leaf leaf) compiled frames bounded sourceRan
      exact ⟨⟨.normal, after, target⟩, ran, ⟨rfl, rfl, rfl, read⟩, protection, afterBounded⟩
  | unary operation child ih =>
      intro supply output targetFrame compiled frames bounded sourceOut sourceRan
      obtain ⟨type, operandOutput, _, operandCompiled, outputShape⟩ := scalar_unary_lowering_exact compiled
      subst output
      rcases (source_guarded_unary_exact operation child source clear _).mp sourceRan with
        ⟨first, value, operandRan, computed, same⟩ | ⟨fault, operandRan, same⟩
      · subst sourceOut
        obtain ⟨⟨flow, middle, post⟩, initialRun, related, _, middleBounded⟩ :=
          ih operandCompiled frames bounded operandRan
        rcases related with ⟨_, normal, unchanged, read⟩
        cases normal
        change post = target at unchanged
        subst post
        let after := targetDeclareTemporary middle (NativeIR.fresh operandOutput.supply).1 (encodeValue value)
        have tail : TargetRun interface targetHeap targetCalls result root
            (NativeLowering.pureTemporary operandOutput.supply type (.unary operation operandOutput.result)).code
            middle target ⟨.normal, after, target⟩ :=
          (lowered_unary_success_exact operation first value read
            (temporary_bound_fresh middleBounded (NativeIR.fresh_strict _)) computed root _).mpr rfl
        have ran := target_append_normal root _ _
          (expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ operandOutput operandCompiled)
          initialRun tail
        have shape := guarded_target_run_shape zero (.unary operation child) compiled bounded ran
        exact ⟨⟨.normal, after, target⟩, ran,
          ⟨rfl, rfl, rfl, declared_temporary_atom interface middle target
            (NativeIR.fresh operandOutput.supply).1 type (encodeValue value)⟩,
          shape.2.1, shape.2.2⟩
      · subst sourceOut
        obtain ⟨⟨flow, after, post⟩, initialRun, related, _, _⟩ :=
          ih operandCompiled frames bounded operandRan
        rcases related with ⟨_, returned, poisoned⟩
        cases returned
        change post = targetPoison target fault at poisoned
        subst post
        have ran := target_append_returned root operandOutput.code
          (NativeLowering.pureTemporary operandOutput.supply type (.unary operation operandOutput.result)).code
          (expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ operandOutput operandCompiled)
          initialRun
        have shape := guarded_target_run_shape zero (.unary operation child) compiled bounded ran
        exact ⟨⟨.returned default, after, targetPoison target fault⟩, ran,
          ⟨rfl, rfl, rfl⟩, shape.2.1, shape.2.2⟩
  | binary scalar first second firstIH secondIH =>
      rename_i operation left right
      intro supply output targetFrame compiled frames bounded sourceOut sourceRan
      obtain ⟨type, leftOutput, rightOutput, inferred, leftCompiled, rightCompiled, outputShape⟩ :=
        guarded_binary_lowering_exact scalar compiled
      subst output
      obtain ⟨input, leftTyping, rightTyping, operationTyping⟩ := guarded_binary_inferred inferred
      rcases (source_guarded_binary_exact scalar first second source clear _).mp sourceRan with
        ⟨leftValue, rightValue, computed, leftRan, rightRan, executed, same⟩ |
        ⟨fault, leftRan, same⟩ | ⟨leftValue, fault, leftRan, rightRan, same⟩
      · subst sourceOut
        obtain ⟨⟨leftFlow, middle, middleState⟩, leftTarget, leftRelated, leftProtection, middleBounded⟩ :=
          firstIH leftCompiled frames bounded leftRan
        rcases leftRelated with ⟨_, leftNormal, leftUnchanged, leftRead⟩
        cases leftNormal
        change middleState = target at leftUnchanged
        subst middleState
        obtain ⟨⟨rightFlow, last, lastState⟩, rightTarget, rightRelated, rightProtection, lastBounded⟩ :=
          secondIH rightCompiled (temporary_protection_preserves_source_frame frames leftProtection)
            middleBounded rightRan
        rcases rightRelated with ⟨_, rightNormal, rightUnchanged, rightRead⟩
        cases rightNormal
        change lastState = target at rightUnchanged
        subst lastState
        have leftReadAtLast := (protection_atom_evaluation rightProtection leftOutput.result
          (guarded_result_atom_within first leftCompiled) target target (encodeValue leftValue)).mp leftRead
        have firstTag := source_guarded_success_tag first source clear tagged leftTyping leftRan
        have secondTag := source_guarded_success_tag second source clear tagged rightTyping rightRan
        have suffixExact := guarded_binary_fragment_exact (heap := targetHeap) (calls := targetCalls)
          zero scalar operationTyping firstTag secondTag executed
          leftReadAtLast rightRead (temporary_bound_fresh lastBounded (NativeIR.fresh_strict _)) root
        cases computed with
        | ok value =>
            let after := targetDeclareTemporary last (NativeIR.fresh rightOutput.supply).1 (encodeValue value)
            have tail : TargetRun interface targetHeap targetCalls result root
                (NativeLowering.numericGuard operation rightOutput.result ++
                  (NativeLowering.pureTemporary rightOutput.supply type
                    (.binary operation leftOutput.result rightOutput.result)).code)
                last target ⟨.normal, after, target⟩ := (suffixExact _).mpr rfl
            have rest := target_append_normal root _ _
              (expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ rightOutput rightCompiled)
              rightTarget tail
            have all := target_append_normal root _ _
              (expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ leftOutput leftCompiled)
              leftTarget rest
            have ran : TargetRun interface targetHeap targetCalls result root
                (NativeLowering.prependCode
                  (leftOutput.code ++ rightOutput.code ++ NativeLowering.numericGuard operation rightOutput.result)
                  (NativeLowering.pureTemporary rightOutput.supply type
                    (.binary operation leftOutput.result rightOutput.result))).code targetFrame target
                ⟨.normal, after, target⟩ := by
              simpa only [NativeLowering.prependCode, List.append_assoc] using all
            have shape := guarded_target_run_shape zero (.binary scalar first second) compiled bounded ran
            refine ⟨⟨.normal, after, target⟩, ran, ?_, shape.2.1, shape.2.2⟩
            simp only [sourceFinish, sourceObserve, clear, GuardedEvaluationRelated, true_and]
            exact declared_temporary_atom interface last target
              (NativeIR.fresh rightOutput.supply).1 type (encodeValue value)
        | error fault =>
            have tail : TargetRun interface targetHeap targetCalls result root
                (NativeLowering.numericGuard operation rightOutput.result ++
                  (NativeLowering.pureTemporary rightOutput.supply type
                    (.binary operation leftOutput.result rightOutput.result)).code)
                last target ⟨.returned default, last, targetPoison target fault⟩ := (suffixExact _).mpr rfl
            have rest := target_append_normal root _ _
              (expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ rightOutput rightCompiled)
              rightTarget tail
            have all := target_append_normal root _ _
              (expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ leftOutput leftCompiled)
              leftTarget rest
            have ran : TargetRun interface targetHeap targetCalls result root
                (NativeLowering.prependCode
                  (leftOutput.code ++ rightOutput.code ++ NativeLowering.numericGuard operation rightOutput.result)
                  (NativeLowering.pureTemporary rightOutput.supply type
                    (.binary operation leftOutput.result rightOutput.result))).code targetFrame target
                ⟨.returned default, last, targetPoison target fault⟩ := by
              simpa only [NativeLowering.prependCode, List.append_assoc] using all
            have shape := guarded_target_run_shape zero (.binary scalar first second) compiled bounded ran
            refine ⟨⟨.returned default, last, targetPoison target fault⟩, ran, ?_, shape.2.1, shape.2.2⟩
            simp only [sourceFinish, sourceObserve, sourcePoison, clear, GuardedEvaluationRelated, true_and]
      · subst sourceOut
        obtain ⟨⟨flow, after, post⟩, initialRun, related, _, _⟩ :=
          firstIH leftCompiled frames bounded leftRan
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
        have ran : TargetRun interface targetHeap targetCalls result root
            (NativeLowering.prependCode
              (leftOutput.code ++ rightOutput.code ++ NativeLowering.numericGuard operation rightOutput.result)
              (NativeLowering.pureTemporary rightOutput.supply type
                (.binary operation leftOutput.result rightOutput.result))).code targetFrame target
            ⟨.returned default, after, targetPoison target fault⟩ := by
          simpa only [NativeLowering.prependCode, List.append_assoc] using all
        have shape := guarded_target_run_shape zero (.binary scalar first second) compiled bounded ran
        exact ⟨⟨.returned default, after, targetPoison target fault⟩, ran,
          ⟨rfl, rfl, rfl⟩, shape.2.1, shape.2.2⟩
      · subst sourceOut
        obtain ⟨⟨flow, middle, post⟩, leftTarget, leftRelated, leftProtection, middleBounded⟩ :=
          firstIH leftCompiled frames bounded leftRan
        rcases leftRelated with ⟨_, normal, unchanged, _⟩
        cases normal
        change post = target at unchanged
        subst post
        obtain ⟨⟨flow, after, post⟩, rightTarget, rightRelated, _, _⟩ :=
          secondIH rightCompiled (temporary_protection_preserves_source_frame frames leftProtection)
            middleBounded rightRan
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
        have ran : TargetRun interface targetHeap targetCalls result root
            (NativeLowering.prependCode
              (leftOutput.code ++ rightOutput.code ++ NativeLowering.numericGuard operation rightOutput.result)
              (NativeLowering.pureTemporary rightOutput.supply type
                (.binary operation leftOutput.result rightOutput.result))).code targetFrame target
            ⟨.returned default, after, targetPoison target fault⟩ := by
          simpa only [NativeLowering.prependCode, List.append_assoc] using all
        have shape := guarded_target_run_shape zero (.binary scalar first second) compiled bounded ran
        exact ⟨⟨.returned default, after, targetPoison target fault⟩, ran,
          ⟨rfl, rfl, rfl⟩, shape.2.1, shape.2.2⟩

/-- Any emitted path is authorized by a source evaluation, including refusal paths. -/
theorem guarded_expression_run_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    (tagged : SourceLocalsTagged sourceFrame source.memory)
    (result : NativeType) {default : TargetValue} (zero : TargetZero interface result default)
    (root : List Instruction) {expression : Expr} (guarded : SourceGuardedExpression expression) :
    ∀ {supply : NativeIR.Supply} {output : Expression} {targetFrame : TargetFrame},
      NativeLowering.expression? interface (sourceFrameScope sourceFrame) expression supply = some output →
      FrameRelated sourceFrame targetFrame → TemporaryNamesBound targetFrame supply.next →
      ∀ {out : TargetBlockOutcome TargetWorld},
      TargetRun interface targetHeap targetCalls result root output.code targetFrame target out →
      ∃ sourceOut,
        SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source sourceOut ∧
        GuardedEvaluationRelated interface default output.result source target sourceOut out := by
  induction guarded with
  | leaf leaf =>
      intro supply output targetFrame compiled frames bounded out ran
      obtain ⟨value, sourceRan, read⟩ := scalar_expression_value_reflection sourceHeap sourceCalls
        targetHeap targetCalls states clear result root (.leaf leaf) compiled frames bounded ran
      have shape := scalar_target_run_shape (.leaf leaf) compiled bounded ran
      exact ⟨⟨.ok value, source⟩, sourceRan, ⟨rfl, shape.1, shape.2.1, read⟩⟩
  | unary operation child ih =>
      intro supply output targetFrame compiled frames bounded out ran
      obtain ⟨type, operandOutput, _, operandCompiled, outputShape⟩ := scalar_unary_lowering_exact compiled
      subst output
      rcases target_split_jump_free_prefix root operandOutput.code _
        (expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ operandOutput operandCompiled)
        ran with ⟨middle, post, initialRun, tail⟩ | ⟨value, after, post, initialRun, same⟩
      · have shape := guarded_target_run_shape zero child operandCompiled bounded initialRun
        have unchanged := guarded_target_normal_state shape.1 rfl
        change post = target at unchanged
        subst post
        obtain ⟨sourceOut, sourceRan, related⟩ := ih operandCompiled frames bounded initialRun
        obtain ⟨first, exactSource, _, operandRead⟩ := guarded_related_normal related rfl
        subst sourceOut
        obtain ⟨actual, pure, same⟩ := (target_pure_temporary_any_exact interface targetHeap targetCalls
          result root middle target (NativeIR.fresh operandOutput.supply).1 type
          (.unary operation operandOutput.result)
          (temporary_bound_fresh shape.2.2 (NativeIR.fresh_strict _)) out).mp tail
        cases pure with
        | unary otherRead computed =>
            cases target_atom_unique operandRead otherRead
            let value := decodeValue actual
            have sourceComputed : sourceUnaryOp operation first = some value := by
              apply (unary_value_result_iff operation first value).mp
              simpa only [value, encode_decode_value] using computed
            subst out
            refine ⟨⟨.ok value, source⟩,
              (source_guarded_unary_exact operation child source clear _).mpr
                (.inl ⟨first, value, sourceRan, sourceComputed, rfl⟩), ?_⟩
            exact ⟨rfl, rfl, rfl, by
              simpa only [value, encode_decode_value, NativeLowering.prependCode,
                NativeLowering.pureTemporary] using declared_temporary_atom interface middle target
                  (NativeIR.fresh operandOutput.supply).1 type actual⟩
      · obtain ⟨sourceOut, sourceRan, related⟩ := ih operandCompiled frames bounded initialRun
        obtain ⟨fault, exactSource, exactDefault, poisoned⟩ := guarded_related_returned related rfl
        subst sourceOut
        subst value
        change post = targetPoison target fault at poisoned
        subst post
        subst out
        exact ⟨⟨.error fault, sourcePoison source fault⟩,
          (source_guarded_unary_exact operation child source clear _).mpr
            (.inr ⟨fault, sourceRan, rfl⟩), ⟨rfl, rfl, rfl⟩⟩
  | binary scalar first second firstIH secondIH =>
      rename_i operation left right
      intro supply output targetFrame compiled frames bounded out ran
      obtain ⟨type, leftOutput, rightOutput, inferred, leftCompiled, rightCompiled, outputShape⟩ :=
        guarded_binary_lowering_exact scalar compiled
      subst output
      obtain ⟨input, leftTyping, rightTyping, operationTyping⟩ := guarded_binary_inferred inferred
      have ordered : TargetRun interface targetHeap targetCalls result root
          (leftOutput.code ++ (rightOutput.code ++ (NativeLowering.numericGuard operation rightOutput.result ++
            (NativeLowering.pureTemporary rightOutput.supply type
              (.binary operation leftOutput.result rightOutput.result)).code))) targetFrame target out := by
        simpa only [NativeLowering.prependCode, List.append_assoc] using ran
      rcases target_split_jump_free_prefix root leftOutput.code _
        (expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ leftOutput leftCompiled)
        ordered with ⟨middle, post, leftTarget, rest⟩ | ⟨value, after, post, leftTarget, same⟩
      · have leftShape := guarded_target_run_shape zero first leftCompiled bounded leftTarget
        have unchanged := guarded_target_normal_state leftShape.1 rfl
        change post = target at unchanged
        subst post
        obtain ⟨leftSourceOut, leftSource, leftRelated⟩ := firstIH leftCompiled frames bounded leftTarget
        obtain ⟨leftValue, exactLeft, _, leftRead⟩ := guarded_related_normal leftRelated rfl
        subst leftSourceOut
        rcases target_split_jump_free_prefix root rightOutput.code _
          (expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ rightOutput rightCompiled)
          rest with ⟨last, post, rightTarget, tail⟩ | ⟨value, after, post, rightTarget, same⟩
        · have rightShape := guarded_target_run_shape zero second rightCompiled leftShape.2.2 rightTarget
          have unchanged := guarded_target_normal_state rightShape.1 rfl
          change post = target at unchanged
          subst post
          obtain ⟨rightSourceOut, rightSource, rightRelated⟩ :=
            secondIH rightCompiled (temporary_protection_preserves_source_frame frames leftShape.2.1)
              leftShape.2.2 rightTarget
          obtain ⟨rightValue, exactRight, _, rightRead⟩ := guarded_related_normal rightRelated rfl
          subst rightSourceOut
          have leftReadAtLast := (protection_atom_evaluation rightShape.2.1 leftOutput.result
            (guarded_result_atom_within first leftCompiled) target target (encodeValue leftValue)).mp leftRead
          have firstTag := source_guarded_success_tag first source clear tagged leftTyping leftSource
          have secondTag := source_guarded_success_tag second source clear tagged rightTyping rightSource
          obtain ⟨computed, executed, _⟩ := source_binary_typed_defined operationTyping firstTag secondTag
          have suffixExact := (guarded_binary_fragment_exact zero scalar operationTyping firstTag secondTag
            executed leftReadAtLast rightRead (temporary_bound_fresh rightShape.2.2 (NativeIR.fresh_strict _))
            root out).mp tail
          have sourceRan : SourceExprEval interface sourceHeap sourceCalls sourceFrame
              (.binary operation left right) source (sourceFinish source computed) :=
            (source_guarded_binary_exact scalar first second source clear _).mpr
              (.inl ⟨leftValue, rightValue, computed, leftSource, rightSource, executed, rfl⟩)
          refine ⟨sourceFinish source computed, sourceRan, ?_⟩
          cases computed with
          | ok value =>
              subst out
              simp only [sourceFinish, sourceObserve, clear, GuardedEvaluationRelated, true_and]
              exact declared_temporary_atom interface last target
                (NativeIR.fresh rightOutput.supply).1 type (encodeValue value)
          | error fault =>
              subst out
              simp only [sourceFinish, sourceObserve, sourcePoison, clear, GuardedEvaluationRelated, true_and]
        · obtain ⟨sourceOut, sourceRan, related⟩ :=
            secondIH rightCompiled (temporary_protection_preserves_source_frame frames leftShape.2.1)
              leftShape.2.2 rightTarget
          obtain ⟨fault, exactSource, exactDefault, poisoned⟩ := guarded_related_returned related rfl
          subst sourceOut
          subst value
          change post = targetPoison target fault at poisoned
          subst post
          subst out
          exact ⟨⟨.error fault, sourcePoison source fault⟩,
            (source_guarded_binary_exact scalar first second source clear _).mpr
              (.inr (.inr ⟨leftValue, fault, leftSource, sourceRan, rfl⟩)), ⟨rfl, rfl, rfl⟩⟩
      · obtain ⟨sourceOut, sourceRan, related⟩ := firstIH leftCompiled frames bounded leftTarget
        obtain ⟨fault, exactSource, exactDefault, poisoned⟩ := guarded_related_returned related rfl
        subst sourceOut
        subst value
        change post = targetPoison target fault at poisoned
        subst post
        subst out
        exact ⟨⟨.error fault, sourcePoison source fault⟩,
          (source_guarded_binary_exact scalar first second source clear _).mpr
            (.inr (.inl ⟨fault, sourceRan, rfl⟩)), ⟨rfl, rfl, rfl⟩⟩

theorem guarded_related_observation_correspondence {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {default : TargetValue} {atom : Atom} {source : SourceState SourceWorld}
    {target : TargetState TargetWorld} {sourceOut : SourceOutcome SourceWorld}
    {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    (related : GuardedEvaluationRelated interface default atom source target sourceOut out)
    (observation : targetExpressionObservation interface atom out observed) :
    OutcomeRelated worldRelated sourceOut observed := by
  rcases sourceOut with ⟨answer, sourcePost⟩
  rcases out with ⟨flow, frame, targetPost⟩
  cases answer with
  | ok value =>
      rcases related with ⟨same, normal, unchanged, read⟩
      change sourcePost = source at same
      change targetPost = target at unchanged
      change flow = .normal at normal
      subst sourcePost
      subst targetPost
      subst flow
      obtain ⟨actual, otherRead, observedSame⟩ := observation
      cases target_atom_unique read otherRead
      subst observed
      simpa only [sourceObserve, clear] using observation_correspondence states value
  | error fault =>
      rcases related with ⟨same, returned, poisoned⟩
      change sourcePost = sourcePoison source fault at same
      change targetPost = targetPoison target fault at poisoned
      change flow = .returned default at returned
      subst sourcePost
      subst targetPost
      subst flow
      change observed = targetObserve (targetPoison target fault) default at observation
      subst observed
      simpa only [sourceFinish, sourceObserve, sourcePoison, clear, targetFinish, Except.map] using
        finish_correspondence states (.error fault) default

theorem guarded_related_has_observation {SourceWorld TargetWorld : Type} {interface : Interface}
    {default : TargetValue} {atom : Atom} {source : SourceState SourceWorld}
    {target : TargetState TargetWorld} {sourceOut : SourceOutcome SourceWorld}
    {out : TargetBlockOutcome TargetWorld}
    (related : GuardedEvaluationRelated interface default atom source target sourceOut out) :
    ∃ observed, targetExpressionObservation interface atom out observed := by
  rcases sourceOut with ⟨answer, sourcePost⟩
  rcases out with ⟨flow, frame, targetPost⟩
  cases answer with
  | ok value =>
      rcases related with ⟨_, normal, _, read⟩
      change flow = .normal at normal
      subst flow
      exact ⟨targetObserve targetPost (encodeValue value), encodeValue value, read, rfl⟩
  | error fault =>
      have returned : flow = .returned default := related.2.1
      subst flow
      exact ⟨targetObserve targetPost default, rfl⟩

/-- Complete observable preservation includes the actual emitted run and all post-state fields. -/
theorem guarded_expression_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    (tagged : SourceLocalsTagged sourceFrame source.memory)
    (result : NativeType) {default : TargetValue} (zero : TargetZero interface result default)
    (root : List Instruction) {expression : Expr} (guarded : SourceGuardedExpression expression)
    {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) expression supply = some output)
    (bounded : TemporaryNamesBound targetFrame supply.next) {sourceOut : SourceOutcome SourceWorld}
    (sourceRan : SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source sourceOut) :
    ∃ out observed,
      TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      targetExpressionObservation interface output.result out observed ∧
      GuardedTargetState default target out ∧ FrameRelated sourceFrame out.frame ∧
      TemporaryProtection supply.next targetFrame out.frame ∧ TemporaryNamesBound out.frame output.supply.next ∧
      OutcomeRelated worldRelated sourceOut observed := by
  obtain ⟨out, ran, related, protection, finalBounded⟩ := guarded_expression_run_preservation
    sourceHeap sourceCalls targetHeap targetCalls states clear tagged result zero root guarded
    compiled frames bounded sourceRan
  obtain ⟨observed, observation⟩ := guarded_related_has_observation related
  exact ⟨out, observed, ran, observation, (guarded_target_run_shape zero guarded compiled bounded ran).1,
    temporary_protection_preserves_source_frame frames protection, protection, finalBounded,
    guarded_related_observation_correspondence states clear related observation⟩

/-- Every observable target result reflects to the independent authored expression relation. -/
theorem guarded_expression_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    (tagged : SourceLocalsTagged sourceFrame source.memory)
    (result : NativeType) {default : TargetValue} (zero : TargetZero interface result default)
    (root : List Instruction) {expression : Expr} (guarded : SourceGuardedExpression expression)
    {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) expression supply = some output)
    (bounded : TemporaryNamesBound targetFrame supply.next)
    {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out)
    (observation : targetExpressionObservation interface output.result out observed) :
    ∃ sourceOut,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source sourceOut ∧
      GuardedTargetState default target out ∧ FrameRelated sourceFrame out.frame ∧
      TemporaryProtection supply.next targetFrame out.frame ∧ TemporaryNamesBound out.frame output.supply.next ∧
      OutcomeRelated worldRelated sourceOut observed := by
  obtain ⟨sourceOut, sourceRan, related⟩ := guarded_expression_run_reflection
    sourceHeap sourceCalls targetHeap targetCalls states clear tagged result zero root guarded
    compiled frames bounded ran
  obtain ⟨shape, protection, finalBounded⟩ := guarded_target_run_shape zero guarded compiled bounded ran
  exact ⟨sourceOut, sourceRan, shape, temporary_protection_preserves_source_frame frames protection,
    protection, finalBounded, guarded_related_observation_correspondence states clear related observation⟩

end Mettapedia.GSLT.LanguageDef.NativeOps
