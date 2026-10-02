import Mettapedia.GSLT.LanguageDef.NativeOpsShortCircuitTarget

/-!
# Composable source-to-target child evidence

Child evidence consists of laws for the independently defined source and
target relations, with actual successful compilation and exact state/frame
observations. The guarded factory below proves these laws; no evidence is
granted to an arbitrary heap operation or external call.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Atom)
open NativeLowering (Expression)

/-- Reusable child laws at a fixed source entry and actual evaluation interfaces. -/
structure ShortCircuitChildLaws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld)
    (result : NativeType) (default : TargetValue) (expression : Expr) : Prop where
  sourceState : ∀ {out : SourceOutcome SourceWorld},
    SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source out →
    SourceScalarResultState source out.result out.state
  sourceTag : ∀ {type : NativeType} {value : SourceValue},
    inferExpr interface (sourceFrameScope sourceFrame) expression = some type →
    SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source ⟨.ok value, source⟩ →
    SourceOuterTag type value
  bounds : ∀ {supply : NativeIR.Supply} {output : Expression},
    NativeLowering.expression? interface (sourceFrameScope sourceFrame) expression supply = some output →
    supply.next < output.supply.next ∧ atomWithin output.supply.next output.result
  forward : ∀ (root : List Instruction) {supply : NativeIR.Supply} {output : Expression}
      {targetFrame : TargetFrame} {target : TargetState TargetWorld},
    NativeLowering.expression? interface (sourceFrameScope sourceFrame) expression supply = some output →
    FrameRelated sourceFrame targetFrame → StateRelated worldRelated source target →
    TemporaryNamesBound targetFrame supply.next → TemporariesScoped targetFrame →
    ∀ {sourceOut : SourceOutcome SourceWorld},
    SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source sourceOut →
    ∃ out,
      TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      GuardedEvaluationRelated interface default output.result source target sourceOut out ∧
      TemporaryProtection supply.next targetFrame out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame
  backward : ∀ (root : List Instruction) {supply : NativeIR.Supply} {output : Expression}
      {targetFrame : TargetFrame} {target : TargetState TargetWorld},
    NativeLowering.expression? interface (sourceFrameScope sourceFrame) expression supply = some output →
    FrameRelated sourceFrame targetFrame → StateRelated worldRelated source target →
    TemporaryNamesBound targetFrame supply.next → TemporariesScoped targetFrame →
    ∀ {out : TargetBlockOutcome TargetWorld},
    TargetRun interface targetHeap targetCalls result root output.code targetFrame target out →
    ∃ sourceOut,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source sourceOut ∧
      GuardedEvaluationRelated interface default output.result source target sourceOut out ∧
      TemporaryProtection supply.next targetFrame out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame

theorem guarded_short_circuit_child_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld) (clear : source.fault = none)
    (tagged : SourceLocalsTagged sourceFrame source.memory)
    (result : NativeType) {default : TargetValue} (zero : TargetZero interface result default)
    {expression : Expr} (guarded : SourceGuardedExpression expression) :
    ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default expression := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro out ran
    exact source_guarded_run_state guarded source clear ran
  · intro type value typing ran
    exact source_guarded_success_tag guarded source clear tagged typing ran
  · intro supply output compiled
    exact ⟨(guarded_lowering_bounds guarded compiled).1, guarded_result_atom_within guarded compiled⟩
  · intro root supply output frame target compiled frames states bounded hscope sourceOut ran
    obtain ⟨out, targetRan, related, protection, finalBounded⟩ := guarded_expression_run_preservation
      sourceHeap sourceCalls targetHeap targetCalls states clear tagged result zero root guarded
      compiled frames bounded ran
    exact ⟨out, targetRan, related, protection, finalBounded,
      guarded_expression_run_scoped guarded compiled hscope targetRan⟩
  · intro root supply output frame target compiled frames states bounded hscope out ran
    obtain ⟨sourceOut, sourceRan, related⟩ := guarded_expression_run_reflection
      sourceHeap sourceCalls targetHeap targetCalls states clear tagged result zero root guarded
      compiled frames bounded ran
    have shape := guarded_target_run_shape zero guarded compiled bounded ran
    exact ⟨sourceOut, sourceRan, related, shape.2.1, shape.2.2,
      guarded_expression_run_scoped guarded compiled hscope ran⟩

theorem short_circuit_children_source_state {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {left right : Expr}
    (continueValue : Bool)
    (first : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default left)
    (second : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default right) {out : SourceOutcome SourceWorld}
    (ran : SourceExprEval interface sourceHeap sourceCalls sourceFrame
      (.binary (shortCircuitBinary continueValue) left right) source out) :
    SourceScalarResultState source out.result out.state := by
  rcases (source_short_circuit_exact continueValue left right source out).mp ran with
    ⟨after, leftRan, same⟩ | ⟨middle, leftRan, rightRan⟩ | ⟨fault, after, leftRan, same⟩
  · cases same
    exact first.sourceState leftRan
  · have unchanged : middle = source := first.sourceState leftRan
    subst middle
    exact second.sourceState rightRan
  · cases same
    exact first.sourceState leftRan

theorem short_circuit_children_source_tag {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {left right : Expr}
    (continueValue : Bool)
    (first : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default left)
    (second : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default right) {type : NativeType} {value : SourceValue}
    (typing : inferExpr interface (sourceFrameScope sourceFrame)
      (.binary (shortCircuitBinary continueValue) left right) = some type)
    (ran : SourceExprEval interface sourceHeap sourceCalls sourceFrame
      (.binary (shortCircuitBinary continueValue) left right) source ⟨.ok value, source⟩) :
    SourceOuterTag type value := by
  have types := short_circuit_inferred continueValue typing
  cases types.1
  rcases (source_short_circuit_exact continueValue left right source _).mp ran with
    ⟨after, leftRan, same⟩ | ⟨middle, leftRan, rightRan⟩ | ⟨fault, after, leftRan, impossible⟩
  · have exactValue : value = .bool (!continueValue) := Except.ok.inj (congrArg SourceOutcome.result same)
    cases exactValue
    constructor
  · have unchanged : middle = source := first.sourceState leftRan
    subst middle
    exact second.sourceTag types.2.2 rightRan
  · cases impossible

/-- Selected-arm preservation uses the proved right child, then the actual
assignment and lexical close. The copied left result is an outer private cell. -/
theorem short_circuit_taken_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {right : Expr}
    (continueValue : Bool)
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default right)
    {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) right supply = some output)
    {marker : TargetFrame} {target : TargetState TargetWorld}
    (frames : FrameRelated sourceFrame marker) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound marker supply.next) (hscope : TemporariesScoped marker)
    {lower identity : Nat} (fresh : lower < identity) (within : identity ≤ supply.next)
    (read : TargetAtomEval interface marker target (.temporary identity .bool) (.bool continueValue))
    (root : List Instruction) {sourceOut : SourceOutcome SourceWorld}
    (sourceRan : SourceExprEval interface sourceHeap sourceCalls sourceFrame right source sourceOut) :
    ∃ out,
      TargetRun interface targetHeap targetCalls result root
        [.branch (shortCircuitCondition continueValue (.temporary identity .bool))
          (output.code ++ [.assign (.temporary identity .bool) output.result]) []] marker target out ∧
      GuardedEvaluationRelated interface default (.temporary identity .bool) source target sourceOut out ∧
      TemporaryProtection lower marker out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  have live : marker.temporaryNames.contains identity = true := by cases read; assumption
  have checked := expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ output compiled
  have finalBounded := guarded_temporary_bound_mono bounded (Nat.le_of_lt (child.bounds compiled).1)
  obtain ⟨⟨flow, after, post⟩, ran, related, protection, _, _⟩ :=
    child.forward (output.code ++ [.assign (.temporary identity .bool) output.result])
      compiled frames states bounded hscope sourceRan
  rcases sourceOut with ⟨answer, sourcePost⟩
  cases answer with
  | ok value =>
      rcases related with ⟨sameSource, normal, sameTarget, resultRead⟩
      cases normal
      change post = target at sameTarget
      subst post
      have innerLive := (protection.names identity within).trans live
      let out := targetCloseBlock marker
        ⟨.normal, targetUpdateTemporary after identity (encodeValue value), target⟩
      refine ⟨out, ?_, ?_, ?_, close_block_temporary_bound finalBounded _, target_close_block_scoped marker _⟩
      · exact (target_short_circuit_taken_exact continueValue read output checked root out).mpr
          (.inl ⟨after, target, encodeValue value, ran, resultRead, innerLive, rfl⟩)
      · exact ⟨sameSource, rfl,
          target_close_block_state_no_locals (by exact protection.nextLocal),
          close_updated_temporary_read interface marker after target identity .bool (encodeValue value) live innerLive⟩
      · exact close_updated_temporary_protection hscope protection
          ((Nat.le_of_lt fresh).trans within) fresh (encodeValue value) target
  | error fault =>
      rcases related with ⟨sameSource, returned, sameTarget⟩
      cases returned
      change post = targetPoison target fault at sameTarget
      subst post
      let out := targetCloseBlock marker ⟨.returned default, after, targetPoison target fault⟩
      refine ⟨out, ?_, ?_, ?_, close_block_temporary_bound finalBounded _, target_close_block_scoped marker _⟩
      · exact (target_short_circuit_taken_exact continueValue read output checked root out).mpr
          (.inr ⟨default, after, targetPoison target fault, ran, rfl⟩)
      · exact ⟨sameSource, rfl, target_close_block_state_no_locals protection.nextLocal⟩
      · exact close_block_temporary_protection hscope
          (temporary_protection_weaken ((Nat.le_of_lt fresh).trans within) protection) (targetPoison target fault)

/-- Every actual selected-arm run reflects to the child evaluation; early
returns and assignment results cannot add another source outcome. -/
theorem short_circuit_taken_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {right : Expr}
    (continueValue : Bool)
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default right)
    {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) right supply = some output)
    {marker : TargetFrame} {target : TargetState TargetWorld}
    (frames : FrameRelated sourceFrame marker) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound marker supply.next) (hscope : TemporariesScoped marker)
    {lower identity : Nat} (fresh : lower < identity) (within : identity ≤ supply.next)
    (read : TargetAtomEval interface marker target (.temporary identity .bool) (.bool continueValue))
    (root : List Instruction) {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root
      [.branch (shortCircuitCondition continueValue (.temporary identity .bool))
        (output.code ++ [.assign (.temporary identity .bool) output.result]) []] marker target out) :
    ∃ sourceOut,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame right source sourceOut ∧
      GuardedEvaluationRelated interface default (.temporary identity .bool) source target sourceOut out ∧
      TemporaryProtection lower marker out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  have outerLive : marker.temporaryNames.contains identity = true := by cases read; assumption
  have checked := expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ output compiled
  have finalBounded := guarded_temporary_bound_mono bounded (Nat.le_of_lt (child.bounds compiled).1)
  rcases (target_short_circuit_taken_exact continueValue read output checked root out).mp ran with
    ⟨after, post, value, childRan, resultRead, innerLive, same⟩ |
    ⟨value, after, post, childRan, same⟩
  · obtain ⟨sourceOut, sourceRan, related, protection, _, _⟩ := child.backward
      (output.code ++ [.assign (.temporary identity .bool) output.result])
      compiled frames states bounded hscope childRan
    obtain ⟨sourceValue, exactSource, unchanged, actualRead⟩ := guarded_related_normal related rfl
    subst sourceOut
    change post = target at unchanged
    subst post
    cases target_atom_unique resultRead actualRead
    subst out
    refine ⟨⟨.ok sourceValue, source⟩, sourceRan, ?_, ?_,
      close_block_temporary_bound finalBounded _, target_close_block_scoped marker _⟩
    · exact ⟨rfl, rfl, target_close_block_state_no_locals (by exact protection.nextLocal),
        close_updated_temporary_read interface marker after target identity .bool (encodeValue sourceValue)
          outerLive innerLive⟩
    · exact close_updated_temporary_protection hscope protection
        ((Nat.le_of_lt fresh).trans within) fresh (encodeValue sourceValue) target
  · obtain ⟨sourceOut, sourceRan, related, protection, _, _⟩ := child.backward
      (output.code ++ [.assign (.temporary identity .bool) output.result])
      compiled frames states bounded hscope childRan
    obtain ⟨fault, exactSource, exactValue, poisoned⟩ := guarded_related_returned related rfl
    subst sourceOut
    subst value
    change post = targetPoison target fault at poisoned
    subst post
    subst out
    refine ⟨⟨.error fault, sourcePoison source fault⟩, sourceRan, ?_, ?_,
      close_block_temporary_bound finalBounded _, target_close_block_scoped marker _⟩
    · exact ⟨rfl, rfl, target_close_block_state_no_locals protection.nextLocal⟩
    · exact close_block_temporary_protection hscope
        (temporary_protection_weaken ((Nat.le_of_lt fresh).trans within) protection) (targetPoison target fault)

/-- A compiled boolean constructor preserves its actual source evaluation,
including an unexecuted right operand and both child refusal positions. -/
theorem short_circuit_children_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {left right : Expr}
    (continueValue : Bool)
    (first : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default left)
    (second : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default right)
    {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame)
      (.binary (shortCircuitBinary continueValue) left right) supply = some output)
    {before : TargetFrame} {target : TargetState TargetWorld}
    (frames : FrameRelated sourceFrame before) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound before supply.next) (hscope : TemporariesScoped before)
    (root : List Instruction) {sourceOut : SourceOutcome SourceWorld}
    (sourceRan : SourceExprEval interface sourceHeap sourceCalls sourceFrame
      (.binary (shortCircuitBinary continueValue) left right) source sourceOut) :
    ∃ out,
      TargetRun interface targetHeap targetCalls result root output.code before target out ∧
      GuardedEvaluationRelated interface default output.result source target sourceOut out ∧
      TemporaryProtection supply.next before out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  obtain ⟨leftOutput, rightOutput, _, _, leftCompiled, rightCompiled, same⟩ :=
    short_circuit_lowering_exact continueValue compiled
  subst output
  let identity := (NativeIR.fresh leftOutput.supply).1
  let copied := NativeLowering.pureTemporary leftOutput.supply .bool (.copy leftOutput.result)
  let branch := Instruction.branch (shortCircuitCondition continueValue copied.result)
    (rightOutput.code ++ [.assign (.temporary identity .bool) rightOutput.result]) []
  have leftChecked := expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ leftOutput leftCompiled
  have leftBounds := first.bounds leftCompiled
  have rightBounds := second.bounds rightCompiled
  have copyFresh : leftOutput.supply.next < identity := NativeIR.fresh_strict leftOutput.supply
  have originFresh : supply.next < identity := leftBounds.1.trans copyFresh
  rcases (source_short_circuit_exact continueValue left right source sourceOut).mp sourceRan with
    ⟨sourcePost, leftRan, sameOut⟩ | ⟨sourcePost, leftRan, rightRan⟩ |
    ⟨fault, sourcePost, leftRan, sameOut⟩
  · subst sourceOut
    have unchanged : sourcePost = source := first.sourceState leftRan
    subst sourcePost
    obtain ⟨⟨flow, middle, post⟩, leftTarget, leftRelated, leftProtection, middleBounded, middleScoped⟩ :=
      first.forward root leftCompiled frames states bounded hscope leftRan
    rcases leftRelated with ⟨_, normal, unchanged, leftRead⟩
    cases normal
    change post = target at unchanged
    subst post
    let marker := targetDeclareTemporary middle identity (.bool (!continueValue))
    have markerProtection := temporary_protection_trans leftProtection
      (declare_temporary_protects middle (.bool (!continueValue)) originFresh)
    have markerBounded : TemporaryNamesBound marker copied.supply.next :=
      declared_temporary_bound middleBounded (Nat.le_of_lt copyFresh) (Nat.le_refl identity) _
    have markerScoped := declared_temporaries_completeNames middleScoped identity (.bool (!continueValue))
    have copiedRead := declared_temporary_atom interface middle target identity .bool (.bool (!continueValue))
    have suffix : TargetRun interface targetHeap targetCalls result root
        (copied.code ++ [branch]) middle target ⟨.normal, marker, target⟩ := by
      apply (target_short_circuit_copy_exact
        (temporary_bound_fresh middleBounded copyFresh) leftRead root [branch] _).mpr
      exact (target_short_circuit_skip_exact continueValue markerScoped copiedRead _ root _).mpr rfl
    have ran := target_append_normal root leftOutput.code _ leftChecked leftTarget suffix
    refine ⟨⟨.normal, marker, target⟩, ?_, ⟨rfl, rfl, rfl, copiedRead⟩,
      markerProtection, guarded_temporary_bound_mono markerBounded (Nat.le_of_lt rightBounds.1), markerScoped⟩
    simpa only [shortCircuitOutput, List.append_assoc] using ran
  · have unchanged : sourcePost = source := first.sourceState leftRan
    subst sourcePost
    obtain ⟨⟨flow, middle, post⟩, leftTarget, leftRelated, leftProtection, middleBounded, middleScoped⟩ :=
      first.forward root leftCompiled frames states bounded hscope leftRan
    rcases leftRelated with ⟨_, normal, unchanged, leftRead⟩
    cases normal
    change post = target at unchanged
    subst post
    let marker := targetDeclareTemporary middle identity (.bool continueValue)
    have markerProtection := temporary_protection_trans leftProtection
      (declare_temporary_protects middle (.bool continueValue) originFresh)
    have markerBounded : TemporaryNamesBound marker copied.supply.next :=
      declared_temporary_bound middleBounded (Nat.le_of_lt copyFresh) (Nat.le_refl identity) _
    have markerScoped := declared_temporaries_completeNames middleScoped identity (.bool continueValue)
    have copiedRead := declared_temporary_atom interface middle target identity .bool (.bool continueValue)
    obtain ⟨out, branchRan, related, branchProtection, finalBounded, finalScoped⟩ :=
      short_circuit_taken_preservation continueValue second rightCompiled
        (temporary_protection_preserves_source_frame frames markerProtection) states markerBounded markerScoped
        originFresh (Nat.le_refl identity) copiedRead root rightRan
    have suffix : TargetRun interface targetHeap targetCalls result root
        (copied.code ++ [branch]) middle target out :=
      (target_short_circuit_copy_exact (temporary_bound_fresh middleBounded copyFresh)
        leftRead root [branch] out).mpr branchRan
    have ran := target_append_normal root leftOutput.code _ leftChecked leftTarget suffix
    refine ⟨out, ?_, related, temporary_protection_trans markerProtection branchProtection,
      finalBounded, finalScoped⟩
    simpa only [shortCircuitOutput, List.append_assoc] using ran
  · subst sourceOut
    obtain ⟨⟨flow, after, post⟩, leftTarget, related, protection, finalBounded, finalScoped⟩ :=
      first.forward root leftCompiled frames states bounded hscope leftRan
    rcases related with ⟨sameSource, returned, poisoned⟩
    cases returned
    change post = targetPoison target fault at poisoned
    subst post
    have ran := target_append_returned root leftOutput.code (copied.code ++ [branch]) leftChecked leftTarget
    refine ⟨⟨.returned default, after, targetPoison target fault⟩, ?_,
      ⟨sameSource, rfl, rfl⟩, protection, ?_, finalScoped⟩
    · simpa only [shortCircuitOutput, List.append_assoc] using ran
    · exact guarded_temporary_bound_mono finalBounded
        ((Nat.le_of_lt copyFresh).trans (Nat.le_of_lt rightBounds.1))

/-- Every actual compiled constructor run reflects to the source connective.
The prefix split fixes whether the copy and selected arm were reached. -/
theorem short_circuit_children_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {left right : Expr}
    (continueValue : Bool)
    (first : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default left)
    (second : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default right)
    {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame)
      (.binary (shortCircuitBinary continueValue) left right) supply = some output)
    {before : TargetFrame} {target : TargetState TargetWorld}
    (frames : FrameRelated sourceFrame before) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound before supply.next) (hscope : TemporariesScoped before)
    (root : List Instruction) {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code before target out) :
    ∃ sourceOut,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame
        (.binary (shortCircuitBinary continueValue) left right) source sourceOut ∧
      GuardedEvaluationRelated interface default output.result source target sourceOut out ∧
      TemporaryProtection supply.next before out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  obtain ⟨leftOutput, rightOutput, leftTyping, _, leftCompiled, rightCompiled, same⟩ :=
    short_circuit_lowering_exact continueValue compiled
  subst output
  let identity := (NativeIR.fresh leftOutput.supply).1
  let copied := NativeLowering.pureTemporary leftOutput.supply .bool (.copy leftOutput.result)
  let branch := Instruction.branch (shortCircuitCondition continueValue copied.result)
    (rightOutput.code ++ [.assign (.temporary identity .bool) rightOutput.result]) []
  have leftChecked := expression_lowering_jump_free interface (sourceFrameScope sourceFrame) _ _ leftOutput leftCompiled
  have leftBounds := first.bounds leftCompiled
  have rightBounds := second.bounds rightCompiled
  have copyFresh : leftOutput.supply.next < identity := NativeIR.fresh_strict leftOutput.supply
  have originFresh : supply.next < identity := leftBounds.1.trans copyFresh
  have ordered : TargetRun interface targetHeap targetCalls result root
      (leftOutput.code ++ (copied.code ++ [branch])) before target out := by
    simpa only [shortCircuitOutput, List.append_assoc] using ran
  rcases target_split_jump_free_prefix root leftOutput.code _ leftChecked ordered with
    ⟨middle, post, leftTarget, suffix⟩ | ⟨value, after, post, leftTarget, sameOut⟩
  · obtain ⟨leftSourceOut, leftSource, leftRelated, leftProtection, middleBounded, middleScoped⟩ :=
      first.backward root leftCompiled frames states bounded hscope leftTarget
    obtain ⟨leftValue, exactLeft, unchanged, leftRead⟩ := guarded_related_normal leftRelated rfl
    subst leftSourceOut
    change post = target at unchanged
    subst post
    have tag := first.sourceTag leftTyping leftSource
    cases tag with
    | bool boolean =>
        let marker := targetDeclareTemporary middle identity (.bool boolean)
        have markerProtection := temporary_protection_trans leftProtection
          (declare_temporary_protects middle (.bool boolean) originFresh)
        have markerBounded : TemporaryNamesBound marker copied.supply.next :=
          declared_temporary_bound middleBounded (Nat.le_of_lt copyFresh) (Nat.le_refl identity) _
        have markerScoped := declared_temporaries_completeNames middleScoped identity (.bool boolean)
        have copiedRead := declared_temporary_atom interface middle target identity .bool (.bool boolean)
        have branchRan := (target_short_circuit_copy_exact (temporary_bound_fresh middleBounded copyFresh)
          leftRead root [branch] out).mp suffix
        by_cases selected : boolean = continueValue
        · subst boolean
          obtain ⟨sourceOut, sourceRan, related, branchProtection, finalBounded, finalScoped⟩ :=
            short_circuit_taken_reflection continueValue second rightCompiled
              (temporary_protection_preserves_source_frame frames markerProtection) states markerBounded markerScoped
              originFresh (Nat.le_refl identity) copiedRead root branchRan
          exact ⟨sourceOut, source_short_circuit_taken continueValue leftSource sourceRan,
            related, temporary_protection_trans markerProtection branchProtection, finalBounded, finalScoped⟩
        · have skipped : boolean = !continueValue := by
            cases boolean <;> cases continueValue
            · exact False.elim (selected rfl)
            · rfl
            · rfl
            · exact False.elim (selected rfl)
          subst boolean
          have sameOut := (target_short_circuit_skip_exact continueValue markerScoped copiedRead _ root out).mp branchRan
          subst out
          exact ⟨⟨.ok (.bool (!continueValue)), source⟩, source_short_circuit_skip continueValue leftSource,
            ⟨rfl, rfl, rfl, copiedRead⟩, markerProtection,
            guarded_temporary_bound_mono markerBounded (Nat.le_of_lt rightBounds.1), markerScoped⟩
  · obtain ⟨sourceOut, sourceRan, related, protection, finalBounded, finalScoped⟩ :=
      first.backward root leftCompiled frames states bounded hscope leftTarget
    obtain ⟨fault, exactSource, exactValue, poisoned⟩ := guarded_related_returned related rfl
    subst sourceOut
    subst value
    change post = targetPoison target fault at poisoned
    subst post
    subst out
    exact ⟨⟨.error fault, sourcePoison source fault⟩,
      source_short_circuit_left_fault continueValue sourceRan, ⟨rfl, rfl, rfl⟩,
      protection, guarded_temporary_bound_mono finalBounded
        ((Nat.le_of_lt copyFresh).trans (Nat.le_of_lt rightBounds.1)), finalScoped⟩

/-- The constructor laws compose actual child proofs; they grant no laws to
unproved memory or effectful call expressions. -/
theorem short_circuit_child_laws {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {left right : Expr}
    (continueValue : Bool)
    (first : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default left)
    (second : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default right) :
    ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.binary (shortCircuitBinary continueValue) left right) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro out ran
    exact short_circuit_children_source_state continueValue first second ran
  · intro type value typing ran
    exact short_circuit_children_source_tag continueValue first second typing ran
  · intro supply output compiled
    obtain ⟨leftOutput, rightOutput, _, _, leftCompiled, rightCompiled, same⟩ :=
      short_circuit_lowering_exact continueValue compiled
    subst output
    have leftBounds := first.bounds leftCompiled
    have rightBounds := second.bounds rightCompiled
    have copied : leftOutput.supply.next <
        (NativeLowering.pureTemporary leftOutput.supply .bool (.copy leftOutput.result)).supply.next :=
      NativeIR.fresh_strict leftOutput.supply
    exact ⟨leftBounds.1.trans (copied.trans rightBounds.1), Nat.le_of_lt rightBounds.1⟩
  · intro root supply output frame target compiled frames states bounded hscope sourceOut ran
    exact short_circuit_children_preservation continueValue first second compiled frames states bounded hscope root ran
  · intro root supply output frame target compiled frames states bounded hscope out ran
    exact short_circuit_children_reflection continueValue first second compiled frames states bounded hscope root ran

/-- Recursive evidence covers nested boolean branches over the independently
proved guarded family, with no target execution premise. -/
theorem short_circuit_expression_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld) (clear : source.fault = none)
    (tagged : SourceLocalsTagged sourceFrame source.memory)
    (result : NativeType) {default : TargetValue} (zero : TargetZero interface result default)
    {expression : Expr} (supported : SourceShortCircuitExpression expression) :
    ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default expression := by
  induction supported with
  | guarded child =>
      exact guarded_short_circuit_child_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
        sourceFrame source clear tagged result zero child
  | connect continueValue first second firstIH secondIH =>
      exact short_circuit_child_laws continueValue firstIH secondIH

theorem child_related_target_shape {SourceWorld TargetWorld : Type} {interface : Interface}
    {default : TargetValue} {atom : Atom} {source : SourceState SourceWorld}
    {target : TargetState TargetWorld} {sourceOut : SourceOutcome SourceWorld}
    {out : TargetBlockOutcome TargetWorld}
    (related : GuardedEvaluationRelated interface default atom source target sourceOut out) :
    GuardedTargetState default target out := by
  rcases sourceOut with ⟨answer, post⟩
  cases answer with
  | ok value => exact .inl ⟨related.2.1, related.2.2.1⟩
  | error fault => exact .inr ⟨fault, related.2.1, related.2.2⟩

/-- Observable preservation executes the actual emitted branches and retains
complete runtime state, caller-visible frame and prior private values. -/
theorem short_circuit_expression_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    (tagged : SourceLocalsTagged sourceFrame source.memory)
    (result : NativeType) {default : TargetValue} (zero : TargetZero interface result default)
    (root : List Instruction) {expression : Expr} (supported : SourceShortCircuitExpression expression)
    {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) expression supply = some output)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceOutcome SourceWorld}
    (sourceRan : SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source sourceOut) :
    ∃ out observed,
      TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      targetExpressionObservation interface output.result out observed ∧
      GuardedTargetState default target out ∧ FrameRelated sourceFrame out.frame ∧
      TemporaryProtection supply.next targetFrame out.frame ∧ TemporaryNamesBound out.frame output.supply.next ∧
      TemporariesScoped out.frame ∧ OutcomeRelated worldRelated sourceOut observed := by
  have laws := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
    sourceFrame source clear tagged result zero supported
  obtain ⟨out, ran, related, protection, finalBounded, finalScoped⟩ :=
    laws.forward root compiled frames states bounded hscope sourceRan
  obtain ⟨observed, observation⟩ := guarded_related_has_observation related
  exact ⟨out, observed, ran, observation, child_related_target_shape related,
    temporary_protection_preserves_source_frame frames protection, protection, finalBounded, finalScoped,
    guarded_related_observation_correspondence states clear related observation⟩

/-- Observable reflection excludes additional target values and faults while
retaining the exact post-state and lexical private-map discipline. -/
theorem short_circuit_expression_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    (tagged : SourceLocalsTagged sourceFrame source.memory)
    (result : NativeType) {default : TargetValue} (zero : TargetZero interface result default)
    (root : List Instruction) {expression : Expr} (supported : SourceShortCircuitExpression expression)
    {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) expression supply = some output)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out)
    (observation : targetExpressionObservation interface output.result out observed) :
    ∃ sourceOut,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source sourceOut ∧
      GuardedTargetState default target out ∧ FrameRelated sourceFrame out.frame ∧
      TemporaryProtection supply.next targetFrame out.frame ∧ TemporaryNamesBound out.frame output.supply.next ∧
      TemporariesScoped out.frame ∧ OutcomeRelated worldRelated sourceOut observed := by
  have laws := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
    sourceFrame source clear tagged result zero supported
  obtain ⟨sourceOut, sourceRan, related, protection, finalBounded, finalScoped⟩ :=
    laws.backward root compiled frames states bounded hscope ran
  exact ⟨sourceOut, sourceRan, child_related_target_shape related,
    temporary_protection_preserves_source_frame frames protection, protection, finalBounded, finalScoped,
    guarded_related_observation_correspondence states clear related observation⟩

end Mettapedia.GSLT.LanguageDef.NativeOps
