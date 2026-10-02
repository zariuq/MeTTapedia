import Mettapedia.GSLT.LanguageDef.NativeOpsReferenceFieldLowering

/-!
# Reference-field expression correspondence

The base expression is evaluated by the existing child lowering. The field
location and contents then use the emitted reference guard, address and load.
Both directions retain the exact first fault and whole memory state; a nominal
reference type does not assert a tag for the value read from its storage.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Atom Instruction)
open NativeLowering (Expression)

theorem reference_field_child_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {reference : Expr} {record member : String}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default reference) (clear : source.fault = none)
    (baseType : inferExpr interface (sourceFrameScope sourceFrame) reference = some (.ref (.named record)))
    (zero : TargetZero interface result default)
    (root : List Instruction) {supply : NativeIR.Supply} {output : Expression}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.field reference member)
      supply = some output) (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceOutcome SourceWorld}
    (ran : SourceExprEval interface sourceHeap sourceCalls sourceFrame (.field reference member) source sourceOut) :
    ∃ out observed, TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      targetExpressionObservation interface output.result out observed ∧ OutcomeRelated worldRelated sourceOut observed := by
  obtain ⟨type, first, index, _, firstCompiled, position, same⟩ := reference_field_combined_lowering_exact baseType compiled
  subst output
  have next := NativeIR.fresh_strict first.supply
  have nextValue := NativeIR.fresh_strict (NativeIR.fresh first.supply).2
  have distinct : (NativeIR.fresh (NativeIR.fresh first.supply).2).1 ≠ (NativeIR.fresh first.supply).1 := by
    exact Nat.ne_of_gt nextValue
  have jumpFree := expression_lowering_jump_free interface (sourceFrameScope sourceFrame)
    reference supply first firstCompiled
  rcases (source_read_operand_exact child rfl sourceOut).mp ran with
    ⟨value, sourceRan, primitive⟩ | ⟨fault, sourceRan, same⟩
  · have tag := child.sourceTag baseType sourceRan
    cases tag with
    | reference element pointer =>
        obtain ⟨⟨flow, middle, post⟩, firstRan, related, _, middleBounded, _⟩ :=
          child.forward root firstCompiled frames states bounded hscope sourceRan
        rcases related with ⟨_, normal, unchanged, read⟩
        cases normal
        change post = target at unchanged
        subst post
        obtain ⟨out, observed, tail, observation, outcome⟩ := checked_reference_field_preservation
          states sourceHeap sourceCalls targetHeap targetCalls sourceFrame middle reference pointer
          record member index (NativeIR.fresh first.supply).1 (NativeIR.fresh (NativeIR.fresh first.supply).2).1
          type result baseType position first.result read
          (temporary_bound_fresh middleBounded next) (temporary_bound_fresh middleBounded (next.trans nextValue))
          distinct zero root primitive
        have all := target_append_normal root _ _ jumpFree firstRan tail
        exact ⟨out, observed, by simpa only [NativeLowering.prependCode, NativeLowering.pureTemporary,
          List.append_assoc, List.cons_append, List.nil_append] using all, observation, outcome⟩
  · subst sourceOut
    obtain ⟨⟨flow, after, post⟩, firstRan, related, _, _, _⟩ :=
      child.forward root firstCompiled frames states bounded hscope sourceRan
    rcases related with ⟨_, returned, poisoned⟩
    cases returned
    change post = targetPoison target fault at poisoned
    subst post
    have all := target_append_returned root _
      (NativeLowering.checkReference first.result ++
        [.temporary (NativeIR.fresh first.supply).1 (.ref type) (.fieldAddress first.result record index)] ++
        (NativeLowering.pureTemporary (NativeIR.fresh first.supply).2 type
          (.indirectRead (.temporary (NativeIR.fresh first.supply).1 (.ref type)))).code)
      jumpFree firstRan
    have wholeRelated : GuardedEvaluationRelated interface default
        (NativeLowering.pureTemporary (NativeIR.fresh first.supply).2 type
          (.indirectRead (.temporary (NativeIR.fresh first.supply).1 (.ref type)))).result source target
        ⟨.error fault, sourcePoison source fault⟩
        ⟨.returned default, after, targetPoison target fault⟩ := ⟨rfl, rfl, rfl⟩
    obtain ⟨observed, observation⟩ := guarded_related_has_observation wholeRelated
    have outcome := guarded_related_observation_correspondence states clear wholeRelated observation
    exact ⟨⟨.returned default, after, targetPoison target fault⟩, observed,
      by simpa only [NativeLowering.prependCode, List.append_assoc, List.cons_append, List.nil_append] using all, observation, outcome⟩

theorem reference_field_child_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {reference : Expr} {record member : String}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default reference) (clear : source.fault = none)
    (baseType : inferExpr interface (sourceFrameScope sourceFrame) reference = some (.ref (.named record)))
    (zero : TargetZero interface result default)
    (root : List Instruction) {supply : NativeIR.Supply} {output : Expression}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.field reference member)
      supply = some output) (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out)
    (observation : targetExpressionObservation interface output.result out observed) :
    ∃ sourceOut, SourceExprEval interface sourceHeap sourceCalls sourceFrame (.field reference member) source sourceOut ∧
      OutcomeRelated worldRelated sourceOut observed := by
  obtain ⟨type, first, index, _, firstCompiled, position, same⟩ := reference_field_combined_lowering_exact baseType compiled
  subst output
  have next := NativeIR.fresh_strict first.supply
  have nextValue := NativeIR.fresh_strict (NativeIR.fresh first.supply).2
  have distinct : (NativeIR.fresh (NativeIR.fresh first.supply).2).1 ≠ (NativeIR.fresh first.supply).1 := by
    exact Nat.ne_of_gt nextValue
  have jumpFree := expression_lowering_jump_free interface (sourceFrameScope sourceFrame)
    reference supply first firstCompiled
  have all : TargetRun interface targetHeap targetCalls result root
      (first.code ++ NativeLowering.checkReference first.result ++
        [.temporary (NativeIR.fresh first.supply).1 (.ref type) (.fieldAddress first.result record index)] ++
        (NativeLowering.pureTemporary (NativeIR.fresh first.supply).2 type
          (.indirectRead (.temporary (NativeIR.fresh first.supply).1 (.ref type)))).code)
      targetFrame target out := ran
  simp only [List.append_assoc, List.cons_append, List.nil_append] at all
  rcases target_split_jump_free_prefix root first.code _ jumpFree all with
    ⟨middle, post, firstRan, tail⟩ | ⟨value, after, post, firstRan, same⟩
  · obtain ⟨sourceOut, sourceRan, related, _, middleBounded, _⟩ :=
      child.backward root firstCompiled frames states bounded hscope firstRan
    obtain ⟨value, sameSource, unchanged, read⟩ := guarded_related_normal related rfl
    cases sameSource
    change post = target at unchanged
    subst post
    have tag := child.sourceTag baseType sourceRan
    cases tag with
    | reference element pointer =>
        obtain ⟨sourceOut, primitive, outcome⟩ := checked_reference_field_reflection
          states sourceHeap sourceCalls targetHeap targetCalls sourceFrame middle reference pointer
          record member index (NativeIR.fresh first.supply).1 (NativeIR.fresh (NativeIR.fresh first.supply).2).1
          type result baseType position first.result read
          (temporary_bound_fresh middleBounded next) (temporary_bound_fresh middleBounded (next.trans nextValue))
          distinct zero root tail observation
        exact ⟨sourceOut, (source_read_operand_exact child rfl _).mpr
          (.inl ⟨.reference pointer, sourceRan, primitive⟩), outcome⟩
  · obtain ⟨sourceOut, sourceRan, related, _, _, _⟩ :=
      child.backward root firstCompiled frames states bounded hscope firstRan
    obtain ⟨fault, sameSource, exactDefault, exactState⟩ := guarded_related_returned related rfl
    cases sameSource
    subst value
    change post = targetPoison target fault at exactState
    subst post
    subst out
    have wholeRelated : GuardedEvaluationRelated interface default
        (NativeLowering.pureTemporary (NativeIR.fresh first.supply).2 type
          (.indirectRead (.temporary (NativeIR.fresh first.supply).1 (.ref type)))).result source target
        ⟨.error fault, sourcePoison source fault⟩
        ⟨.returned default, after, targetPoison target fault⟩ := ⟨rfl, rfl, rfl⟩
    exact ⟨⟨.error fault, sourcePoison source fault⟩,
      (source_read_operand_exact child rfl _).mpr (.inr ⟨fault, sourceRan, rfl⟩),
      guarded_related_observation_correspondence states clear wholeRelated observation⟩

theorem guarded_reference_field_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    {result : NativeType} {default : TargetValue} (zero : TargetZero interface result default)
    {reference : Expr} {record member : String} (guarded : SourceGuardedExpression reference)
    (baseType : inferExpr interface (sourceFrameScope sourceFrame) reference = some (.ref (.named record)))
    (root : List Instruction) {supply : NativeIR.Supply} {output : Expression}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.field reference member)
      supply = some output) (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceOutcome SourceWorld}
    (ran : SourceExprEval interface sourceHeap sourceCalls sourceFrame (.field reference member) source sourceOut) :
    ∃ out observed, TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      targetExpressionObservation interface output.result out observed ∧ OutcomeRelated worldRelated sourceOut observed :=
  reference_field_child_preservation (guarded_short_circuit_child_laws worldRelated interface sourceHeap sourceCalls
    targetHeap targetCalls sourceFrame source clear tagged result zero guarded)
    clear baseType zero root compiled frames states bounded hscope ran

theorem guarded_reference_field_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    {result : NativeType} {default : TargetValue} (zero : TargetZero interface result default)
    {reference : Expr} {record member : String} (guarded : SourceGuardedExpression reference)
    (baseType : inferExpr interface (sourceFrameScope sourceFrame) reference = some (.ref (.named record)))
    (root : List Instruction) {supply : NativeIR.Supply} {output : Expression}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.field reference member)
      supply = some output) (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out)
    (observation : targetExpressionObservation interface output.result out observed) :
    ∃ sourceOut, SourceExprEval interface sourceHeap sourceCalls sourceFrame (.field reference member) source sourceOut ∧
      OutcomeRelated worldRelated sourceOut observed :=
  reference_field_child_reflection (guarded_short_circuit_child_laws worldRelated interface sourceHeap sourceCalls
    targetHeap targetCalls sourceFrame source clear tagged result zero guarded)
    clear baseType zero root compiled frames states bounded hscope ran observation

end Mettapedia.GSLT.LanguageDef.NativeOps
