import Mettapedia.GSLT.LanguageDef.NativeOpsReferenceFieldProfiles

/-!
# Composable reference-field child laws

Read results are typed only by a separately established fact about the actual
source memory. Frame preservation and both execution directions come from the
existing lowerer and execution relations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Atom)
open NativeLowering (Expression)

theorem reference_field_child_strong_reflection {SourceWorld TargetWorld : Type}
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
    {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out)
    :
    ∃ sourceOut, SourceExprEval interface sourceHeap sourceCalls sourceFrame (.field reference member) source sourceOut ∧
      GuardedEvaluationRelated interface default output.result source target sourceOut out ∧
      TemporaryProtection supply.next targetFrame out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  obtain ⟨type, first, index, _, firstCompiled, position, same⟩ := reference_field_combined_lowering_exact baseType compiled
  subst output
  have next := NativeIR.fresh_strict first.supply
  have nextValue := NativeIR.fresh_strict (NativeIR.fresh first.supply).2
  have distinct : (NativeIR.fresh (NativeIR.fresh first.supply).2).1 ≠ (NativeIR.fresh first.supply).1 := by
    exact Nat.ne_of_gt nextValue
  have advance := (child.bounds firstCompiled).1
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
  · obtain ⟨sourceOut, sourceRan, related, protection, middleBounded, middleScoped⟩ :=
      child.backward root firstCompiled frames states bounded hscope firstRan
    obtain ⟨value, sameSource, unchanged, read⟩ := guarded_related_normal related rfl
    cases sameSource
    change post = target at unchanged
    subst post
    have tag := child.sourceTag baseType sourceRan
    cases tag with
    | reference element pointer =>
        obtain ⟨sourceOut, primitive, agreement⟩ := target_reference_field_guarded
          states clear sourceHeap sourceCalls sourceFrame middle reference pointer
          record member index (NativeIR.fresh first.supply).1 (NativeIR.fresh (NativeIR.fresh first.supply).2).1
          type result baseType position first.result read
          (temporary_bound_fresh middleBounded next) (temporary_bound_fresh middleBounded (next.trans nextValue))
          distinct zero root tail
        obtain ⟨tailProtection, finalBounded, finalScoped⟩ := target_reference_field_frame states zero read
          record index type first.supply middleBounded middleScoped root tail
        exact ⟨sourceOut, (source_read_operand_exact child rfl _).mpr
          (.inl ⟨.reference pointer, sourceRan, primitive⟩), agreement,
          temporary_protection_trans protection (temporary_protection_weaken (Nat.le_of_lt advance) tailProtection),
          finalBounded, finalScoped⟩
  · obtain ⟨sourceOut, sourceRan, related, protection, afterBounded, afterScoped⟩ :=
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
      wholeRelated, protection,
      guarded_temporary_bound_mono afterBounded (Nat.le_of_lt (next.trans nextValue)), afterScoped⟩

theorem reference_field_child_strong_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {base : Expr} {record member : String}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default base) (clear : source.fault = none)
    (baseType : inferExpr interface (sourceFrameScope sourceFrame) base = some (.ref (.named record)))
    (zero : TargetZero interface result default)
    (root : List Instruction) {supply : NativeIR.Supply} {output : Expression}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.field base member)
      supply = some output) (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceOutcome SourceWorld}
    (ran : SourceExprEval interface sourceHeap sourceCalls sourceFrame (.field base member) source sourceOut) :
    ∃ out, TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      GuardedEvaluationRelated interface default output.result source target sourceOut out ∧
      TemporaryProtection supply.next targetFrame out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  obtain ⟨out, observed, targetRan, observation, outcome⟩ := reference_field_child_preservation child
    clear baseType zero root compiled frames states bounded hscope ran
  obtain ⟨reflected, reflectedRan, agreement, protection, finalBounded, finalScoped⟩ :=
    reference_field_child_strong_reflection child clear baseType zero root compiled frames states bounded hscope targetRan
  have reflectedOutcome := guarded_related_observation_correspondence states clear agreement observation
  obtain ⟨type, first, index, _, _, position, _⟩ := reference_field_combined_lowering_exact baseType compiled
  have same := source_scalar_outcome_equal
    (reference_field_child_source_state child baseType clear position ran)
    (reference_field_child_source_state child baseType clear position reflectedRan)
    (outcome.result.symm.trans reflectedOutcome.result)
  cases same
  exact ⟨out, targetRan, agreement, protection, finalBounded, finalScoped⟩

theorem reference_field_child_source_tag {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {base : Expr} {record member : String}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default base) (clear : source.fault = none)
    (baseType : inferExpr interface (sourceFrameScope sourceFrame) base = some (.ref (.named record)))
    {index : Nat} (position : NativeLowering.fieldLayout? interface record member = some index)
    (contentsTagged : ∀ {type : NativeType} {address : Address} {value : SourceValue},
      inferExpr interface (sourceFrameScope sourceFrame) (.field base member) = some type →
      SourceExprEval interface sourceHeap sourceCalls sourceFrame base source
        ⟨.ok (.reference (some address)), source⟩ →
      sourceRead source.memory (sourceFieldAddress address index) = some value → SourceOuterTag type value)
    {type : NativeType} {value : SourceValue}
    (typing : inferExpr interface (sourceFrameScope sourceFrame) (.field base member) = some type)
    (ran : SourceExprEval interface sourceHeap sourceCalls sourceFrame (.field base member) source
      ⟨.ok value, source⟩) : SourceOuterTag type value := by
  rcases (source_read_operand_exact child rfl _).mp ran with
    ⟨first, firstRan, primitive⟩ | ⟨fault, _, impossible⟩
  · have tag := child.sourceTag baseType firstRan
    cases tag with
    | reference element pointer =>
        have exactSource := (source_reference_field_primitive_exact sourceHeap sourceCalls sourceFrame
          base record member index pointer baseType position source _).mp primitive
        cases failed : (sourceReferenceCall source pointer).state.fault with
        | some fault => rw [failed] at exactSource; cases exactSource
        | none =>
            rw [failed] at exactSource
            obtain ⟨address, actual, pointed, loaded, same⟩ := exactSource
            have actualValue : value = actual := Except.ok.inj (congrArg SourceOutcome.result same)
            subst actual
            subst pointer
            have unchanged := source_reference_state_shape source (some address) clear
            rw [failed] at unchanged
            rw [unchanged] at loaded
            exact contentsTagged typing firstRan loaded
  · cases impossible

theorem reference_field_child_laws {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {base : Expr} {record member : String}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default base) (clear : source.fault = none)
    (baseType : inferExpr interface (sourceFrameScope sourceFrame) base = some (.ref (.named record)))
    (zero : TargetZero interface result default)
    {index : Nat} (position : NativeLowering.fieldLayout? interface record member = some index)
    (contentsTagged : ∀ {type : NativeType} {address : Address} {value : SourceValue},
      inferExpr interface (sourceFrameScope sourceFrame) (.field base member) = some type →
      SourceExprEval interface sourceHeap sourceCalls sourceFrame base source
        ⟨.ok (.reference (some address)), source⟩ →
      sourceRead source.memory (sourceFieldAddress address index) = some value → SourceOuterTag type value) :
    ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.field base member) :=
  ⟨reference_field_child_source_state child baseType clear position,
    reference_field_child_source_tag child clear baseType position contentsTagged,
    reference_field_child_bounds child baseType,
    reference_field_child_strong_preservation child clear baseType zero,
    reference_field_child_strong_reflection child clear baseType zero⟩

/-- Primitive field reads use the state left by the reference computation. -/
theorem stateful_reference_field_primitive_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld)
    (result : NativeType) (default : TargetValue) (zero : TargetZero interface result default)
    (reference : Expr) (record member : String) (index : Nat) (type : NativeType)
    (baseType : inferExpr interface (sourceFrameScope sourceFrame) reference = some (.ref (.named record)))
    (position : NativeLowering.fieldLayout? interface record member = some index)
    (tagged : ∀ before post value,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame reference before ⟨.ok value, post⟩ →
      SourceOuterTag (.ref (.named record)) value)
    (child : NativeLowering.Expression) :
    StatefulPrimitiveLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.field reference member) [reference]
      ⟨child.code, [child.result], child.supply⟩
      (NativeLowering.prependCode
        (NativeLowering.checkReference child.result ++
          [.temporary (NativeIR.fresh child.supply).1 (.ref type) (.fieldAddress child.result record index)])
        (NativeLowering.pureTemporary (NativeIR.fresh child.supply).2 type
          (.indirectRead (.temporary (NativeIR.fresh child.supply).1 (.ref type))))) := by
  have next := NativeIR.fresh_strict child.supply
  have nextValue := NativeIR.fresh_strict (NativeIR.fresh child.supply).2
  refine ⟨⟨(next.trans nextValue).le, Nat.le_refl _⟩, ?_, ?_⟩
  · intro root values middle argsRan middleClear frame target _ states bounded hscope reads sourceOut primitiveRan
    obtain ⟨value, same, read⟩ := target_one_encoded_argument reads
    subst values
    have childRan := (source_single_argument_success_exact reference source middle value).mp argsRan
    cases tagged source middle value childRan with
    | reference element pointer =>
        obtain ⟨out, _, targetRan, _, _⟩ := checked_reference_field_preservation states
          sourceHeap sourceCalls targetHeap targetCalls sourceFrame frame reference pointer record member index
          (NativeIR.fresh child.supply).1 (NativeIR.fresh (NativeIR.fresh child.supply).2).1 type result
          baseType position child.result read (temporary_bound_fresh bounded next)
          (temporary_bound_fresh bounded (next.trans nextValue)) (Nat.ne_of_gt nextValue) zero root primitiveRan
        obtain ⟨reflected, reflectedRan, checked, protection, finalBounded, finalScoped⟩ :=
          stateful_checked_reference_field_fragment_profile states middleClear sourceHeap sourceCalls
            sourceFrame frame reference pointer record member index type result baseType position
            child.result child.supply read bounded hscope zero root targetRan
        cases source_reference_field_primitive_unique baseType position primitiveRan reflectedRan
        exact ⟨out, targetRan, checked, protection, finalBounded, finalScoped⟩
  · intro root values middle argsRan middleClear frame target _ states bounded hscope reads out ran
    obtain ⟨value, same, read⟩ := target_one_encoded_argument reads
    subst values
    have childRan := (source_single_argument_success_exact reference source middle value).mp argsRan
    cases tagged source middle value childRan with
    | reference element pointer =>
        exact stateful_checked_reference_field_fragment_profile states middleClear sourceHeap sourceCalls
          sourceFrame frame reference pointer record member index type result baseType position
          child.result child.supply read bounded hscope zero root ran

/-- Stateful argument lowering composes with the guarded field-read suffix. -/
theorem stateful_reference_field_child_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld) (clear : source.fault = none)
    (result : NativeType) (default : TargetValue) (zero : TargetZero interface result default)
    (reference : Expr) (record member : String)
    (baseType : inferExpr interface (sourceFrameScope sourceFrame) reference = some (.ref (.named record)))
    (children : ∀ before, before.fault = none →
      StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
        sourceFrame before result default reference)
    (tagged : ∀ before post value,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame reference before ⟨.ok value, post⟩ →
      SourceOuterTag (.ref (.named record)) value) :
    StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.field reference member) := by
  apply stateful_strict_child_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
    sourceFrame source clear result default (.field reference member) [reference] rfl
    (fun child member before ready => by cases List.mem_singleton.mp member; exact children before ready)
  intro supply output compiled
  obtain ⟨type, child, index, _, childCompiled, position, same⟩ :=
    reference_field_combined_lowering_exact baseType compiled
  refine ⟨⟨child.code, [child.result], child.supply⟩,
    NativeLowering.prependCode
      (NativeLowering.checkReference child.result ++
        [.temporary (NativeIR.fresh child.supply).1 (.ref type) (.fieldAddress child.result record index)])
      (NativeLowering.pureTemporary (NativeIR.fresh child.supply).2 type
        (.indirectRead (.temporary (NativeIR.fresh child.supply).1 (.ref type)))),
    arguments_lowering_single interface (sourceFrameScope sourceFrame) reference childCompiled,
    ?_, stateful_reference_field_primitive_laws worldRelated interface sourceHeap sourceCalls
      targetHeap targetCalls sourceFrame source result default zero reference record member index type
      baseType position tagged child⟩
  simpa only [NativeLowering.prependCode, List.append_assoc] using same

/-- A field result receives its tag from the reached cell after evaluating the base. -/
theorem stateful_reference_field_source_tag {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {reference : Expr} {record member : String} {index : Nat}
    (baseType : inferExpr interface (sourceFrameScope frame) reference = some (.ref (.named record)))
    (position : NativeLowering.fieldLayout? interface record member = some index)
    (tagged : ∀ before post value,
      SourceExprEval interface heap calls frame reference before ⟨.ok value, post⟩ →
      SourceOuterTag (.ref (.named record)) value)
    (contentsTagged : ∀ before middle address value type,
      inferExpr interface (sourceFrameScope frame) (.field reference member) = some type →
      SourceExprEval interface heap calls frame reference before ⟨.ok (.reference (some address)), middle⟩ →
      sourceRead (sourceReferenceCall middle (some address)).state.memory (sourceFieldAddress address index) = some value →
      SourceOuterTag type value)
    {before post : SourceState World} {value : SourceValue} {type : NativeType}
    (typing : inferExpr interface (sourceFrameScope frame) (.field reference member) = some type)
    (ran : SourceExprEval interface heap calls frame (.field reference member) before ⟨.ok value, post⟩) :
    SourceOuterTag type value := by
  rcases (source_strict_expression_exact (.field reference member) [reference] rfl before _).mp ran with
    ⟨values, middle, argumentsRan, primitive⟩ | ⟨fault, after, _, impossible⟩
  · rcases (source_arguments_cons_exact reference [] before _).mp argumentsRan with
      ⟨head, after, tail, childRan, nilRan, same⟩ | ⟨fault, after, _, impossible⟩
    · have empty := (source_arguments_nil_exact after tail).mp nilRan
      subst tail
      cases same
      cases tagged before after head childRan with
      | reference element pointer =>
          have exactPrimitive := (source_reference_field_primitive_exact heap calls frame reference record member index
            pointer baseType position after _).mp primitive
          cases failed : (sourceReferenceCall after pointer).state.fault with
          | some fault => rw [failed] at exactPrimitive; cases exactPrimitive
          | none =>
              rw [failed] at exactPrimitive
              obtain ⟨address, loaded, pointed, read, same⟩ := exactPrimitive
              subst pointer
              cases Except.ok.inj (congrArg SourceOutcome.result same)
              exact contentsTagged before after address value type typing childRan read
    · cases impossible
  · cases impossible

end Mettapedia.GSLT.LanguageDef.NativeOps
