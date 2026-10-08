import Mettapedia.GSLT.LanguageDef.NativeOpsReferenceFieldExpression

/-!
# State and temporary frames of reference-field reads

These laws retain the existing checked-reference operation and the actual
emitted fresh names. They do not infer a loaded value's type from a pointer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Atom Instruction)
open NativeLowering (Expression)

theorem source_reference_state_shape {World : Type} (state : SourceState World)
    (pointer : Option Address) (clear : state.fault = none) :
    match (sourceReferenceCall state pointer).state.fault with
    | none => (sourceReferenceCall state pointer).state = state
    | some fault => (sourceReferenceCall state pointer).state = sourcePoison state fault := by
  unfold sourceReferenceCall
  generalize sourceCheckedValue state
    ((NativeOpsMemoryGuards.sourceReference pointer.isSome).map (fun _ => SourceValue.bool true)) = operation
  cases operation <;> simp [sourceRawFinish, sourcePoison, clear]

theorem target_reference_state_shape {World : Type} (state : TargetState World)
    (pointer : Option Address) (clear : state.fault = none) :
    match (targetReferenceCall state pointer).state.fault with
    | none => (targetReferenceCall state pointer).state = state
    | some fault => (targetReferenceCall state pointer).state = targetPoison state fault := by
  unfold targetReferenceCall
  generalize targetCheckedValue state
    ((NativeOpsMemoryGuards.targetReference pointer.isSome).map (fun _ => TargetValue.bool true)) = operation
  cases operation <;> simp [targetRawFinish, targetPoison, clear]

theorem reference_field_child_bounds {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {base : Expr} {record member : String}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default base)
    (baseType : inferExpr interface (sourceFrameScope sourceFrame) base = some (.ref (.named record)))
    {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.field base member)
      supply = some output) :
    supply.next < output.supply.next ∧ atomWithin output.supply.next output.result := by
  obtain ⟨type, first, index, _, firstCompiled, _, same⟩ := reference_field_combined_lowering_exact baseType compiled
  subst output
  exact ⟨((child.bounds firstCompiled).1.trans (NativeIR.fresh_strict first.supply)).trans
    (NativeIR.fresh_strict (NativeIR.fresh first.supply).2), Nat.le_refl _⟩

theorem reference_field_child_source_state {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {base : Expr} {record member : String}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default base)
    (baseType : inferExpr interface (sourceFrameScope sourceFrame) base = some (.ref (.named record)))
    (clear : source.fault = none) {index : Nat}
    (position : NativeLowering.fieldLayout? interface record member = some index)
    {out : SourceOutcome SourceWorld}
    (ran : SourceExprEval interface sourceHeap sourceCalls sourceFrame (.field base member) source out) :
    SourceScalarResultState source out.result out.state := by
  rcases (source_read_operand_exact child rfl out).mp ran with
    ⟨value, first, primitive⟩ | ⟨fault, _, same⟩
  · have tag := child.sourceTag baseType first
    cases tag with
    | reference element pointer =>
        have exactSource := (source_reference_field_primitive_exact sourceHeap sourceCalls sourceFrame
          base record member index pointer baseType position source out).mp primitive
        have shape := source_reference_state_shape source pointer clear
        cases failed : (sourceReferenceCall source pointer).state.fault with
        | some fault =>
            rw [failed] at exactSource shape
            subst out
            exact shape
        | none =>
            rw [failed] at exactSource shape
            obtain ⟨_, _, _, _, same⟩ := exactSource
            subst out
            exact shape
  · subst out
    rfl

theorem target_reference_field_frame {SourceWorld TargetWorld : Type} {interface : Interface}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target)
    {heap : TargetHeapSemantics TargetWorld} {calls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} (zero : TargetZero interface result default)
    {frame : TargetFrame} {atom : Atom} {pointer : Option Address}
    (read : TargetAtomEval interface frame target atom (.reference pointer))
    (record : String) (index : Nat) (type : NativeType) (supply : NativeIR.Supply)
    (bounded : TemporaryNamesBound frame supply.next) (hscope : TemporariesScoped frame)
    (root : List Instruction) {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface heap calls result root
      (NativeLowering.checkReference atom ++
        [.temporary (NativeIR.fresh supply).1 (.ref type) (.fieldAddress atom record index),
         .temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 type
           (.indirectRead (.temporary (NativeIR.fresh supply).1 (.ref type)))]) frame target out) :
    TemporaryProtection supply.next frame out.frame ∧
      TemporaryNamesBound out.frame (NativeIR.fresh (NativeIR.fresh supply).2).2.next ∧
      TemporariesScoped out.frame := by
  have first := NativeIR.fresh_strict supply
  have second := NativeIR.fresh_strict (NativeIR.fresh supply).2
  cases failed : (sourceReferenceCall source pointer).state.fault with
  | some fault =>
      have targetFailed := (reference_call_correspondence states pointer).state.fault.trans failed
      cases (target_field_read_fault_exact read record index _ _ type targetFailed zero root out).mp ran
      exact ⟨temporary_protection_refl _ _, guarded_temporary_bound_mono bounded
        (Nat.le_of_lt (first.trans second)), hscope⟩
  | none =>
      obtain ⟨address, pointed⟩ := source_reference_clear_nonnull source pointer failed
      subst pointer
      obtain ⟨value, _, same⟩ := (target_field_read_clear_exact states frame atom address record index _ _ type
        read (temporary_bound_fresh bounded first) (temporary_bound_fresh bounded (first.trans second))
        (Nat.ne_of_gt second) failed root out).mp ran
      subst out
      refine ⟨temporary_protection_trans (declare_temporary_protects frame _ first)
        (declare_temporary_protects _ _ (first.trans second)), ?_, ?_⟩
      · exact declared_temporary_bound
          (declared_temporary_bound bounded (Nat.le_of_lt first) (Nat.le_refl _) _)
          (Nat.le_of_lt second) (Nat.le_refl _) _
      · exact declared_temporaries_completeNames (declared_temporaries_completeNames hscope _ _) _ _

theorem source_scalar_outcome_equal {World : Type} {state : SourceState World}
    {left right : SourceOutcome World}
    (leftState : SourceScalarResultState state left.result left.state)
    (rightState : SourceScalarResultState state right.result right.state)
    (sameResult : left.result.map encodeValue = right.result.map encodeValue) : left = right := by
  rcases left with ⟨leftResult, leftPost⟩
  rcases right with ⟨rightResult, rightPost⟩
  cases leftResult <;> cases rightResult <;>
    simp only [Except.map, Except.ok.injEq, Except.error.injEq, reduceCtorEq,
      encodeValue_injective.eq_iff] at sameResult
  all_goals cases sameResult
  all_goals change leftPost = _ at leftState
  all_goals change rightPost = _ at rightState
  all_goals cases leftState; cases rightState; rfl

theorem target_reference_field_guarded {SourceWorld TargetWorld : Type} {interface : Interface}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    (sourceFrame : SourceFrame) (frame : TargetFrame) (base : Expr) (pointer : Option Address)
    (record member : String) (index locationId valueId : Nat) (type result : NativeType)
    (baseType : inferExpr interface (sourceFrameScope sourceFrame) base = some (.ref (.named record)))
    (position : NativeLowering.fieldLayout? interface record member = some index)
    (atom : Atom) (read : TargetAtomEval interface frame target atom (.reference pointer))
    (locationUnused : frame.temporaryNames.contains locationId = false)
    (valueUnused : frame.temporaryNames.contains valueId = false) (distinct : valueId ≠ locationId)
    {default : TargetValue} (zero : TargetZero interface result default)
    (root : List Instruction) {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root
      (NativeLowering.checkReference atom ++
        [.temporary locationId (.ref type) (.fieldAddress atom record index),
         .temporary valueId type (.indirectRead (.temporary locationId (.ref type)))]) frame target out) :
    ∃ sourceOut, sourcePrimitive interface sourceHeap sourceCalls sourceFrame (.field base member)
      [.reference pointer] source sourceOut ∧
      GuardedEvaluationRelated interface default (.temporary valueId type) source target sourceOut out := by
  have related := reference_call_correspondence states pointer
  have sourceShape := source_reference_state_shape source pointer clear
  have targetShape := target_reference_state_shape target pointer (states.fault.trans clear)
  cases failed : (sourceReferenceCall source pointer).state.fault with
  | some fault =>
      have targetFailed := related.state.fault.trans failed
      rw [failed] at sourceShape
      rw [targetFailed] at targetShape
      cases (target_field_read_fault_exact read record index locationId valueId type targetFailed zero root out).mp ran
      refine ⟨⟨.error fault, (sourceReferenceCall source pointer).state⟩, ?_, sourceShape, rfl, targetShape⟩
      exact (source_reference_field_primitive_exact sourceHeap sourceCalls sourceFrame base record member
        index pointer baseType position source _).mpr (by simp only [failed])
  | none =>
      have targetClear := related.state.fault.trans failed
      rw [failed] at sourceShape
      rw [targetClear] at targetShape
      obtain ⟨address, pointed⟩ := source_reference_clear_nonnull source pointer failed
      subst pointer
      obtain ⟨value, loaded, same⟩ := (target_field_read_clear_exact states frame atom address record index
        locationId valueId type read locationUnused valueUnused distinct failed root out).mp ran
      subst out
      refine ⟨⟨.ok value, (sourceReferenceCall source (some address)).state⟩, ?_, sourceShape, rfl,
        targetShape, declared_temporary_atom interface _ _ valueId type (encodeValue value)⟩
      apply (source_reference_field_primitive_exact sourceHeap sourceCalls sourceFrame base record member
        index (some address) baseType position source _).mpr
      simpa only [failed] using ⟨address, value, rfl, loaded, rfl⟩

theorem stateful_checked_reference_field_fragment_profile {SourceWorld TargetWorld : Type}
    {interface : Interface} {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    (sourceFrame : SourceFrame) (frame : TargetFrame) (reference : Expr) (pointer : Option Address)
    (record member : String) (index : Nat) (type result : NativeType) {default : TargetValue}
    (baseType : inferExpr interface (sourceFrameScope sourceFrame) reference = some (.ref (.named record)))
    (position : NativeLowering.fieldLayout? interface record member = some index)
    (atom : Atom) (supply : NativeIR.Supply)
    (read : TargetAtomEval interface frame target atom (.reference pointer))
    (bounded : TemporaryNamesBound frame supply.next) (hscope : TemporariesScoped frame)
    (zero : TargetZero interface result default) (root : List Instruction)
    {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root
      (NativeLowering.checkReference atom ++
        [.temporary (NativeIR.fresh supply).1 (.ref type) (.fieldAddress atom record index),
         .temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 type
           (.indirectRead (.temporary (NativeIR.fresh supply).1 (.ref type)))]) frame target out) :
    ∃ sourceOut,
      sourcePrimitive interface sourceHeap sourceCalls sourceFrame (.field reference member)
        [.reference pointer] source sourceOut ∧
      CheckedExpressionRelated worldRelated interface default
        (.temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 type) sourceOut out ∧
      TemporaryProtection supply.next frame out.frame ∧
      TemporaryNamesBound out.frame (NativeIR.fresh (NativeIR.fresh supply).2).2.next ∧
      TemporariesScoped out.frame := by
  have next := NativeIR.fresh_strict supply
  have nextValue := NativeIR.fresh_strict (NativeIR.fresh supply).2
  obtain ⟨sourceOut, primitive, agreement⟩ := target_reference_field_guarded states clear
    sourceHeap sourceCalls sourceFrame frame reference pointer record member index _ _ type result
    baseType position atom read (temporary_bound_fresh bounded next)
    (temporary_bound_fresh bounded (next.trans nextValue)) (Nat.ne_of_gt nextValue) zero root ran
  obtain ⟨protection, finalBounded, finalScoped⟩ :=
    target_reference_field_frame states zero read record index type supply bounded hscope root ran
  exact ⟨sourceOut, primitive, guarded_related_checked states clear agreement,
    protection, finalBounded, finalScoped⟩

end Mettapedia.GSLT.LanguageDef.NativeOps
