import Mettapedia.GSLT.LanguageDef.NativeOpsReadLoweringFacts
import Mettapedia.GSLT.LanguageDef.NativeOpsShortCircuitCorrespondence

/-!
# Composition of actual read expressions

The constructor laws compose real source evaluations with actual emitted
target runs. Guarded and short-circuit child laws have concrete factories;
they preserve complete read-only states or their first-fault poison. Loaded
contents are reflected through the memory relation before any scalar typing
claim is made. Undefined storage is not promoted to a default result.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Atom Instruction)
open NativeLowering (Expression)

theorem source_read_operand_exact {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {expression operand : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default operand)
    (operands : sourceStrictOperands? expression = some [operand]) (out : SourceOutcome SourceWorld) :
    SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source out ↔
      (∃ value, SourceExprEval interface sourceHeap sourceCalls sourceFrame operand source
        ⟨.ok value, source⟩ ∧ sourcePrimitive interface sourceHeap sourceCalls sourceFrame
          expression [value] source out) ∨
      (∃ fault, SourceExprEval interface sourceHeap sourceCalls sourceFrame operand source
        ⟨.error fault, sourcePoison source fault⟩ ∧ out = ⟨.error fault, sourcePoison source fault⟩) := by
  rw [source_strict_expression_exact _ _ operands]
  constructor
  · rintro (⟨values, middle, evaluated, primitive⟩ | ⟨fault, after, evaluated, same⟩)
    · rcases (source_arguments_cons_exact operand [] source _).mp evaluated with
        ⟨value, between, tail, first, remaining, same⟩ | ⟨fault, after, _, same⟩
      · cases (source_arguments_nil_exact between _).mp remaining
        cases same
        have unchanged := child.sourceState first
        change between = source at unchanged
        subst between
        exact .inl ⟨value, first, primitive⟩
      · cases same
    · rcases (source_arguments_cons_fault_exact operand [] source after fault).mp evaluated with
        first | ⟨value, middle, _, remaining⟩
      · have exactState := child.sourceState first
        change after = sourcePoison source fault at exactState
        subst after
        exact .inr ⟨fault, first, same⟩
      · cases (source_arguments_nil_exact middle _).mp remaining
  · rintro (⟨value, first, primitive⟩ | ⟨fault, first, same⟩)
    · exact .inl ⟨[value], source, .cons first (.nil source), primitive⟩
    · exact .inr ⟨fault, sourcePoison source fault, .consFault first, same⟩

theorem source_length_child_exact {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {array : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default array) (out : SourceOutcome SourceWorld) :
    SourceExprEval interface sourceHeap sourceCalls sourceFrame (.length array) source out ↔
      (∃ element pointer length,
        SourceExprEval interface sourceHeap sourceCalls sourceFrame array source
          ⟨.ok (.array element pointer length), source⟩ ∧ out = ⟨.ok (.word length), source⟩) ∨
      (∃ fault, SourceExprEval interface sourceHeap sourceCalls sourceFrame array source
        ⟨.error fault, sourcePoison source fault⟩ ∧ out = ⟨.error fault, sourcePoison source fault⟩) := by
  rw [source_read_operand_exact child rfl]
  constructor
  · rintro (⟨value, evaluated, primitive⟩ | refused)
    · cases value <;> first
        | exact .inl ⟨_, _, _, evaluated, primitive⟩
        | cases primitive
    · exact .inr refused
  · rintro (⟨element, pointer, length, evaluated, same⟩ | refused)
    · exact .inl ⟨.array element pointer length, evaluated, same⟩
    · exact .inr refused

theorem length_child_source_state {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {array : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default array) {out : SourceOutcome SourceWorld}
    (ran : SourceExprEval interface sourceHeap sourceCalls sourceFrame (.length array) source out) :
    SourceScalarResultState source out.result out.state := by
  rcases (source_length_child_exact child out).mp ran with
    ⟨element, pointer, length, _, same⟩ | ⟨fault, _, same⟩
  · cases same; rfl
  · cases same; rfl

theorem length_child_source_tag {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {array : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default array) {type : NativeType} {value : SourceValue}
    (typing : inferExpr interface (sourceFrameScope sourceFrame) (.length array) = some type)
    (ran : SourceExprEval interface sourceHeap sourceCalls sourceFrame (.length array) source
      ⟨.ok value, source⟩) : SourceOuterTag type value := by
  cases (read_length_inferred typing).1
  rcases (source_length_child_exact child _).mp ran with
    ⟨element, pointer, length, _, same⟩ | ⟨fault, _, same⟩
  · cases same; exact .word length
  · cases same

theorem length_child_lowering_bounds {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {array : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default array) {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.length array)
      supply = some output) :
    supply.next < output.supply.next ∧ atomWithin output.supply.next output.result := by
  obtain ⟨type, first, _, firstCompiled, same⟩ := read_length_lowering_exact compiled
  subst output
  exact ⟨(child.bounds firstCompiled).1.trans (NativeIR.fresh_strict first.supply), Nat.le_refl _⟩

theorem length_child_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {array : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default array)
    (root : List Instruction) {supply : NativeIR.Supply} {output : Expression}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.length array)
      supply = some output) (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceOutcome SourceWorld}
    (ran : SourceExprEval interface sourceHeap sourceCalls sourceFrame (.length array) source sourceOut) :
    ∃ out, TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      GuardedEvaluationRelated interface default output.result source target sourceOut out ∧
      TemporaryProtection supply.next targetFrame out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  obtain ⟨type, first, _, firstCompiled, same⟩ := read_length_lowering_exact compiled
  subst output
  have next := NativeIR.fresh_strict first.supply
  have advance := (child.bounds firstCompiled).1
  have jumpFree := expression_lowering_jump_free interface (sourceFrameScope sourceFrame) array supply first firstCompiled
  rcases (source_length_child_exact child sourceOut).mp ran with
    ⟨element, pointer, length, sourceRan, same⟩ | ⟨fault, sourceRan, same⟩
  · subst sourceOut
    obtain ⟨⟨flow, middle, post⟩, firstRan, related, protection, middleBounded, middleScoped⟩ :=
      child.forward root firstCompiled frames states bounded hscope sourceRan
    rcases related with ⟨_, normal, unchanged, read⟩
    cases normal
    change post = target at unchanged
    subst post
    let after := targetDeclareTemporary middle (NativeIR.fresh first.supply).1
      (.word (NativeWord64.encode length))
    have tail : TargetRun interface targetHeap targetCalls result root
        (NativeLowering.pureTemporary first.supply type (.length first.result)).code middle target
        ⟨.normal, after, target⟩ :=
      (target_run_temporary_exact (temporary_bound_fresh middleBounded next)
        (.length read) root _).mpr rfl
    have all := target_append_normal root _ _ jumpFree firstRan tail
    refine ⟨⟨.normal, after, target⟩, all, ?_, ?_, ?_, ?_⟩
    · exact ⟨rfl, rfl, rfl, declared_temporary_atom interface middle target
        (NativeIR.fresh first.supply).1 type (.word (NativeWord64.encode length))⟩
    · exact temporary_protection_trans protection
        (declare_temporary_protects middle (.word (NativeWord64.encode length)) (advance.trans next))
    · exact declared_temporary_bound middleBounded (Nat.le_of_lt next) (Nat.le_refl _) _
    · exact declared_temporaries_completeNames middleScoped _ _
  · subst sourceOut
    obtain ⟨⟨flow, after, post⟩, firstRan, related, protection, afterBounded, afterScoped⟩ :=
      child.forward root firstCompiled frames states bounded hscope sourceRan
    rcases related with ⟨_, returned, poisoned⟩
    cases returned
    change post = targetPoison target fault at poisoned
    subst post
    have all := target_append_returned root _
      (NativeLowering.pureTemporary first.supply type (.length first.result)).code jumpFree firstRan
    exact ⟨⟨.returned default, after, targetPoison target fault⟩, all, ⟨rfl, rfl, rfl⟩,
      protection, guarded_temporary_bound_mono afterBounded (Nat.le_of_lt next), afterScoped⟩

theorem length_child_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {array : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default array)
    (root : List Instruction) {supply : NativeIR.Supply} {output : Expression}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.length array)
      supply = some output) (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out) :
    ∃ sourceOut, SourceExprEval interface sourceHeap sourceCalls sourceFrame (.length array) source sourceOut ∧
      GuardedEvaluationRelated interface default output.result source target sourceOut out ∧
      TemporaryProtection supply.next targetFrame out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  obtain ⟨type, first, typing, firstCompiled, same⟩ := read_length_lowering_exact compiled
  obtain ⟨_, element, arrayTyping⟩ := read_length_inferred typing
  subst output
  have next := NativeIR.fresh_strict first.supply
  have advance := (child.bounds firstCompiled).1
  have jumpFree := expression_lowering_jump_free interface (sourceFrameScope sourceFrame) array supply first firstCompiled
  rcases target_split_jump_free_prefix root first.code
      (NativeLowering.pureTemporary first.supply type (.length first.result)).code jumpFree ran with
    ⟨middle, post, firstRan, tail⟩ | ⟨value, after, post, firstRan, same⟩
  · obtain ⟨sourceOut, sourceRan, related, protection, middleBounded, middleScoped⟩ :=
      child.backward root firstCompiled frames states bounded hscope firstRan
    obtain ⟨value, sameSource, unchanged, read⟩ := guarded_related_normal related rfl
    cases sameSource
    change post = target at unchanged
    subst post
    have tag := child.sourceTag arrayTyping sourceRan
    cases tag with
    | array element pointer length =>
        have tailExact := target_run_temporary_exact (heap := targetHeap) (calls := targetCalls)
          (result := result) (type := type)
          (temporary_bound_fresh middleBounded next) (TargetPureEval.length read) root out
        cases tailExact.mp tail
        refine ⟨⟨.ok (.word length), source⟩,
          (source_length_child_exact child _).mpr (.inl ⟨element, pointer, length, sourceRan, rfl⟩),
          ?_, ?_, ?_, ?_⟩
        · exact ⟨rfl, rfl, rfl, declared_temporary_atom interface middle target
            (NativeIR.fresh first.supply).1 type (.word (NativeWord64.encode length))⟩
        · exact temporary_protection_trans protection
            (declare_temporary_protects middle (.word (NativeWord64.encode length)) (advance.trans next))
        · exact declared_temporary_bound middleBounded (Nat.le_of_lt next) (Nat.le_refl _) _
        · exact declared_temporaries_completeNames middleScoped _ _
  · obtain ⟨sourceOut, sourceRan, related, protection, afterBounded, afterScoped⟩ :=
      child.backward root firstCompiled frames states bounded hscope firstRan
    obtain ⟨fault, exactSource, exactDefault, exactState⟩ := guarded_related_returned related rfl
    cases exactSource
    subst value
    change post = targetPoison target fault at exactState
    subst post
    subst out
    exact ⟨⟨.error fault, sourcePoison source fault⟩,
      (source_length_child_exact child _).mpr (.inr ⟨fault, sourceRan, rfl⟩),
      ⟨rfl, rfl, rfl⟩, protection,
      guarded_temporary_bound_mono afterBounded (Nat.le_of_lt next), afterScoped⟩

theorem length_child_laws {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {array : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default array) :
    ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.length array) :=
  ⟨length_child_source_state child, length_child_source_tag child, length_child_lowering_bounds child,
    length_child_preservation child, length_child_reflection child⟩

/-- This factory uses the already proved child implementation, not an assumed target run. -/
theorem guarded_length_child_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld) (clear : source.fault = none)
    (tagged : SourceLocalsTagged sourceFrame source.memory)
    (result : NativeType) {default : TargetValue} (zero : TargetZero interface result default)
    {array : Expr} (guarded : SourceGuardedExpression array) :
    ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.length array) :=
  length_child_laws (guarded_short_circuit_child_laws worldRelated interface sourceHeap sourceCalls
    targetHeap targetCalls sourceFrame source clear tagged result zero guarded)

theorem source_load_primitive_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (reference : Expr) (pointer : Option Address) (state : SourceState World) (out : SourceOutcome World) :
    sourcePrimitive interface heap calls frame (.load reference) [.reference pointer] state out ↔
      match (sourceReferenceCall state pointer).state.fault with
      | some fault => out = ⟨.error fault, (sourceReferenceCall state pointer).state⟩
      | none => ∃ address value, pointer = some address ∧
          sourceRead (sourceReferenceCall state pointer).state.memory address = some value ∧
          out = ⟨.ok value, (sourceReferenceCall state pointer).state⟩ := by
  cases found : (sourceReferenceCall state pointer).state.fault with
  | some fault =>
      simp only [sourcePrimitive, sourcePrimitiveLocation, found]
      constructor
      · rintro ⟨location, same, next⟩
        subst location
        exact next
      · intro same
        exact ⟨⟨.error fault, (sourceReferenceCall state pointer).state⟩, rfl, same⟩
  | none =>
      simp only [sourcePrimitive, sourcePrimitiveLocation, found]
      constructor
      · rintro ⟨location, ⟨address, pointed, same⟩, next⟩
        subst location
        obtain ⟨value, read, same⟩ := next
        exact ⟨address, value, pointed, read, same⟩
      · rintro ⟨address, value, pointed, read, same⟩
        exact ⟨⟨.ok address, (sourceReferenceCall state pointer).state⟩,
          ⟨address, pointed, rfl⟩, value, read, same⟩

theorem source_reference_clear_nonnull {World : Type} (state : SourceState World) (pointer : Option Address)
    (clear : (sourceReferenceCall state pointer).state.fault = none) : ∃ address, pointer = some address := by
  cases pointer with
  | some address => exact ⟨address, rfl⟩
  | none =>
      cases prior : state.fault with
      | some fault =>
          simp only [sourceReferenceCall, sourceCheckedValue, NativeOpsMemoryGuards.sourceChecked,
            NativeOpsMemoryGuards.sourceReady, prior, sourceRawFinish, sourcePoison] at clear
          cases clear
      | none =>
          cases allocator : state.allocatorAvailable <;> cases release : state.releaseAvailable <;>
            simp only [sourceReferenceCall, sourceCheckedValue, NativeOpsMemoryGuards.sourceChecked,
              NativeOpsMemoryGuards.sourceReady, prior, allocator, release, Bool.false_and,
              Bool.true_and, Bool.false_eq_true, if_false, if_true,
              NativeOpsMemoryGuards.sourceReference, Option.isSome, Except.map,
              sourceRawFinish, sourcePoison] at clear
          all_goals cases clear

theorem checked_load_primitive_preservation {SourceWorld TargetWorld : Type} {interface : Interface}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (frame : TargetFrame) (reference : Expr) (pointer : Option Address)
    (atom : Atom) (identity : Nat) (type result : NativeType) {default : TargetValue}
    (read : TargetAtomEval interface frame target atom (.reference pointer))
    (unused : frame.temporaryNames.contains identity = false)
    (zero : TargetZero interface result default) (root : List Instruction)
    {sourceOut : SourceOutcome SourceWorld}
    (ran : sourcePrimitive interface sourceHeap sourceCalls sourceFrame (.load reference)
      [.reference pointer] source sourceOut) :
    ∃ out observed, TargetRun interface targetHeap targetCalls result root
        (NativeLowering.checkReference atom ++ [.temporary identity type (.indirectRead atom)]) frame target out ∧
      targetExpressionObservation interface (.temporary identity type) out observed ∧
      OutcomeRelated worldRelated sourceOut observed := by
  have rawRelated := reference_call_correspondence states pointer
  cases failed : (sourceReferenceCall source pointer).state.fault with
  | some fault =>
      have targetFailed := rawRelated.state.fault.trans failed
      have exactSource : sourceOut = ⟨.error fault, (sourceReferenceCall source pointer).state⟩ := by
        simpa only [failed] using (source_load_primitive_exact interface sourceHeap sourceCalls sourceFrame
          reference pointer source sourceOut).mp ran
      subst sourceOut
      refine ⟨⟨.returned default, frame, (targetReferenceCall target pointer).state⟩,
        targetObserve (targetReferenceCall target pointer).state default, ?_, rfl, ?_⟩
      · exact (target_reference_fault_then_exact read targetFailed zero root _ _).mpr rfl
      · refine ⟨?_, ?_⟩
        · simpa only [targetObserve_state] using rawRelated.state
        · simp [targetObserve, targetFailed, Except.map]
  | none =>
      obtain ⟨address, value, pointed, loaded, exactSource⟩ :=
        (show ∃ address value, pointer = some address ∧
          sourceRead (sourceReferenceCall source pointer).state.memory address = some value ∧
          sourceOut = ⟨.ok value, (sourceReferenceCall source pointer).state⟩ from by
          simpa only [failed] using (source_load_primitive_exact interface sourceHeap sourceCalls sourceFrame
            reference pointer source sourceOut).mp ran)
      subst sourceOut
      subst pointer
      have targetClear := rawRelated.state.fault.trans failed
      have afterRead := target_atom_state_irrelevant read (targetReferenceCall target (some address)).state
      have tail := (target_indirect_temporary_exact (heap := targetHeap) (calls := targetCalls)
        (result := result) rawRelated.state frame atom address identity type
        afterRead unused root ⟨.normal, targetDeclareTemporary frame identity (encodeValue value),
          (targetReferenceCall target (some address)).state⟩).mpr ⟨value, loaded, rfl⟩
      refine ⟨⟨.normal, targetDeclareTemporary frame identity (encodeValue value),
          (targetReferenceCall target (some address)).state⟩,
        targetObserve (targetReferenceCall target (some address)).state (encodeValue value),
        (target_reference_clear_then_exact read targetClear root _ _).mpr tail,
        ⟨encodeValue value, declared_temporary_atom interface frame _ identity type _, rfl⟩, ?_⟩
      refine ⟨?_, ?_⟩
      · simpa only [targetObserve_state] using rawRelated.state
      · simp [targetObserve, targetClear, Except.map]

theorem checked_load_primitive_reflection {SourceWorld TargetWorld : Type} {interface : Interface}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (frame : TargetFrame) (reference : Expr) (pointer : Option Address)
    (atom : Atom) (identity : Nat) (type result : NativeType) {default : TargetValue}
    (read : TargetAtomEval interface frame target atom (.reference pointer))
    (unused : frame.temporaryNames.contains identity = false)
    (zero : TargetZero interface result default) (root : List Instruction)
    {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root
      (NativeLowering.checkReference atom ++ [.temporary identity type (.indirectRead atom)]) frame target out)
    (observation : targetExpressionObservation interface (.temporary identity type) out observed) :
    ∃ sourceOut, sourcePrimitive interface sourceHeap sourceCalls sourceFrame (.load reference)
      [.reference pointer] source sourceOut ∧ OutcomeRelated worldRelated sourceOut observed := by
  have rawRelated := reference_call_correspondence states pointer
  cases failed : (sourceReferenceCall source pointer).state.fault with
  | some fault =>
      have targetFailed := rawRelated.state.fault.trans failed
      cases (target_reference_fault_then_exact read targetFailed zero root _ out).mp ran
      change observed = targetObserve (targetReferenceCall target pointer).state default at observation
      subst observed
      refine ⟨⟨.error fault, (sourceReferenceCall source pointer).state⟩, ?_, ?_, ?_⟩
      · apply (source_load_primitive_exact interface sourceHeap sourceCalls sourceFrame reference pointer source _).mpr
        simp only [failed]
      · simpa only [targetObserve_state] using rawRelated.state
      · simp [targetObserve, targetFailed, Except.map]
  | none =>
      obtain ⟨address, pointed⟩ := source_reference_clear_nonnull source pointer failed
      subst pointer
      have targetClear := rawRelated.state.fault.trans failed
      have afterRead := target_atom_state_irrelevant read (targetReferenceCall target (some address)).state
      have tail := (target_reference_clear_then_exact read targetClear root _ out).mp ran
      obtain ⟨value, loaded, exactTarget⟩ :=
        (target_indirect_temporary_exact rawRelated.state frame atom address identity type afterRead unused root out).mp tail
      subst out
      obtain ⟨native, nativeRead, exactObserved⟩ := observation
      cases target_atom_unique (declared_temporary_atom interface frame _ identity type (encodeValue value)) nativeRead
      subst observed
      refine ⟨⟨.ok value, (sourceReferenceCall source (some address)).state⟩, ?_, ?_, ?_⟩
      · apply (source_load_primitive_exact interface sourceHeap sourceCalls sourceFrame reference (some address) source _).mpr
        simpa only [failed] using ⟨address, value, rfl, loaded, rfl⟩
      · simpa only [targetObserve_state] using rawRelated.state
      · simp [targetObserve, targetClear, Except.map]

theorem load_child_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {reference : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default reference) (clear : source.fault = none)
    (zero : TargetZero interface result default)
    (root : List Instruction) {supply : NativeIR.Supply} {output : Expression}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.load reference)
      supply = some output) (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceOutcome SourceWorld}
    (ran : SourceExprEval interface sourceHeap sourceCalls sourceFrame (.load reference) source sourceOut) :
    ∃ out observed, TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      targetExpressionObservation interface output.result out observed ∧ OutcomeRelated worldRelated sourceOut observed := by
  obtain ⟨type, first, typing, firstCompiled, same⟩ := read_load_combined_lowering_exact compiled
  have childTyping := read_load_inferred typing
  subst output
  have next := NativeIR.fresh_strict first.supply
  have jumpFree := expression_lowering_jump_free interface (sourceFrameScope sourceFrame)
    reference supply first firstCompiled
  rcases (source_read_operand_exact child rfl sourceOut).mp ran with
    ⟨value, sourceRan, primitive⟩ | ⟨fault, sourceRan, same⟩
  · have tag := child.sourceTag childTyping sourceRan
    cases tag with
    | reference element pointer =>
        obtain ⟨⟨flow, middle, post⟩, firstRan, related, _, middleBounded, _⟩ :=
          child.forward root firstCompiled frames states bounded hscope sourceRan
        rcases related with ⟨_, normal, unchanged, read⟩
        cases normal
        change post = target at unchanged
        subst post
        obtain ⟨out, observed, tail, observation, outcome⟩ := checked_load_primitive_preservation
          states sourceHeap sourceCalls targetHeap targetCalls sourceFrame middle reference pointer
          first.result (NativeIR.fresh first.supply).1 type result read
          (temporary_bound_fresh middleBounded next) zero root primitive
        have all := target_append_normal root _ _ jumpFree firstRan tail
        exact ⟨out, observed, by simpa only [NativeLowering.prependCode, NativeLowering.pureTemporary,
          List.append_assoc] using all, observation, outcome⟩
  · subst sourceOut
    obtain ⟨⟨flow, after, post⟩, firstRan, related, _, _, _⟩ :=
      child.forward root firstCompiled frames states bounded hscope sourceRan
    rcases related with ⟨_, returned, poisoned⟩
    cases returned
    change post = targetPoison target fault at poisoned
    subst post
    have all := target_append_returned root _
      (NativeLowering.checkReference first.result ++
        (NativeLowering.pureTemporary first.supply type (.indirectRead first.result)).code)
      jumpFree firstRan
    have wholeRelated : GuardedEvaluationRelated interface default
        (NativeLowering.pureTemporary first.supply type (.indirectRead first.result)).result source target
        ⟨.error fault, sourcePoison source fault⟩
        ⟨.returned default, after, targetPoison target fault⟩ := ⟨rfl, rfl, rfl⟩
    obtain ⟨observed, observation⟩ := guarded_related_has_observation wholeRelated
    have outcome := guarded_related_observation_correspondence states clear wholeRelated observation
    exact ⟨⟨.returned default, after, targetPoison target fault⟩, observed,
      by simpa only [NativeLowering.prependCode, List.append_assoc] using all, observation, outcome⟩

theorem load_child_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {reference : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default reference) (clear : source.fault = none)
    (zero : TargetZero interface result default)
    (root : List Instruction) {supply : NativeIR.Supply} {output : Expression}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.load reference)
      supply = some output) (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out)
    (observation : targetExpressionObservation interface output.result out observed) :
    ∃ sourceOut, SourceExprEval interface sourceHeap sourceCalls sourceFrame (.load reference) source sourceOut ∧
      OutcomeRelated worldRelated sourceOut observed := by
  obtain ⟨type, first, typing, firstCompiled, same⟩ := read_load_combined_lowering_exact compiled
  have childTyping := read_load_inferred typing
  subst output
  have next := NativeIR.fresh_strict first.supply
  have jumpFree := expression_lowering_jump_free interface (sourceFrameScope sourceFrame)
    reference supply first firstCompiled
  have all : TargetRun interface targetHeap targetCalls result root
      (first.code ++ NativeLowering.checkReference first.result ++
        (NativeLowering.pureTemporary first.supply type (.indirectRead first.result)).code)
      targetFrame target out := ran
  rw [List.append_assoc] at all
  rcases target_split_jump_free_prefix root first.code _ jumpFree all with
    ⟨middle, post, firstRan, tail⟩ | ⟨value, after, post, firstRan, same⟩
  · obtain ⟨sourceOut, sourceRan, related, _, middleBounded, _⟩ :=
      child.backward root firstCompiled frames states bounded hscope firstRan
    obtain ⟨value, sameSource, unchanged, read⟩ := guarded_related_normal related rfl
    cases sameSource
    change post = target at unchanged
    subst post
    have tag := child.sourceTag childTyping sourceRan
    cases tag with
    | reference element pointer =>
        obtain ⟨sourceOut, primitive, outcome⟩ := checked_load_primitive_reflection
          states sourceHeap sourceCalls targetHeap targetCalls sourceFrame middle reference pointer
          first.result (NativeIR.fresh first.supply).1 type result read
          (temporary_bound_fresh middleBounded next) zero root tail observation
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
        (NativeLowering.pureTemporary first.supply type (.indirectRead first.result)).result source target
        ⟨.error fault, sourcePoison source fault⟩
        ⟨.returned default, after, targetPoison target fault⟩ := ⟨rfl, rfl, rfl⟩
    exact ⟨⟨.error fault, sourcePoison source fault⟩,
      (source_read_operand_exact child rfl _).mpr (.inr ⟨fault, sourceRan, rfl⟩),
      guarded_related_observation_correspondence states clear wholeRelated observation⟩

theorem guarded_load_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    {result : NativeType} {default : TargetValue} (zero : TargetZero interface result default)
    {reference : Expr} (guarded : SourceGuardedExpression reference)
    (root : List Instruction) {supply : NativeIR.Supply} {output : Expression}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.load reference)
      supply = some output) (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceOutcome SourceWorld}
    (ran : SourceExprEval interface sourceHeap sourceCalls sourceFrame (.load reference) source sourceOut) :
    ∃ out observed, TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      targetExpressionObservation interface output.result out observed ∧ OutcomeRelated worldRelated sourceOut observed :=
  load_child_preservation (guarded_short_circuit_child_laws worldRelated interface sourceHeap sourceCalls
    targetHeap targetCalls sourceFrame source clear tagged result zero guarded)
    clear zero root compiled frames states bounded hscope ran

theorem guarded_load_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    {result : NativeType} {default : TargetValue} (zero : TargetZero interface result default)
    {reference : Expr} (guarded : SourceGuardedExpression reference)
    (root : List Instruction) {supply : NativeIR.Supply} {output : Expression}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) (.load reference)
      supply = some output) (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out)
    (observation : targetExpressionObservation interface output.result out observed) :
    ∃ sourceOut, SourceExprEval interface sourceHeap sourceCalls sourceFrame (.load reference) source sourceOut ∧
      OutcomeRelated worldRelated sourceOut observed :=
  load_child_reflection (guarded_short_circuit_child_laws worldRelated interface sourceHeap sourceCalls
    targetHeap targetCalls sourceFrame source clear tagged result zero guarded)
    clear zero root compiled frames states bounded hscope ran observation

end Mettapedia.GSLT.LanguageDef.NativeOps
