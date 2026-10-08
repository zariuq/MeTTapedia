import Mettapedia.GSLT.LanguageDef.NativeOpsReadLoweringFacts
import Mettapedia.GSLT.LanguageDef.NativeOpsShortCircuitCorrespondence

/-!
# Composition of actual read expressions

The constructor laws compose real source evaluations with actual emitted
target runs. Guarded and short-circuit child laws have concrete factories;
they retain either read-only states or complete effectful post-states. A shared
ordered-argument composition supplies stateful load, descriptor-length and
array-index and three-operand slice clients. Shared raw reference and array
descriptor comparisons retain stored helper returns and the exact context
post-state before checks, reads and length writes. Loaded contents are reflected
through the memory relation before any scalar typing claim is made. Undefined
storage is not promoted to a default result.
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

theorem stateful_length_primitive_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld)
    (result : NativeType) (default : TargetValue) (array : Expr) (element : NativeType)
    (tagged : ∀ before post value,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame array before ⟨.ok value, post⟩ →
      SourceOuterTag (.array element) value)
    (child : NativeLowering.Expression) :
    StatefulPrimitiveLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.length array) [array]
      ⟨child.code, [child.result], child.supply⟩
      (NativeLowering.pureTemporary child.supply .word (.length child.result)) := by
  have next := NativeIR.fresh_strict child.supply
  refine ⟨⟨next.le, Nat.le_refl _⟩, ?_, ?_⟩
  · intro root values middle argsRan clear frame target _ states bounded hscope reads sourceOut primitiveRan
    obtain ⟨value, same, read⟩ := target_one_encoded_argument reads
    subst values
    have childRan := (source_single_argument_success_exact array source middle value).mp argsRan
    cases tagged source middle value childRan with
    | array element pointer length =>
        change sourceOut = ⟨.ok (.word length), middle⟩ at primitiveRan
        subst sourceOut
        have ran : TargetRun interface targetHeap targetCalls result root
            (NativeLowering.pureTemporary child.supply .word (.length child.result)).code frame target
            ⟨.normal, targetDeclareTemporary frame (NativeIR.fresh child.supply).1
              (.word (NativeWord64.encode length)), target⟩ :=
          (target_run_temporary_exact (temporary_bound_fresh bounded next)
            (TargetPureEval.length read) root _).mpr rfl
        obtain ⟨protection, finalBounded, finalScoped⟩ := declared_temporary_frame_profile
          bounded hscope next (Nat.le_refl _) (.word (NativeWord64.encode length))
        exact ⟨_, ran, ⟨states, clear, rfl, declared_temporary_atom interface frame target
          (NativeIR.fresh child.supply).1 .word (.word (NativeWord64.encode length))⟩,
          protection, finalBounded, finalScoped⟩
  · intro root values middle argsRan clear frame target _ states bounded hscope reads out ran
    obtain ⟨value, same, read⟩ := target_one_encoded_argument reads
    subst values
    have childRan := (source_single_argument_success_exact array source middle value).mp argsRan
    cases tagged source middle value childRan with
    | array element pointer length =>
        have same := (target_run_temporary_exact (heap := targetHeap) (calls := targetCalls)
          (result := result) (type := NativeType.word) (temporary_bound_fresh bounded next)
          (TargetPureEval.length read) root out).mp ran
        subst out
        obtain ⟨protection, finalBounded, finalScoped⟩ := declared_temporary_frame_profile
          bounded hscope next (Nat.le_refl _) (.word (NativeWord64.encode length))
        exact ⟨⟨.ok (.word length), middle⟩, rfl,
          ⟨states, clear, rfl, declared_temporary_atom interface frame target
            (NativeIR.fresh child.supply).1 .word (.word (NativeWord64.encode length))⟩,
          protection, finalBounded, finalScoped⟩

theorem stateful_length_child_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld) (clear : source.fault = none)
    (result : NativeType) (default : TargetValue) (array : Expr)
    (children : ∀ before, before.fault = none →
      StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
        sourceFrame before result default array)
    (tagged : ∀ before post value element,
      inferExpr interface (sourceFrameScope sourceFrame) array = some (.array element) →
      SourceExprEval interface sourceHeap sourceCalls sourceFrame array before ⟨.ok value, post⟩ →
      SourceOuterTag (.array element) value) :
    StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.length array) := by
  apply stateful_strict_child_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
    sourceFrame source clear result default (.length array) [array] rfl
    (fun child member before ready => by cases List.mem_singleton.mp member; exact children before ready)
  intro supply output compiled
  obtain ⟨type, child, typing, childCompiled, same⟩ := read_length_lowering_exact compiled
  obtain ⟨typeSame, element, arrayTyping⟩ := read_length_inferred typing
  subst type
  exact ⟨⟨child.code, [child.result], child.supply⟩,
    NativeLowering.pureTemporary child.supply .word (.length child.result),
    arguments_lowering_single interface (sourceFrameScope sourceFrame) array childCompiled,
    same, stateful_length_primitive_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default array element (fun before post value ran => tagged before post value element arrayTyping ran) child⟩



theorem source_load_primitive_unique {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {reference : Expr} {pointer : Option Address} {state : SourceState World}
    {first second : SourceOutcome World}
    (left : sourcePrimitive interface heap calls frame (.load reference) [.reference pointer] state first)
    (right : sourcePrimitive interface heap calls frame (.load reference) [.reference pointer] state second) :
    first = second := by
  have leftExact := (source_load_primitive_exact interface heap calls frame reference pointer state first).mp left
  have rightExact := (source_load_primitive_exact interface heap calls frame reference pointer state second).mp right
  cases failed : (sourceReferenceCall state pointer).state.fault with
  | some fault =>
      simp only [failed] at leftExact rightExact
      exact leftExact.trans rightExact.symm
  | none =>
      simp only [failed] at leftExact rightExact
      obtain ⟨leftAddress, leftValue, leftPointer, leftRead, leftOut⟩ := leftExact
      obtain ⟨rightAddress, rightValue, rightPointer, rightRead, rightOut⟩ := rightExact
      cases Option.some.inj (leftPointer.symm.trans rightPointer)
      cases Option.some.inj (leftRead.symm.trans rightRead)
      exact leftOut.trans rightOut.symm

theorem stateful_checked_load_fragment_profile {SourceWorld TargetWorld : Type} {interface : Interface}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (frame : TargetFrame) (reference : Expr) (pointer : Option Address)
    (atom : NativeIR.Atom) (supply : NativeIR.Supply) (type result : NativeType) {default : TargetValue}
    (read : TargetAtomEval interface frame target atom (.reference pointer))
    (bounded : TemporaryNamesBound frame supply.next) (hscope : TemporariesScoped frame)
    (zero : TargetZero interface result default) (root : List Instruction)
    {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root
      (NativeLowering.checkReference atom ++
        (NativeLowering.pureTemporary supply type (.indirectRead atom)).code) frame target out) :
    ∃ sourceOut,
      sourcePrimitive interface sourceHeap sourceCalls sourceFrame (.load reference)
        [.reference pointer] source sourceOut ∧
      CheckedExpressionRelated worldRelated interface default
        (NativeLowering.pureTemporary supply type (.indirectRead atom)).result sourceOut out ∧
      TemporaryProtection supply.next frame out.frame ∧
      TemporaryNamesBound out.frame (NativeIR.fresh supply).2.next ∧ TemporariesScoped out.frame := by
  have rawRelated := reference_call_correspondence states pointer
  have next := NativeIR.fresh_strict supply
  have unused := temporary_bound_fresh bounded next
  cases failed : (sourceReferenceCall source pointer).state.fault with
  | some fault =>
      have targetFailed := rawRelated.state.fault.trans failed
      cases (target_reference_fault_then_exact read targetFailed zero root _ out).mp ran
      refine ⟨⟨.error fault, (sourceReferenceCall source pointer).state⟩, ?_,
        ⟨rawRelated.state, failed, rfl⟩, temporary_protection_refl _ _,
        temporary_names_bound_weaken next.le bounded, hscope⟩
      apply (source_load_primitive_exact interface sourceHeap sourceCalls sourceFrame reference pointer source _).mpr
      simp only [failed]
  | none =>
      obtain ⟨address, pointed⟩ := source_reference_clear_nonnull source pointer failed
      subst pointer
      have targetClear := rawRelated.state.fault.trans failed
      have afterRead := target_atom_state_irrelevant read (targetReferenceCall target (some address)).state
      have tail := (target_reference_clear_then_exact read targetClear root _ out).mp ran
      obtain ⟨value, loaded, exactTarget⟩ :=
        (target_indirect_temporary_exact rawRelated.state frame atom address (NativeIR.fresh supply).1
          type afterRead unused root out).mp tail
      subst out
      obtain ⟨protection, finalBounded, finalScoped⟩ := declared_temporary_frame_profile
        bounded hscope next (Nat.le_refl _) (encodeValue value)
      refine ⟨⟨.ok value, (sourceReferenceCall source (some address)).state⟩, ?_,
        ⟨rawRelated.state, failed, rfl,
          declared_temporary_atom interface frame _ (NativeIR.fresh supply).1 type (encodeValue value)⟩,
        protection, finalBounded, finalScoped⟩
      apply (source_load_primitive_exact interface sourceHeap sourceCalls sourceFrame reference (some address) source _).mpr
      simpa only [failed] using ⟨address, value, rfl, loaded, rfl⟩

theorem stateful_load_primitive_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld)
    (result : NativeType) (default : TargetValue) (zero : TargetZero interface result default)
    (reference : Expr) (type : NativeType)
    (tagged : ∀ before post value,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame reference before ⟨.ok value, post⟩ →
      SourceOuterTag (.ref type) value)
    (child : NativeLowering.Expression) :
    StatefulPrimitiveLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.load reference) [reference]
      ⟨child.code, [child.result], child.supply⟩
      (NativeLowering.prependCode (NativeLowering.checkReference child.result)
        (NativeLowering.pureTemporary child.supply type (.indirectRead child.result))) := by
  have next := NativeIR.fresh_strict child.supply
  refine ⟨⟨next.le, Nat.le_refl _⟩, ?_, ?_⟩
  · intro root values middle argsRan _ frame target _ states bounded hscope reads sourceOut primitiveRan
    obtain ⟨value, same, read⟩ := target_one_encoded_argument reads
    subst values
    have childRan := (source_single_argument_success_exact reference source middle value).mp argsRan
    cases tagged source middle value childRan with
    | reference element pointer =>
        obtain ⟨out, _, targetRan, _, _⟩ := checked_load_primitive_preservation states
          sourceHeap sourceCalls targetHeap targetCalls sourceFrame frame reference pointer child.result
          (NativeIR.fresh child.supply).1 type result read (temporary_bound_fresh bounded next) zero root primitiveRan
        obtain ⟨reflected, reflectedRan, checked, protection, finalBounded, finalScoped⟩ :=
          stateful_checked_load_fragment_profile states sourceHeap sourceCalls targetHeap targetCalls
            sourceFrame frame reference pointer child.result child.supply type result read bounded hscope zero root targetRan
        cases source_load_primitive_unique primitiveRan reflectedRan
        exact ⟨out, targetRan, checked, protection, finalBounded, finalScoped⟩
  · intro root values middle argsRan _ frame target _ states bounded hscope reads out ran
    obtain ⟨value, same, read⟩ := target_one_encoded_argument reads
    subst values
    have childRan := (source_single_argument_success_exact reference source middle value).mp argsRan
    cases tagged source middle value childRan with
    | reference element pointer =>
        exact stateful_checked_load_fragment_profile states sourceHeap sourceCalls targetHeap targetCalls
          sourceFrame frame reference pointer child.result child.supply type result read bounded hscope zero root ran

theorem stateful_load_child_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld) (clear : source.fault = none)
    (result : NativeType) (default : TargetValue) (zero : TargetZero interface result default)
    (reference : Expr)
    (children : ∀ before, before.fault = none →
      StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
        sourceFrame before result default reference)
    (tagged : ∀ before post value type,
      inferExpr interface (sourceFrameScope sourceFrame) reference = some (.ref type) →
      SourceExprEval interface sourceHeap sourceCalls sourceFrame reference before ⟨.ok value, post⟩ →
      SourceOuterTag (.ref type) value) :
    StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.load reference) := by
  apply stateful_strict_child_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
    sourceFrame source clear result default (.load reference) [reference] rfl
    (fun child member before ready => by cases List.mem_singleton.mp member; exact children before ready)
  intro supply output compiled
  obtain ⟨type, child, typing, childCompiled, same⟩ := read_load_combined_lowering_exact compiled
  refine ⟨⟨child.code, [child.result], child.supply⟩,
    NativeLowering.prependCode (NativeLowering.checkReference child.result)
      (NativeLowering.pureTemporary child.supply type (.indirectRead child.result)),
    arguments_lowering_single interface (sourceFrameScope sourceFrame) reference childCompiled,
    ?_, stateful_load_primitive_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default zero reference type
      (fun before post value ran => tagged before post value type (read_load_inferred typing) ran) child⟩
  simpa only [NativeLowering.prependCode, List.append_assoc] using same

theorem stateful_checked_raw_reference_read_profile {SourceWorld TargetWorld : Type}
    {interface : Interface} {worldRelated : SourceWorld → TargetWorld → Prop}
    {sourceRaw : SourceRawResult SourceWorld} {targetRaw : TargetRawResult TargetWorld}
    {heap : TargetHeapSemantics TargetWorld} {calls : TargetCalls TargetWorld} {result : NativeType}
    {frame : TargetFrame} {state : TargetState TargetWorld} {operation : NativeIR.MemoryOperation}
    (rawRelated : RawResultRelated worldRelated sourceRaw targetRaw)
    (callExact : ∀ other, TargetMemoryCall interface heap frame operation state other ↔ other = targetRaw)
    (supply : NativeIR.Supply) (type : NativeType) {default : TargetValue}
    (bounded : TemporaryNamesBound frame supply.next) (hscope : TemporariesScoped frame)
    (zero : TargetZero interface result default) (root : List Instruction)
    {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface heap calls result root
      [.helper (some (.temporary (NativeIR.fresh supply).1 (.ref type))) operation, .checkContext,
        .temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 type
          (.indirectRead (.temporary (NativeIR.fresh supply).1 (.ref type)))] frame state out) :
    ∃ sourceOut,
      (∃ location, sourceReferenceLocation sourceRaw location ∧
        sourceLocationNext location (fun address post => ∃ value,
          sourceRead post.memory address = some value ∧ sourceOut = ⟨.ok value, post⟩) sourceOut) ∧
      CheckedExpressionRelated worldRelated interface default
        (.temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 type) sourceOut out ∧
      TemporaryProtection supply.next frame out.frame ∧
      TemporaryNamesBound out.frame (NativeIR.fresh (NativeIR.fresh supply).2).2.next ∧
      TemporariesScoped out.frame := by
  have firstFresh := NativeIR.fresh_strict supply
  have secondFresh := NativeIR.fresh_strict (NativeIR.fresh supply).2
  obtain ⟨firstProtected, firstBounded, firstScoped⟩ := declared_temporary_frame_profile
    bounded hscope firstFresh (Nat.le_refl _) targetRaw.value
  have exactRun := (target_raw_reference_read_exact rawRelated callExact
    (temporary_bound_fresh bounded firstFresh) (temporary_bound_fresh firstBounded secondFresh)
    zero root out).mp ran
  cases failed : sourceRaw.state.fault with
  | some fault =>
      simp only [failed] at exactRun
      subst out
      refine ⟨⟨.error fault, sourceRaw.state⟩,
        (source_reference_location_read_exact sourceRaw _).mpr ?_,
        ⟨rawRelated.state, failed, rfl⟩, firstProtected,
        temporary_names_bound_weaken secondFresh.le firstBounded, firstScoped⟩
      simp only [failed]
  | none =>
      simp only [failed] at exactRun
      obtain ⟨address, value, pointer, read, same⟩ := exactRun
      subst out
      obtain ⟨secondProtected, finalBounded, finalScoped⟩ := declared_temporary_frame_profile
        firstBounded firstScoped secondFresh (Nat.le_refl _) (encodeValue value)
      refine ⟨⟨.ok value, sourceRaw.state⟩,
        (source_reference_location_read_exact sourceRaw _).mpr ?_,
        ⟨rawRelated.state, failed, rfl, declared_temporary_atom interface _ _ _ type (encodeValue value)⟩,
        temporary_protection_trans firstProtected
          (temporary_protection_weaken firstFresh.le secondProtected), finalBounded, finalScoped⟩
      simpa only [failed] using ⟨address, value, pointer, read, rfl⟩

theorem stateful_checked_raw_reference_read_preservation {SourceWorld TargetWorld : Type}
    {interface : Interface} {worldRelated : SourceWorld → TargetWorld → Prop}
    {sourceRaw : SourceRawResult SourceWorld} {targetRaw : TargetRawResult TargetWorld}
    {heap : TargetHeapSemantics TargetWorld} {calls : TargetCalls TargetWorld} {result : NativeType}
    {frame : TargetFrame} {state : TargetState TargetWorld} {operation : NativeIR.MemoryOperation}
    (rawRelated : RawResultRelated worldRelated sourceRaw targetRaw)
    (callExact : ∀ other, TargetMemoryCall interface heap frame operation state other ↔ other = targetRaw)
    (supply : NativeIR.Supply) (type : NativeType) {default : TargetValue}
    (bounded : TemporaryNamesBound frame supply.next) (hscope : TemporariesScoped frame)
    (zero : TargetZero interface result default) (root : List Instruction)
    {sourceOut : SourceOutcome SourceWorld}
    (read : ∃ location, sourceReferenceLocation sourceRaw location ∧
      sourceLocationNext location (fun address post => ∃ value,
        sourceRead post.memory address = some value ∧ sourceOut = ⟨.ok value, post⟩) sourceOut) :
    ∃ out,
      TargetRun interface heap calls result root
        [.helper (some (.temporary (NativeIR.fresh supply).1 (.ref type))) operation, .checkContext,
          .temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 type
            (.indirectRead (.temporary (NativeIR.fresh supply).1 (.ref type)))] frame state out ∧
      CheckedExpressionRelated worldRelated interface default
        (.temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 type) sourceOut out ∧
      TemporaryProtection supply.next frame out.frame ∧
      TemporaryNamesBound out.frame (NativeIR.fresh (NativeIR.fresh supply).2).2.next ∧
      TemporariesScoped out.frame := by
  have firstFresh := NativeIR.fresh_strict supply
  have secondFresh := NativeIR.fresh_strict (NativeIR.fresh supply).2
  have firstBounded := declared_temporary_bound bounded firstFresh.le (Nat.le_refl _) targetRaw.value
  have exactRead := (source_reference_location_read_exact sourceRaw sourceOut).mp read
  have existsRun : ∃ out, TargetRun interface heap calls result root
      [.helper (some (.temporary (NativeIR.fresh supply).1 (.ref type))) operation, .checkContext,
        .temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 type
          (.indirectRead (.temporary (NativeIR.fresh supply).1 (.ref type)))] frame state out := by
    cases failed : sourceRaw.state.fault with
    | some fault =>
        refine ⟨⟨.returned default, targetDeclareTemporary frame (NativeIR.fresh supply).1 targetRaw.value,
          targetRaw.state⟩, (target_raw_reference_read_exact rawRelated callExact
          (temporary_bound_fresh bounded firstFresh) (temporary_bound_fresh firstBounded secondFresh)
          zero root _).mpr ?_⟩
        simp only [failed]
    | none =>
        simp only [failed] at exactRead
        obtain ⟨address, value, pointer, selected, _⟩ := exactRead
        refine ⟨⟨.normal, targetDeclareTemporary
            (targetDeclareTemporary frame (NativeIR.fresh supply).1 targetRaw.value)
            (NativeIR.fresh (NativeIR.fresh supply).2).1 (encodeValue value), targetRaw.state⟩,
          (target_raw_reference_read_exact rawRelated callExact
            (temporary_bound_fresh bounded firstFresh) (temporary_bound_fresh firstBounded secondFresh)
            zero root _).mpr ?_⟩
        simpa only [failed] using ⟨address, value, pointer, selected, rfl⟩
  obtain ⟨out, ran⟩ := existsRun
  obtain ⟨reflected, reflectedRead, checked, protection, finalBounded, finalScoped⟩ :=
    stateful_checked_raw_reference_read_profile rawRelated callExact supply type bounded hscope zero root ran
  cases source_reference_location_read_unique read reflectedRead
  exact ⟨out, ran, checked, protection, finalBounded, finalScoped⟩

theorem source_index_primitive_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (array index : Expr) (element : NativeType) (pointer : Option Address)
    (length offset : NativeWord64.Word) (state : SourceState World) (out : SourceOutcome World) :
    sourcePrimitive interface heap calls frame (.index array index)
      [.array element pointer length, .word offset] state out ↔
      match (sourceIndexCall state length (heap.width element) offset pointer).state.fault with
      | some fault => out = ⟨.error fault, (sourceIndexCall state length (heap.width element) offset pointer).state⟩
      | none => ∃ address value,
          (sourceIndexCall state length (heap.width element) offset pointer).value = .reference (some address) ∧
          sourceRead (sourceIndexCall state length (heap.width element) offset pointer).state.memory address = some value ∧
          out = ⟨.ok value, (sourceIndexCall state length (heap.width element) offset pointer).state⟩ :=
  source_reference_location_read_exact _ _

theorem source_index_primitive_unique {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {array index : Expr} {element : NativeType} {pointer : Option Address}
    {length offset : NativeWord64.Word} {state : SourceState World} {left right : SourceOutcome World}
    (one : sourcePrimitive interface heap calls frame (.index array index)
      [.array element pointer length, .word offset] state left)
    (two : sourcePrimitive interface heap calls frame (.index array index)
      [.array element pointer length, .word offset] state right) : left = right :=
  source_reference_location_read_unique one two

theorem stateful_index_primitive_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld)
    (result : NativeType) (default : TargetValue) (zero : TargetZero interface result default)
    (array index : Expr) (type : NativeType)
    (width : targetHeap.width type = NativeWord64.encode (sourceHeap.width type))
    (arrayTagged : ∀ before post value,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame array before ⟨.ok value, post⟩ →
      SourceOuterTag (.array type) value)
    (indexTagged : ∀ before post value,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame index before ⟨.ok value, post⟩ →
      SourceOuterTag .word value)
    (first second : NativeLowering.Expression) :
    StatefulPrimitiveLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.index array index) [array, index]
      ⟨first.code ++ second.code, [first.result, second.result], second.supply⟩
      ⟨[.helper (some (.temporary (NativeIR.fresh second.supply).1 (.ref type)))
          (.index first.result second.result type), .checkContext] ++
          (NativeLowering.pureTemporary (NativeIR.fresh second.supply).2 type
            (.indirectRead (.temporary (NativeIR.fresh second.supply).1 (.ref type)))).code,
        (NativeLowering.pureTemporary (NativeIR.fresh second.supply).2 type
            (.indirectRead (.temporary (NativeIR.fresh second.supply).1 (.ref type)))).result,
        (NativeIR.fresh (NativeIR.fresh second.supply).2).2⟩ := by
  have firstFresh := NativeIR.fresh_strict second.supply
  have secondFresh := NativeIR.fresh_strict (NativeIR.fresh second.supply).2
  refine ⟨⟨firstFresh.le.trans secondFresh.le, Nat.le_refl _⟩, ?_, ?_⟩
  · intro root values middle argsRan _ frame target _ states bounded hscope reads sourceOut primitiveRan
    obtain ⟨arrayValue, indexValue, same, arrayRead, indexRead⟩ := target_two_encoded_arguments reads
    subst values
    obtain ⟨between, firstRan, tailRan⟩ := (source_arguments_cons_success_exact array [index]
      source middle arrayValue [indexValue]).mp argsRan
    have secondRan := (source_single_argument_success_exact index between middle indexValue).mp tailRan
    cases arrayTagged source between arrayValue firstRan with
    | array element pointer length =>
      cases indexTagged between middle indexValue secondRan with
      | word offset =>
        have rawRelated := index_call_correspondence states length (sourceHeap.width type) offset pointer
        have callExact := target_index_call_exact (heap := targetHeap) arrayRead indexRead
        simp only [width] at callExact
        exact stateful_checked_raw_reference_read_preservation rawRelated callExact second.supply type
          bounded hscope zero root primitiveRan
  · intro root values middle argsRan _ frame target _ states bounded hscope reads out ran
    obtain ⟨arrayValue, indexValue, same, arrayRead, indexRead⟩ := target_two_encoded_arguments reads
    subst values
    obtain ⟨between, firstRan, tailRan⟩ := (source_arguments_cons_success_exact array [index]
      source middle arrayValue [indexValue]).mp argsRan
    have secondRan := (source_single_argument_success_exact index between middle indexValue).mp tailRan
    cases arrayTagged source between arrayValue firstRan with
    | array element pointer length =>
      cases indexTagged between middle indexValue secondRan with
      | word offset =>
        have rawRelated := index_call_correspondence states length (sourceHeap.width type) offset pointer
        have callExact := target_index_call_exact (heap := targetHeap) arrayRead indexRead
        simp only [width] at callExact
        exact stateful_checked_raw_reference_read_profile rawRelated callExact second.supply type
          bounded hscope zero root ran

theorem stateful_index_child_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld) (clear : source.fault = none)
    (result : NativeType) (default : TargetValue) (zero : TargetZero interface result default)
    (array index : Expr)
    (arrayChildren : ∀ before, before.fault = none →
      StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
        sourceFrame before result default array)
    (indexChildren : ∀ before, before.fault = none →
      StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
        sourceFrame before result default index)
    (width : ∀ type, inferExpr interface (sourceFrameScope sourceFrame) array = some (.array type) →
      targetHeap.width type = NativeWord64.encode (sourceHeap.width type))
    (arrayTagged : ∀ before post value type,
      inferExpr interface (sourceFrameScope sourceFrame) array = some (.array type) →
      SourceExprEval interface sourceHeap sourceCalls sourceFrame array before ⟨.ok value, post⟩ →
      SourceOuterTag (.array type) value)
    (indexTagged : ∀ before post value,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame index before ⟨.ok value, post⟩ →
      SourceOuterTag .word value) :
    StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.index array index) := by
  apply stateful_strict_child_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
    sourceFrame source clear result default (.index array index) [array, index] rfl
    (fun child member before ready => by
      rcases List.mem_cons.mp member with equal | tail
      · subst child; exact arrayChildren before ready
      · cases List.mem_singleton.mp tail; exact indexChildren before ready)
  intro supply output compiled
  obtain ⟨type, first, second, typing, firstCompiled, secondCompiled, same⟩ :=
    read_index_combined_lowering_exact compiled
  obtain ⟨arrayTyped, _⟩ := read_index_inferred typing
  refine ⟨⟨first.code ++ second.code, [first.result, second.result], second.supply⟩,
    _, arguments_lowering_pair interface (sourceFrameScope sourceFrame) array index firstCompiled secondCompiled,
    same, stateful_index_primitive_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default zero array index type (width type arrayTyped)
      (fun before post value ran => arrayTagged before post value type arrayTyped ran) indexTagged first second⟩


theorem stateful_checked_array_descriptor_profile {SourceWorld TargetWorld : Type}
    {interface : Interface} {worldRelated : SourceWorld → TargetWorld → Prop}
    {sourceRaw : SourceRawResult SourceWorld} {targetRaw : TargetRawResult TargetWorld}
    {heap : TargetHeapSemantics TargetWorld} {calls : TargetCalls TargetWorld} {result : NativeType}
    {frame : TargetFrame} {state : TargetState TargetWorld} {operation : NativeIR.MemoryOperation}
    (rawRelated : RawResultRelated worldRelated sourceRaw targetRaw)
    (pointer : Option Address) (sourceReference : sourceRaw.value = .reference pointer)
    (supply : NativeIR.Supply) (element : NativeType) (length : NativeWord64.Word)
    (lengthAtom : Atom) {default : TargetValue}
    (callExact : ∀ other, TargetMemoryCall interface heap
      (targetDeclareTemporary frame (NativeIR.fresh supply).1 (.array element none 0))
      operation state other ↔ other = targetRaw)
    (countRead : TargetAtomEval interface frame state lengthAtom (.word (NativeWord64.encode length)))
    (bounded : TemporaryNamesBound frame supply.next) (hscope : TemporariesScoped frame)
    (zero : TargetZero interface result default) (root : List Instruction)
    {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface heap calls result root
      [.temporary (NativeIR.fresh supply).1 (.array element) (.zero (.array element)),
        .helper (some (.arrayData (.temporary (NativeIR.fresh supply).1 (.array element)) element)) operation,
        .checkContext, .assign (.arrayLength (.temporary (NativeIR.fresh supply).1 (.array element))) lengthAtom]
      frame state out) :
    CheckedExpressionRelated worldRelated interface default
      (.temporary (NativeIR.fresh supply).1 (.array element))
      (sourceObserve sourceRaw.state (.array element pointer length)) out ∧
      TemporaryProtection supply.next frame out.frame ∧
      TemporaryNamesBound out.frame (NativeIR.fresh supply).2.next ∧ TemporariesScoped out.frame := by
  have fresh := NativeIR.fresh_strict supply
  have rawReference : targetRaw.value = .reference pointer := by
    simpa only [sourceReference, encodeValue] using rawRelated.value
  have exactRun := (target_fresh_array_descriptor_exact supply element targetRaw rawReference
    callExact bounded countRead zero root out).mp ran
  obtain ⟨initialProtected, initialBounded, initialScoped⟩ := declared_temporary_frame_profile
    bounded hscope fresh (Nat.le_refl _) (.array element none 0)
  have live : (targetDeclareTemporary frame (NativeIR.fresh supply).1
      (.array element none 0)).temporaryNames.contains (NativeIR.fresh supply).1 = true := by
    change ((NativeIR.fresh supply).1 :: frame.temporaryNames).contains (NativeIR.fresh supply).1 = true
    exact List.contains_iff_mem.mpr (List.mem_cons_self ..)
  obtain ⟨dataProtected, dataBounded, dataScoped⟩ := updated_temporary_frame_profile
    initialBounded initialScoped live fresh (.array element pointer 0)
  cases failed : sourceRaw.state.fault with
  | some fault =>
      rw [rawRelated.state.fault.trans failed] at exactRun
      subst out
      refine ⟨?_, temporary_protection_trans initialProtected dataProtected, dataBounded, dataScoped⟩
      change CheckedResultRelated worldRelated default
        (sourceObserve sourceRaw.state (.array element pointer length)).result
        (sourceObserve sourceRaw.state (.array element pointer length)).state _ _
      rw [sourceObserve, failed]
      exact ⟨rawRelated.state, failed, rfl⟩
  | none =>
      rw [rawRelated.state.fault.trans failed] at exactRun
      subst out
      obtain ⟨lengthProtected, lengthBounded, lengthScoped⟩ := updated_temporary_frame_profile
        dataBounded dataScoped live fresh (.array element pointer (NativeWord64.encode length))
      refine ⟨?_, temporary_protection_trans initialProtected
        (temporary_protection_trans dataProtected lengthProtected), lengthBounded, lengthScoped⟩
      have answer := updated_temporary_atom interface
        (targetUpdateTemporary
          (targetDeclareTemporary frame (NativeIR.fresh supply).1 (.array element none 0))
          (NativeIR.fresh supply).1 (.array element pointer 0)) targetRaw.state
        (NativeIR.fresh supply).1 (.array element)
        (.array element pointer (NativeWord64.encode length)) live
      have related : CheckedResultRelated worldRelated default
          (.ok (.array element pointer length)) sourceRaw.state
          ⟨.normal, targetUpdateTemporary
            (targetUpdateTemporary
              (targetDeclareTemporary frame (NativeIR.fresh supply).1 (.array element none 0))
              (NativeIR.fresh supply).1 (.array element pointer 0))
            (NativeIR.fresh supply).1 (.array element pointer (NativeWord64.encode length)), targetRaw.state⟩
          (fun value after post => TargetAtomEval interface after post
            (.temporary (NativeIR.fresh supply).1 (.array element)) (encodeValue value)) :=
        ⟨rawRelated.state, failed, rfl, answer⟩
      change CheckedResultRelated worldRelated default
        (sourceObserve sourceRaw.state (.array element pointer length)).result
        (sourceObserve sourceRaw.state (.array element pointer length)).state _ _
      rw [sourceObserve, failed]
      exact related

theorem source_slice_primitive_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (array start count : Expr) (element : NativeType) (pointer resultPointer : Option Address)
    (length first amount : NativeWord64.Word) (state : SourceState World)
    (reference : (sourceSliceCall state length (heap.width element) first amount pointer).value =
      .reference resultPointer) (out : SourceOutcome World) :
    sourcePrimitive interface heap calls frame (.slice array start count)
      [.array element pointer length, .word first, .word amount] state out ↔
      out = sourceObserve (sourceSliceCall state length (heap.width element) first amount pointer).state
        (.array element resultPointer amount) := by
  simp only [sourcePrimitive]
  cases failed : (sourceSliceCall state length (heap.width element) first amount pointer).state.fault with
  | some fault => simp only [sourceObserve, failed]
  | none =>
      simp only [sourceObserve, failed]
      constructor
      · rintro ⟨other, otherReference, same⟩
        cases SourceValue.reference.inj (reference.symm.trans otherReference)
        exact same
      · intro same; exact ⟨resultPointer, reference, same⟩

theorem stateful_checked_array_descriptor_preservation {SourceWorld TargetWorld : Type}
    {interface : Interface} {worldRelated : SourceWorld → TargetWorld → Prop}
    {sourceRaw : SourceRawResult SourceWorld} {targetRaw : TargetRawResult TargetWorld}
    {heap : TargetHeapSemantics TargetWorld} {calls : TargetCalls TargetWorld} {result : NativeType}
    {frame : TargetFrame} {state : TargetState TargetWorld} {operation : NativeIR.MemoryOperation}
    (rawRelated : RawResultRelated worldRelated sourceRaw targetRaw)
    (pointer : Option Address) (sourceReference : sourceRaw.value = .reference pointer)
    (supply : NativeIR.Supply) (element : NativeType) (length : NativeWord64.Word)
    (lengthAtom : Atom) {default : TargetValue}
    (callExact : ∀ other, TargetMemoryCall interface heap
      (targetDeclareTemporary frame (NativeIR.fresh supply).1 (.array element none 0))
      operation state other ↔ other = targetRaw)
    (countRead : TargetAtomEval interface frame state lengthAtom (.word (NativeWord64.encode length)))
    (bounded : TemporaryNamesBound frame supply.next) (hscope : TemporariesScoped frame)
    (zero : TargetZero interface result default) (root : List Instruction) :
    ∃ out,
      TargetRun interface heap calls result root
        [.temporary (NativeIR.fresh supply).1 (.array element) (.zero (.array element)),
          .helper (some (.arrayData (.temporary (NativeIR.fresh supply).1 (.array element)) element)) operation,
          .checkContext, .assign (.arrayLength (.temporary (NativeIR.fresh supply).1 (.array element))) lengthAtom]
        frame state out ∧
      CheckedExpressionRelated worldRelated interface default
        (.temporary (NativeIR.fresh supply).1 (.array element))
        (sourceObserve sourceRaw.state (.array element pointer length)) out ∧
      TemporaryProtection supply.next frame out.frame ∧
      TemporaryNamesBound out.frame (NativeIR.fresh supply).2.next ∧ TemporariesScoped out.frame := by
  have rawReference : targetRaw.value = .reference pointer := by
    simpa only [sourceReference, encodeValue] using rawRelated.value
  have exactRun := target_fresh_array_descriptor_exact (calls := calls) supply element targetRaw rawReference
    callExact bounded countRead zero root
  have existsRun : ∃ out,
      TargetRun interface heap calls result root
        [.temporary (NativeIR.fresh supply).1 (.array element) (.zero (.array element)),
          .helper (some (.arrayData (.temporary (NativeIR.fresh supply).1 (.array element)) element)) operation,
          .checkContext, .assign (.arrayLength (.temporary (NativeIR.fresh supply).1 (.array element))) lengthAtom]
        frame state out := by
    cases failed : targetRaw.state.fault with
    | some fault => exact ⟨_, (exactRun _).mpr rfl⟩
    | none => exact ⟨_, (exactRun _).mpr rfl⟩
  obtain ⟨out, ran⟩ := existsRun
  exact ⟨out, ran, stateful_checked_array_descriptor_profile rawRelated pointer sourceReference
    supply element length lengthAtom callExact countRead bounded hscope zero root ran⟩

theorem stateful_slice_primitive_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld)
    (result : NativeType) (default : TargetValue) (zero : TargetZero interface result default)
    (array start count : Expr) (type : NativeType)
    (width : targetHeap.width type = NativeWord64.encode (sourceHeap.width type))
    (arrayTagged : ∀ before post value,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame array before ⟨.ok value, post⟩ →
      SourceOuterTag (.array type) value)
    (startTagged : ∀ before post value,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame start before ⟨.ok value, post⟩ →
      SourceOuterTag .word value)
    (countTagged : ∀ before post value,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame count before ⟨.ok value, post⟩ →
      SourceOuterTag .word value)
    (first second third : NativeLowering.Expression) :
    StatefulPrimitiveLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.slice array start count) [array, start, count]
      ⟨first.code ++ second.code ++ third.code, [first.result, second.result, third.result], third.supply⟩
      ⟨[.temporary (NativeIR.fresh third.supply).1 (.array type) (.zero (.array type)),
          .helper (some (.arrayData (.temporary (NativeIR.fresh third.supply).1 (.array type)) type))
            (.slice first.result second.result third.result type),
          .checkContext, .assign (.arrayLength (.temporary (NativeIR.fresh third.supply).1 (.array type))) third.result],
        .temporary (NativeIR.fresh third.supply).1 (.array type), (NativeIR.fresh third.supply).2⟩ := by
  have fresh := NativeIR.fresh_strict third.supply
  refine ⟨⟨fresh.le, Nat.le_refl _⟩, ?_, ?_⟩
  · intro root values middle argsRan _ frame target _ states bounded hscope reads sourceOut primitiveRan
    obtain ⟨arrayValue, startValue, countValue, same, arrayRead, startRead, countRead⟩ := target_three_encoded_arguments reads
    subst values
    obtain ⟨afterArray, firstRan, tailRan⟩ := (source_arguments_cons_success_exact array [start, count]
      source middle arrayValue [startValue, countValue]).mp argsRan
    obtain ⟨afterStart, secondRan, tailRan⟩ := (source_arguments_cons_success_exact start [count]
      afterArray middle startValue [countValue]).mp tailRan
    have thirdRan := (source_single_argument_success_exact count afterStart middle countValue).mp tailRan
    cases arrayTagged source afterArray arrayValue firstRan with
    | array element pointer length =>
      cases startTagged afterArray afterStart startValue secondRan with
      | word offset =>
        cases countTagged afterStart middle countValue thirdRan with
        | word amount =>
          have rawRelated := slice_call_correspondence states length (sourceHeap.width type) offset amount pointer
          have savedOperands := declare_temporary_protects frame (.array type none 0) fresh
          have newArrayRead := (protection_atom_evaluation savedOperands first.result
            (target_atom_read_within bounded arrayRead) target target _).mp arrayRead
          have newStartRead := (protection_atom_evaluation savedOperands second.result
            (target_atom_read_within bounded startRead) target target _).mp startRead
          have newCountRead := (protection_atom_evaluation savedOperands third.result
            (target_atom_read_within bounded countRead) target target _).mp countRead
          have callExact := target_slice_call_exact (heap := targetHeap) newArrayRead newStartRead newCountRead
          simp only [width] at callExact
          obtain ⟨resultPointer, reference⟩ := source_slice_call_reference middle length (sourceHeap.width type) offset amount pointer
          cases (source_slice_primitive_exact interface sourceHeap sourceCalls sourceFrame array start count
            type pointer resultPointer length offset amount middle reference sourceOut).mp primitiveRan
          exact stateful_checked_array_descriptor_preservation rawRelated resultPointer reference
            third.supply type amount third.result callExact countRead bounded hscope zero root
  · intro root values middle argsRan _ frame target _ states bounded hscope reads out ran
    obtain ⟨arrayValue, startValue, countValue, same, arrayRead, startRead, countRead⟩ := target_three_encoded_arguments reads
    subst values
    obtain ⟨afterArray, firstRan, tailRan⟩ := (source_arguments_cons_success_exact array [start, count]
      source middle arrayValue [startValue, countValue]).mp argsRan
    obtain ⟨afterStart, secondRan, tailRan⟩ := (source_arguments_cons_success_exact start [count]
      afterArray middle startValue [countValue]).mp tailRan
    have thirdRan := (source_single_argument_success_exact count afterStart middle countValue).mp tailRan
    cases arrayTagged source afterArray arrayValue firstRan with
    | array element pointer length =>
      cases startTagged afterArray afterStart startValue secondRan with
      | word offset =>
        cases countTagged afterStart middle countValue thirdRan with
        | word amount =>
          have rawRelated := slice_call_correspondence states length (sourceHeap.width type) offset amount pointer
          have savedOperands := declare_temporary_protects frame (.array type none 0) fresh
          have newArrayRead := (protection_atom_evaluation savedOperands first.result
            (target_atom_read_within bounded arrayRead) target target _).mp arrayRead
          have newStartRead := (protection_atom_evaluation savedOperands second.result
            (target_atom_read_within bounded startRead) target target _).mp startRead
          have newCountRead := (protection_atom_evaluation savedOperands third.result
            (target_atom_read_within bounded countRead) target target _).mp countRead
          have callExact := target_slice_call_exact (heap := targetHeap) newArrayRead newStartRead newCountRead
          simp only [width] at callExact
          obtain ⟨resultPointer, reference⟩ := source_slice_call_reference middle length (sourceHeap.width type) offset amount pointer
          refine ⟨sourceObserve
            (sourceSliceCall middle length (sourceHeap.width type) offset amount pointer).state
            (.array type resultPointer amount), ?_, ?_⟩
          · exact (source_slice_primitive_exact interface sourceHeap sourceCalls sourceFrame array start count
              type pointer resultPointer length offset amount middle reference _).mpr rfl
          · exact stateful_checked_array_descriptor_profile rawRelated resultPointer reference
              third.supply type amount third.result callExact countRead bounded hscope zero root ran

theorem stateful_slice_child_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld) (clear : source.fault = none)
    (result : NativeType) (default : TargetValue) (zero : TargetZero interface result default)
    (array start count : Expr)
    (arrayChildren : ∀ before, before.fault = none →
      StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
        sourceFrame before result default array)
    (startChildren : ∀ before, before.fault = none →
      StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
        sourceFrame before result default start)
    (countChildren : ∀ before, before.fault = none →
      StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
        sourceFrame before result default count)
    (width : ∀ type, inferExpr interface (sourceFrameScope sourceFrame) array = some (.array type) →
      targetHeap.width type = NativeWord64.encode (sourceHeap.width type))
    (arrayTagged : ∀ before post value type,
      inferExpr interface (sourceFrameScope sourceFrame) array = some (.array type) →
      SourceExprEval interface sourceHeap sourceCalls sourceFrame array before ⟨.ok value, post⟩ →
      SourceOuterTag (.array type) value)
    (startTagged : ∀ before post value,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame start before ⟨.ok value, post⟩ →
      SourceOuterTag .word value)
    (countTagged : ∀ before post value,
      SourceExprEval interface sourceHeap sourceCalls sourceFrame count before ⟨.ok value, post⟩ →
      SourceOuterTag .word value) :
    StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default (.slice array start count) := by
  apply stateful_strict_child_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
    sourceFrame source clear result default (.slice array start count) [array, start, count] rfl
    (fun child member before ready => by
      rcases List.mem_cons.mp member with equal | tail
      · subst child; exact arrayChildren before ready
      · rcases List.mem_cons.mp tail with equal | tail
        · subst child; exact startChildren before ready
        · cases List.mem_singleton.mp tail; exact countChildren before ready)
  intro supply output compiled
  obtain ⟨type, first, second, third, typing, firstCompiled, secondCompiled, thirdCompiled, same⟩ :=
    read_slice_combined_lowering_exact compiled
  obtain ⟨arrayTyped, _, _⟩ := read_slice_inferred typing
  refine ⟨⟨first.code ++ second.code ++ third.code, [first.result, second.result, third.result], third.supply⟩,
    _, arguments_lowering_triple interface (sourceFrameScope sourceFrame) array start count
      firstCompiled secondCompiled thirdCompiled,
    ?_, stateful_slice_primitive_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default zero array start count type (width type arrayTyped)
      (fun before post value ran => arrayTagged before post value type arrayTyped ran)
      startTagged countTagged first second third⟩
  simpa only [NativeLowering.pureTemporary, List.cons_append, List.nil_append] using same

end Mettapedia.GSLT.LanguageDef.NativeOps
