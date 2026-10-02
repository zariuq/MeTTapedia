import Mettapedia.GSLT.LanguageDef.NativeOpsTemporaryFrames
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsScalarObservation

/-!
# Actual lowering of pure source leaves

The source and target relations are evaluated independently. Successful
admission fixes the emitted operation; both-direction laws include local
reads, record zeros and nullable references. Private-result freshness is a
separate compilation invariant. These leaves preserve the whole runtime
state and do not suppress an existing context fault.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Atom)
open NativeWord64 (Word)

inductive SourceLeaf : Expr → Prop where
  | word (value : Word) : SourceLeaf (.word value)
  | byte (value : NativeWord64.Byte) : SourceLeaf (.byte value)
  | bool (value : Bool) : SourceLeaf (.bool value)
  | variable (name : String) : SourceLeaf (.variable name)
  | zero (type : NativeType) : SourceLeaf (.zero type)
  | nullReference (element : NativeType) : SourceLeaf (.null (.ref element))

theorem source_leaf_has_no_operands {expression : Expr} (leaf : SourceLeaf expression) :
    sourceStrictOperands? expression = some [] := by
  cases leaf <;> rfl

private theorem constant_leaf_pure_equivalence {World : Type} {interface : Interface}
    {frame : TargetFrame} {target : TargetState World} {operation : NativeIR.PureOperation}
    {SourceWorld : Type} (source : SourceState SourceWorld) (value : SourceValue)
    (computed : TargetPureEval interface frame target operation (encodeValue value))
    (out : SourceOutcome SourceWorld) :
    out = ⟨.ok value, source⟩ ↔
      ∃ actual, out = ⟨.ok actual, source⟩ ∧
        TargetPureEval interface frame target operation (encodeValue actual) := by
  constructor
  · intro same; exact ⟨value, same, computed⟩
  · rintro ⟨actual, same, otherComputed⟩
    have equal : actual = value := encodeValue_injective (target_pure_unique otherComputed computed)
    subst actual; exact same

theorem local_pure_read_correspondence {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target) (name : String) (value : SourceValue) :
    TargetPureEval interface targetFrame target (.readLocal name) (encodeValue value) ↔
      sourceLocalValue sourceFrame source name = some value := by
  constructor
  · intro computed
    cases computed with
    | «local» read =>
        rw [local_value_correspondence frames states] at read
        obtain ⟨actual, selected, same⟩ := Option.map_eq_some_iff.mp read
        cases encodeValue_injective same
        exact selected
  · intro read
    apply TargetPureEval.local
    rw [local_value_correspondence frames states, read]
    rfl

theorem zero_pure_read_correspondence {World : Type} (interface : Interface)
    (frame : TargetFrame) (state : TargetState World) (type : NativeType) (value : SourceValue) :
    TargetPureEval interface frame state (.zero type) (encodeValue value) ↔
      SourceZero interface type value := by
  constructor
  · intro computed
    cases computed with
    | zero initialized => exact (zero_correspondence interface type value).mp initialized
  · intro initialized; exact .zero (zero_preservation initialized)

theorem actual_leaf_operation_correspondence {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    {expression : Expr} (leaf : SourceLeaf expression) (scope : Scope)
    (supply : NativeIR.Supply) (output : NativeLowering.Expression)
    (compiled : NativeLowering.expression? interface scope expression supply = some output) :
    ∃ type operation, output = NativeLowering.pureTemporary supply type operation ∧
      ∀ out, sourcePrimitive interface sourceHeap sourceCalls sourceFrame expression [] source out ↔
        ∃ value, out = ⟨.ok value, source⟩ ∧
          TargetPureEval interface targetFrame target operation (encodeValue value) := by
  cases leaf with
  | word value =>
      simp only [NativeLowering.expression?, inferExpr] at compiled
      cases Option.some.inj compiled
      refine ⟨.word, .word (NativeWord64.encode value), rfl, ?_⟩
      intro out
      exact constant_leaf_pure_equivalence source (.word value) (.word _) out
  | byte value =>
      simp only [NativeLowering.expression?, inferExpr] at compiled
      cases Option.some.inj compiled
      refine ⟨.byte, .byte (NativeWord64.encode value), rfl, ?_⟩
      intro out
      exact constant_leaf_pure_equivalence source (.byte value) (.byte _) out
  | bool value =>
      simp only [NativeLowering.expression?, inferExpr] at compiled
      cases Option.some.inj compiled
      refine ⟨.bool, .bool value, rfl, ?_⟩
      intro out
      exact constant_leaf_pure_equivalence source (.bool value) (.bool _) out
  | «variable» name =>
      cases admitted : lookupVariable scope name with
      | none => simp only [NativeLowering.expression?, inferExpr, admitted] at compiled; cases compiled
      | some type =>
          simp only [NativeLowering.expression?, inferExpr, admitted] at compiled
          cases Option.some.inj compiled
          refine ⟨type, .readLocal name, rfl, ?_⟩
          intro out
          change (∃ value, sourceLocalValue sourceFrame source name = some value ∧
            out = ⟨.ok value, source⟩) ↔ _
          constructor
          · rintro ⟨value, read, same⟩
            exact ⟨value, same, (local_pure_read_correspondence frames states name value).mpr read⟩
          · rintro ⟨value, same, read⟩
            exact ⟨value, (local_pure_read_correspondence frames states name value).mp read, same⟩
  | zero type =>
      by_cases valid : validType interface type true = true
      · simp only [NativeLowering.expression?, inferExpr, valid, if_true] at compiled
        cases Option.some.inj compiled
        refine ⟨type, .zero type, rfl, ?_⟩
        intro out
        change (∃ value, SourceZero interface type value ∧ out = ⟨.ok value, source⟩) ↔ _
        constructor
        · rintro ⟨value, initialized, same⟩
          exact ⟨value, same, .zero (zero_preservation initialized)⟩
        · rintro ⟨value, same, initialized⟩
          exact ⟨value, (zero_pure_read_correspondence _ _ _ _ _).mp initialized, same⟩
      · simp only [NativeLowering.expression?, inferExpr, valid] at compiled
        cases compiled
  | nullReference element =>
      by_cases valid : validType interface (.ref element) false = true
      · simp only [NativeLowering.expression?, inferExpr, valid, if_true] at compiled
        cases Option.some.inj compiled
        refine ⟨.ref element, .zero (.ref element), rfl, ?_⟩
        intro out
        exact constant_leaf_pure_equivalence source (.reference none) (.zero (.nullPointer _)) out
      · simp only [NativeLowering.expression?, inferExpr, valid] at compiled
        cases compiled

theorem actual_leaf_expression_run_exact {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target)
    {expression : Expr} (leaf : SourceLeaf expression) (scope : Scope)
    (supply : NativeIR.Supply) (output : NativeLowering.Expression)
    (compiled : NativeLowering.expression? interface scope expression supply = some output)
    (unused : targetFrame.temporaryNames.contains (NativeIR.fresh supply).1 = false)
    (result : NativeType) (root : List Instruction) (out : TargetBlockOutcome TargetWorld) :
    TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ↔
      ∃ value, SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source
        ⟨.ok value, source⟩ ∧
        out = ⟨.normal,
          targetDeclareTemporary targetFrame (NativeIR.fresh supply).1 (encodeValue value), target⟩ := by
  obtain ⟨type, operation, exactOutput, primitive⟩ :=
    actual_leaf_operation_correspondence sourceHeap sourceCalls frames states leaf scope supply output compiled
  subst output
  change TargetRun interface targetHeap targetCalls result root
    [.temporary (NativeIR.fresh supply).1 type operation] targetFrame target out ↔ _
  rw [target_pure_temporary_any_exact interface targetHeap targetCalls result root targetFrame target
    (NativeIR.fresh supply).1 type operation unused out]
  constructor
  · rintro ⟨value, computed, same⟩
    have encoded : TargetPureEval interface targetFrame target operation (encodeValue (decodeValue value)) := by
      rw [encode_decode_value]; exact computed
    have sourcePrimitive := (primitive ⟨.ok (decodeValue value), source⟩).mpr
      ⟨decodeValue value, rfl, encoded⟩
    refine ⟨decodeValue value,
      (source_operand_free_expression_exact expression (source_leaf_has_no_operands leaf) _ _).mpr
        sourcePrimitive, ?_⟩
    rw [encode_decode_value]
    exact same
  · rintro ⟨value, sourceRan, same⟩
    have sourcePrimitive :=
      (source_operand_free_expression_exact expression (source_leaf_has_no_operands leaf) _ _).mp sourceRan
    obtain ⟨actual, exactSource, computed⟩ := (primitive _).mp sourcePrimitive
    cases exactSource
    exact ⟨_, computed, same⟩

theorem actual_leaf_result_atom {interface : Interface} {expression : Expr}
    (leaf : SourceLeaf expression) (scope : Scope) (supply : NativeIR.Supply)
    (output : NativeLowering.Expression)
    (compiled : NativeLowering.expression? interface scope expression supply = some output) :
    ∃ type, output.result = .temporary (NativeIR.fresh supply).1 type := by
  cases leaf with
  | word | byte | bool =>
      simp only [NativeLowering.expression?, inferExpr] at compiled
      cases Option.some.inj compiled
      exact ⟨_, rfl⟩
  | «variable» name =>
      cases admitted : lookupVariable scope name with
      | none => simp only [NativeLowering.expression?, inferExpr, admitted] at compiled; cases compiled
      | some type =>
          simp only [NativeLowering.expression?, inferExpr, admitted] at compiled
          cases Option.some.inj compiled
          exact ⟨_, rfl⟩
  | zero type =>
      by_cases valid : validType interface type true = true
      · simp only [NativeLowering.expression?, inferExpr, valid, if_true] at compiled
        cases Option.some.inj compiled
        exact ⟨_, rfl⟩
      · simp only [NativeLowering.expression?, inferExpr, valid] at compiled
        cases compiled
  | nullReference element =>
      by_cases valid : validType interface (.ref element) false = true
      · simp only [NativeLowering.expression?, inferExpr, valid, if_true] at compiled
        cases Option.some.inj compiled
        exact ⟨_, rfl⟩
      · simp only [NativeLowering.expression?, inferExpr, valid] at compiled
        cases compiled

theorem actual_leaf_expression_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    {expression : Expr} (leaf : SourceLeaf expression) (scope : Scope)
    (supply : NativeIR.Supply) (output : NativeLowering.Expression)
    (compiled : NativeLowering.expression? interface scope expression supply = some output)
    (bounded : TemporaryNamesBound targetFrame supply.next)
    (result : NativeType) (root : List Instruction) {sourceOut : SourceOutcome SourceWorld}
    (sourceRan : SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source sourceOut) :
    ∃ out observed,
      TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      targetExpressionObservation interface output.result out observed ∧
      FrameRelated sourceFrame out.frame ∧ OutcomeRelated worldRelated sourceOut observed := by
  obtain ⟨_, _, _, primitive⟩ := actual_leaf_operation_correspondence sourceHeap sourceCalls
    frames states leaf scope supply output compiled
  have operation := (source_operand_free_expression_exact expression
    (source_leaf_has_no_operands leaf) source sourceOut).mp sourceRan
  obtain ⟨value, sourceExact, _⟩ := (primitive sourceOut).mp operation
  subst sourceOut
  have unused := temporary_bound_fresh bounded (NativeIR.fresh_strict supply)
  obtain ⟨type, atomShape⟩ := actual_leaf_result_atom leaf scope supply output compiled
  let frame := targetDeclareTemporary targetFrame (NativeIR.fresh supply).1 (encodeValue value)
  refine ⟨⟨.normal, frame, target⟩, targetObserve target (encodeValue value), ?_, ?_, ?_, ?_⟩
  · exact (actual_leaf_expression_run_exact sourceHeap sourceCalls targetHeap targetCalls frames states
      leaf scope supply output compiled unused result root _).mpr ⟨value, sourceRan, rfl⟩
  · change ∃ actual, TargetAtomEval interface frame target output.result actual ∧ _
    refine ⟨encodeValue value, ?_, rfl⟩
    rw [atomShape]
    exact declared_temporary_atom _ _ _ _ _ _
  · exact ⟨frames.storage, frames.nextLocal, frames.bindings⟩
  · simpa only [sourceObserve, clear] using observation_correspondence states value

theorem actual_leaf_expression_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame)
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    {expression : Expr} (leaf : SourceLeaf expression) (scope : Scope)
    (supply : NativeIR.Supply) (output : NativeLowering.Expression)
    (compiled : NativeLowering.expression? interface scope expression supply = some output)
    (bounded : TemporaryNamesBound targetFrame supply.next)
    (result : NativeType) (root : List Instruction)
    {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (targetRan : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out)
    (observation : targetExpressionObservation interface output.result out observed) :
    ∃ sourceOut, SourceExprEval interface sourceHeap sourceCalls sourceFrame expression source sourceOut ∧
      FrameRelated sourceFrame out.frame ∧ OutcomeRelated worldRelated sourceOut observed := by
  have unused := temporary_bound_fresh bounded (NativeIR.fresh_strict supply)
  obtain ⟨value, sourceRan, exactOut⟩ := (actual_leaf_expression_run_exact sourceHeap sourceCalls
    targetHeap targetCalls frames states leaf scope supply output compiled unused result root out).mp targetRan
  subst out
  obtain ⟨type, atomShape⟩ := actual_leaf_result_atom leaf scope supply output compiled
  rcases observation with ⟨actual, read, exactObserved⟩
  rw [atomShape] at read
  have encoded := declared_temporary_atom interface targetFrame target (NativeIR.fresh supply).1
    type (encodeValue value)
  cases target_atom_unique read encoded
  subst observed
  refine ⟨⟨.ok value, source⟩, sourceRan, ⟨frames.storage, frames.nextLocal, frames.bindings⟩, ?_⟩
  simpa only [sourceObserve, clear] using observation_correspondence states value

end Mettapedia.GSLT.LanguageDef.NativeOps
