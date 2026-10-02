import Mettapedia.GSLT.LanguageDef.NativeOpsShortCircuitCorrespondence
import Mettapedia.GSLT.LanguageDef.NativeOpsGuardedExpressionControls

/-! Controls for actual branch lowering, skipped reads, refusals and private scopes. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.ShortCircuitControls

open NativeIR (Instruction Atom)
open NativeWord64 (Fault)

def divisionTest : Expr :=
  .binary (.compare .eq) (GuardedExpressionControls.wordBinary .div 7 0) (.word 0)

def divisionTestOutput (base : Nat) : NativeLowering.Expression :=
  ⟨[.temporary (base + 1) .word (.word 7),
    .temporary (base + 2) .word (.word 0),
    .checkedNumericGuard .div (.temporary (base + 2) .word),
    .temporary (base + 3) .word (.binary (.word .div) (.temporary (base + 1) .word) (.temporary (base + 2) .word)),
    .temporary (base + 4) .word (.word 0),
    .temporary (base + 5) .bool (.binary (.compare .eq) (.temporary (base + 3) .word) (.temporary (base + 4) .word))],
    .temporary (base + 5) .bool, ⟨base + 5⟩⟩

theorem division_test_guarded : SourceGuardedExpression divisionTest :=
  .binary (.compare .eq) (GuardedExpressionControls.word_binary_guarded .div 7 0) (.leaf (.word 0))

theorem division_test_actual_emission (interface : Interface) (scope : Scope) (supply : NativeIR.Supply) :
    NativeLowering.expression? interface scope divisionTest supply = some (divisionTestOutput supply.next) := by
  simp [divisionTest, divisionTestOutput, GuardedExpressionControls.wordBinary,
    NativeLowering.expression?, NativeLowering.prependCode, NativeLowering.pureTemporary,
    NativeLowering.numericGuard, inferExpr, binaryType, NativeIR.fresh, Nat.add_assoc]
  exact ⟨rfl, rfl⟩

def guardedConnect (continueValue selected : Bool) : Expr :=
  .binary (shortCircuitBinary continueValue) (.bool selected) divisionTest

def guardedConnectOutput (continueValue selected : Bool) (supply : NativeIR.Supply) : NativeLowering.Expression :=
  shortCircuitOutput continueValue
    (NativeLowering.pureTemporary supply .bool (.bool selected))
    (divisionTestOutput (supply.next + 2))

theorem guarded_connect_supported (continueValue selected : Bool) :
    SourceShortCircuitExpression (guardedConnect continueValue selected) :=
  .connect continueValue (.guarded (.leaf (.bool selected))) (.guarded division_test_guarded)

theorem guarded_connect_actual_emission (interface : Interface) (scope : Scope)
    (continueValue selected : Bool) (supply : NativeIR.Supply) :
    NativeLowering.expression? interface scope (guardedConnect continueValue selected) supply =
      some (guardedConnectOutput continueValue selected supply) := by
  cases continueValue <;>
    simp [guardedConnect, guardedConnectOutput, shortCircuitBinary, shortCircuitOutput,
      shortCircuitCondition, NativeLowering.expression?, NativeLowering.prependCode,
      NativeLowering.pureTemporary, divisionTest, divisionTestOutput,
      GuardedExpressionControls.wordBinary, NativeLowering.numericGuard, inferExpr,
      binaryType, NativeIR.fresh, Nat.add_assoc]
  all_goals exact ⟨rfl, rfl⟩

private theorem bool_source_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (value : Bool) (state : SourceState World) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame (.bool value) state out ↔ out = ⟨.ok (.bool value), state⟩ :=
  source_operand_free_expression_exact _ rfl _ _

theorem literal_skip_source_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (continueValue : Bool) (right : Expr) (state : SourceState World) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame
      (.binary (shortCircuitBinary continueValue) (.bool (!continueValue)) right) state out ↔
      out = ⟨.ok (.bool (!continueValue)), state⟩ := by
  rw [source_short_circuit_exact]
  constructor
  · rintro (⟨post, leftRan, same⟩ | ⟨post, leftRan, _⟩ | ⟨fault, post, leftRan, _⟩)
    · cases (bool_source_exact interface heap calls frame (!continueValue) state _).mp leftRan
      exact same
    · have impossible := congrArg SourceOutcome.result
        ((bool_source_exact interface heap calls frame (!continueValue) state _).mp leftRan)
      cases continueValue <;> cases impossible
    · cases (bool_source_exact interface heap calls frame (!continueValue) state _).mp leftRan
  · intro same
    exact .inl ⟨state, (bool_source_exact interface heap calls frame (!continueValue) state _).mpr rfl, same⟩

theorem division_test_source_refuses {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (state : SourceState World) (clear : state.fault = none) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame divisionTest state out ↔
      out = ⟨.error .divisionByZero, sourcePoison state .divisionByZero⟩ := by
  have leftExact : ∀ childOut,
      SourceExprEval interface heap calls frame (GuardedExpressionControls.wordBinary .div 7 0) state childOut ↔
        childOut = ⟨.error .divisionByZero, sourcePoison state .divisionByZero⟩ := by
    intro childOut
    simpa only [show NativeWord64.sourceBinary .div 7 0 = .error .divisionByZero from rfl,
      sourceFinish, sourceObserve, sourcePoison, clear, Except.map] using
      GuardedExpressionControls.word_binary_source_exact interface heap calls frame .div 7 0 state clear childOut
  rw [show divisionTest = .binary (.compare .eq)
    (GuardedExpressionControls.wordBinary .div 7 0) (.word 0) from rfl,
    source_guarded_binary_exact (.compare .eq)
      (GuardedExpressionControls.word_binary_guarded .div 7 0) (.leaf (.word 0)) state clear out]
  constructor
  · rintro (⟨left, right, computed, leftRan, _, _, _⟩ | ⟨fault, leftRan, same⟩ |
      ⟨left, fault, leftRan, _, _⟩)
    · cases (leftExact _).mp leftRan
    · cases Except.error.inj (congrArg SourceOutcome.result ((leftExact _).mp leftRan))
      exact same
    · cases (leftExact _).mp leftRan
  · intro same
    exact .inr (.inl ⟨.divisionByZero, (leftExact _).mpr rfl, same⟩)

theorem literal_taken_source_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (continueValue : Bool) (right : Expr) (state : SourceState World) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame
      (.binary (shortCircuitBinary continueValue) (.bool continueValue) right) state out ↔
      SourceExprEval interface heap calls frame right state out := by
  rw [source_short_circuit_exact]
  constructor
  · rintro (⟨post, leftRan, _⟩ | ⟨post, leftRan, rightRan⟩ | ⟨fault, post, leftRan, _⟩)
    · have impossible := congrArg SourceOutcome.result
        ((bool_source_exact interface heap calls frame continueValue state _).mp leftRan)
      cases continueValue <;> cases impossible
    · cases (bool_source_exact interface heap calls frame continueValue state _).mp leftRan
      exact rightRan
    · cases (bool_source_exact interface heap calls frame continueValue state _).mp leftRan
  · intro rightRan
    exact .inr (.inl ⟨state, (bool_source_exact interface heap calls frame continueValue state _).mpr rfl, rightRan⟩)

/-- Both false conjunction and true disjunction execute without reaching the
real division guard on their right. This includes the complete target state. -/
theorem skip_division_executes {SourceWorld TargetWorld : Type}
    {related : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated related source target)
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    (bounded : TemporaryNamesBound targetFrame 0) (hscope : TemporariesScoped targetFrame)
    (root : List Instruction) (continueValue : Bool) :
    ∃ out observed,
      TargetRun interface targetHeap targetCalls .bool root
        (guardedConnectOutput continueValue (!continueValue) ⟨0⟩).code targetFrame target out ∧
      targetExpressionObservation interface (guardedConnectOutput continueValue (!continueValue) ⟨0⟩).result
        out observed ∧ out.state = target ∧ observed.result = .ok (.bool (!continueValue)) := by
  obtain ⟨out, observed, ran, observation, _, _, _, _, _, correspondence⟩ :=
    short_circuit_expression_preservation sourceHeap sourceCalls targetHeap targetCalls frames states clear tagged
      .bool TargetZero.boolean root (guarded_connect_supported continueValue (!continueValue))
      (guarded_connect_actual_emission interface (sourceFrameScope sourceFrame) continueValue (!continueValue) ⟨0⟩)
      bounded hscope
      ((literal_skip_source_exact interface sourceHeap sourceCalls sourceFrame continueValue divisionTest source _).mpr rfl)
  have laws := short_circuit_expression_laws related interface sourceHeap sourceCalls targetHeap targetCalls
    sourceFrame source clear tagged .bool TargetZero.boolean (guarded_connect_supported continueValue (!continueValue))
  obtain ⟨sourceOut, sourceRan, raw, _, _, _⟩ := laws.backward root
    (guarded_connect_actual_emission interface (sourceFrameScope sourceFrame) continueValue (!continueValue) ⟨0⟩)
    frames states bounded hscope ran
  cases (literal_skip_source_exact interface sourceHeap sourceCalls sourceFrame continueValue divisionTest source _).mp sourceRan
  exact ⟨out, observed, ran, observation, raw.2.2.1, correspondence.result⟩

theorem guarded_connect_no_extra_result {SourceWorld TargetWorld : Type}
    {related : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated related source target)
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    (bounded : TemporaryNamesBound targetFrame 0) (hscope : TemporariesScoped targetFrame)
    (root : List Instruction) (continueValue selected : Bool)
    {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls .bool root
      (guardedConnectOutput continueValue selected ⟨0⟩).code targetFrame target out)
    (observation : targetExpressionObservation interface (guardedConnectOutput continueValue selected ⟨0⟩).result
      out observed) :
    observed.result = if selected == continueValue then .error .divisionByZero else .ok (.bool selected) := by
  obtain ⟨sourceOut, sourceRan, _, _, _, _, _, correspondence⟩ := short_circuit_expression_reflection
    sourceHeap sourceCalls targetHeap targetCalls frames states clear tagged .bool TargetZero.boolean root
    (guarded_connect_supported continueValue selected)
    (guarded_connect_actual_emission interface (sourceFrameScope sourceFrame) continueValue selected ⟨0⟩)
    bounded hscope ran observation
  cases selected <;> cases continueValue
  all_goals
    first
    | cases (literal_skip_source_exact interface sourceHeap sourceCalls sourceFrame _ divisionTest source _).mp sourceRan
      exact correspondence.result
    | have rightRan := (literal_taken_source_exact interface sourceHeap sourceCalls sourceFrame _ divisionTest source _).mp sourceRan
      cases (division_test_source_refuses interface sourceHeap sourceCalls sourceFrame source clear _).mp rightRan
      exact correspondence.result

/-- Selecting the same right operand reaches the actual numeric guard and
returns the enclosing boolean zero with a division fault. -/
theorem taken_division_executes {SourceWorld TargetWorld : Type}
    {related : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated related source target)
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    (bounded : TemporaryNamesBound targetFrame 0) (hscope : TemporariesScoped targetFrame)
    (root : List Instruction) (continueValue : Bool) :
    ∃ out observed,
      TargetRun interface targetHeap targetCalls .bool root
        (guardedConnectOutput continueValue continueValue ⟨0⟩).code targetFrame target out ∧
      targetExpressionObservation interface (guardedConnectOutput continueValue continueValue ⟨0⟩).result
        out observed ∧ out.state = targetPoison target .divisionByZero ∧
      observed.result = .error .divisionByZero := by
  have laws := short_circuit_expression_laws related interface sourceHeap sourceCalls targetHeap targetCalls
    sourceFrame source clear tagged .bool TargetZero.boolean (guarded_connect_supported continueValue continueValue)
  obtain ⟨out, ran, raw, _, _, _⟩ := laws.forward root
    (guarded_connect_actual_emission interface (sourceFrameScope sourceFrame) continueValue continueValue ⟨0⟩)
    frames states bounded hscope
    ((literal_taken_source_exact interface sourceHeap sourceCalls sourceFrame continueValue divisionTest source _).mpr
      ((division_test_source_refuses interface sourceHeap sourceCalls sourceFrame source clear _).mpr rfl))
  obtain ⟨observed, observation⟩ := guarded_related_has_observation raw
  have correspondence := guarded_related_observation_correspondence states clear raw observation
  exact ⟨out, observed, ran, observation, raw.2.2, correspondence.result⟩

def emptyInterface : Interface := ⟨[], [], [], []⟩
def emptySource : SourceState Unit := ⟨⟨fun _ _ => none, fun _ => none⟩, none, true, true, (), AllocatorStats.sourceEmpty⟩
def emptyTarget : TargetState Unit := ⟨⟨fun _ _ => none, fun _ => none⟩, none, true, true, (), AllocatorStats.targetEmpty⟩
def missingSourceFrame : SourceFrame := ⟨0, 1, [⟨"missing", .bool, 0⟩]⟩
def missingTargetFrame : TargetFrame := ⟨0, 1, [⟨"missing", .bool, 0⟩], [], fun _ => none⟩
def missingConnect (continueValue : Bool) : Expr :=
  .binary (shortCircuitBinary continueValue) (.bool (!continueValue)) (.variable "missing")

/-- This is a statically admitted, outer-tag-compatible but non-reached frame:
the declaration has no live cell. Tag compatibility does not assert liveness. -/
theorem missing_cell_profile :
    inferExpr emptyInterface (sourceFrameScope missingSourceFrame) (.variable "missing") = some .bool ∧
    sourceLocalValue missingSourceFrame emptySource "missing" = none ∧
    SourceLocalsTagged missingSourceFrame emptySource.memory ∧
    TemporariesScoped missingTargetFrame := by
  refine ⟨?_, rfl, ?_, fun _ _ => rfl⟩
  · simp only [inferExpr, sourceFrameScope, missingSourceFrame, List.map_cons, List.map_nil,
      lookupVariable, List.find?_cons, beq_self_eq_true, Option.map_some]
  · intro binding member value read
    cases read

theorem missing_cell_has_no_source_read (heap : SourceHeapSemantics Unit) (calls : SourceCalls Unit)
    (out : SourceOutcome Unit) :
    ¬ SourceExprEval emptyInterface heap calls missingSourceFrame (.variable "missing") emptySource out := by
  intro ran
  obtain ⟨value, read, _⟩ := (source_operand_free_expression_exact _ rfl _ _).mp ran
  cases read

theorem missing_connect_actual_emission (continueValue : Bool) :
    NativeLowering.expression? emptyInterface (sourceFrameScope missingSourceFrame) (missingConnect continueValue) ⟨0⟩ =
      some (shortCircuitOutput continueValue
        ⟨[.temporary 1 .bool (.bool (!continueValue))], .temporary 1 .bool, ⟨1⟩⟩
        ⟨[.temporary 3 .bool (.readLocal "missing")], .temporary 3 .bool, ⟨3⟩⟩) := by
  cases continueValue <;>
    simp [missingConnect, shortCircuitBinary, shortCircuitOutput, shortCircuitCondition,
      NativeLowering.expression?, inferExpr, sourceFrameScope, missingSourceFrame,
      lookupVariable, binaryType, NativeLowering.pureTemporary, NativeIR.fresh]

theorem skipped_missing_read_executes (sourceHeap : SourceHeapSemantics Unit) (sourceCalls : SourceCalls Unit)
    (targetHeap : TargetHeapSemantics Unit) (targetCalls : TargetCalls Unit) (continueValue : Bool) :
    ∃ output out observed,
      NativeLowering.expression? emptyInterface (sourceFrameScope missingSourceFrame) (missingConnect continueValue) ⟨0⟩ = some output ∧
      TargetRun emptyInterface targetHeap targetCalls .bool output.code output.code missingTargetFrame emptyTarget out ∧
      targetExpressionObservation emptyInterface output.result out observed ∧
      out.state = emptyTarget ∧ observed.result = .ok (.bool (!continueValue)) := by
  let output := shortCircuitOutput continueValue
    ⟨[.temporary 1 .bool (.bool (!continueValue))], .temporary 1 .bool, ⟨1⟩⟩
    ⟨[.temporary 3 .bool (.readLocal "missing")], .temporary 3 .bool, ⟨3⟩⟩
  have states : StateRelated (fun (s t : Unit) => s = t) emptySource emptyTarget :=
    ⟨⟨fun _ _ => rfl, fun _ => rfl⟩, rfl, rfl, rfl, rfl, AllocatorStats.empty_related⟩
  have frames : FrameRelated missingSourceFrame missingTargetFrame := ⟨rfl, rfl, rfl⟩
  have bounded : TemporaryNamesBound missingTargetFrame 0 := by intro _ live; cases live
  have supported : SourceShortCircuitExpression (missingConnect continueValue) :=
    .connect continueValue (.guarded (.leaf (.bool _))) (.guarded (.leaf (.variable _)))
  have laws := short_circuit_expression_laws (fun (s t : Unit) => s = t) emptyInterface
    sourceHeap sourceCalls targetHeap targetCalls missingSourceFrame emptySource rfl missing_cell_profile.2.2.1
    .bool TargetZero.boolean supported
  obtain ⟨out, ran, related, _, _, _⟩ := laws.forward output.code (missing_connect_actual_emission continueValue)
    frames states bounded missing_cell_profile.2.2.2
    ((literal_skip_source_exact emptyInterface sourceHeap sourceCalls missingSourceFrame continueValue
      (.variable "missing") emptySource _).mpr rfl)
  obtain ⟨observed, observation⟩ := guarded_related_has_observation related
  have correspondence := guarded_related_observation_correspondence states rfl related observation
  exact ⟨output, out, observed, missing_connect_actual_emission continueValue, ran, observation,
    related.2.2.1, correspondence.result⟩

def nullCheckBody : List Instruction :=
  [.helper none (.reference (.zero (.ref .word))), .checkContext]

/-- The skipped arm contains a real shared helper that would poison this
clear context if called; no reference dereference is presumed defined. -/
theorem null_helper_refuses_if_called (heap : TargetHeapSemantics Unit) (frame : TargetFrame) :
    TargetMemoryCall emptyInterface heap frame (.reference (.zero (.ref .word))) emptyTarget
      ⟨.bool false, targetPoison emptyTarget .nullReference⟩ := by
  exact .reference (.zero (.nullPointer .word))

theorem skipped_null_helper_keeps_full_state (heap : TargetHeapSemantics Unit) (calls : TargetCalls Unit)
    (continueValue : Bool) :
    let marker := targetDeclareTemporary (targetEmptyFrame 0) 1 (.bool (!continueValue))
    TargetRun emptyInterface heap calls .bool []
      [.branch (shortCircuitCondition continueValue (.temporary 1 .bool)) nullCheckBody []]
      marker emptyTarget ⟨.normal, marker, emptyTarget⟩ := by
  apply (target_short_circuit_skip_exact continueValue
    (declared_temporaries_completeNames (target_empty_frame_scoped 0) 1 (.bool (!continueValue)))
    (declared_temporary_atom emptyInterface (targetEmptyFrame 0) emptyTarget 1 .bool (.bool (!continueValue)))
    nullCheckBody [] _).mpr
  rfl

def ghostFrame : TargetFrame :=
  { targetEmptyFrame 0 with temporaries := fun identity => if identity = 7 then some (.bool true) else none }

theorem ghost_private_value_is_not_scoped : ¬ TemporariesScoped ghostFrame := by
  intro hscope
  have impossible := hscope 7 rfl
  cases impossible

/-- Empty branch closure removes a ghost map entry, demonstrating why the
exact skip-frame theorem derives and requires live-name scoping. -/
theorem ghost_empty_branch_changes_private_map {World : Type} (state : TargetState World)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) :
    ∃ out,
      TargetRun emptyInterface heap calls .bool [] [.branch (.value (.zero .bool)) [] []] ghostFrame state out ∧
      out.frame.temporaries 7 = none ∧ ghostFrame.temporaries 7 = some (.bool true) ∧
      out ≠ ⟨.normal, ghostFrame, state⟩ := by
  let out := targetCloseBlock ghostFrame ⟨.normal, ghostFrame, state⟩
  refine ⟨out, ?_, rfl, rfl, ?_⟩
  · exact (target_single_branch_exact (.value (.zero TargetZero.boolean))
      (by simp only [Bool.false_eq_true, if_false, jumpFreeCode]) [] out).mpr
      ⟨⟨.normal, ghostFrame, state⟩, .nil [] ghostFrame state, rfl⟩
  · intro same
    have impossible := congrArg (fun value : TargetBlockOutcome World => value.frame.temporaries 7) same
    cases impossible

end Mettapedia.GSLT.LanguageDef.NativeOps.ShortCircuitControls
