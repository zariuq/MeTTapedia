import Mettapedia.GSLT.LanguageDef.NativeOpsShortCircuitCorrespondence
import Mettapedia.GSLT.LanguageDef.NativeOpsGuardedExpressionControls
import Mettapedia.GSLT.LanguageDef.NativeOpsCFunctionComposition

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

/-- A catalogued Boolean action remains an actual call in the selected arm. -/
def observedBool : External :=
  ⟨⟨"probe", [], .bool⟩, "probe", .effect, none⟩

def cProbeExpression (continueValue : Bool) : NativeC.CExpr :=
  .binary (if continueValue then .and else .or)
    (.identifier "left".toList) (.call "probe".toList [])

def cProbeOutput (identity : Nat) (continueValue : Bool) : NativeLowering.Expression :=
  shortCircuitOutput continueValue
    ⟨[], .temporary identity .bool, ⟨identity⟩⟩
    ⟨[.call (some (.temporary (identity + 2) .bool)) (.external "probe") []],
      .temporary (identity + 2) .bool, ⟨identity + 2⟩⟩

theorem c_probe_actual_admission (identity : Nat) (continueValue : Bool) :
    NativeC.primitiveExpression? [("left".toList, .temporary identity .bool)] 2
      (cProbeExpression continueValue) ⟨identity⟩ [observedBool] =
      some (cProbeOutput identity continueValue) := by
  cases continueValue <;> rfl

def cScalarProbeOutput (type : NativeType) (identity : Nat)
    (continueValue : Bool) : NativeLowering.Expression :=
  shortCircuitOutput continueValue
    ⟨[.temporary (identity + 1) .bool
        (.binary (.compare .ne) (.temporary identity type) (.zero type))],
      .temporary (identity + 1) .bool, ⟨identity + 1⟩⟩
    ⟨[.call (some (.temporary (identity + 3) .bool)) (.external "probe") []],
      .temporary (identity + 3) .bool, ⟨identity + 3⟩⟩

theorem c_scalar_probe_actual_admission (type : NativeType) (identity : Nat)
    (continueValue : Bool)
    (admitted : NativeLowering.scalarConditionOperation? (.temporary identity type) =
      some (.binary (.compare .ne) (.temporary identity type) (.zero type))) :
    NativeC.primitiveExpression? [("left".toList, .temporary identity type)] 2
      (cProbeExpression continueValue) ⟨identity⟩ [observedBool] =
      some (cScalarProbeOutput type identity continueValue) := by
  cases type <;> simp only [NativeLowering.scalarConditionOperation?, Atom.type,
    reduceCtorEq, Option.some.injEq] at admitted
  all_goals cases continueValue <;> rfl

theorem c_word_logical_operand_admitted (continueValue : Bool) :
    NativeC.primitiveExpression? [("left".toList, .temporary 0 .word)] 2
      (cProbeExpression continueValue) ⟨0⟩ [observedBool] =
      some (cScalarProbeOutput .word 0 continueValue) :=
  c_scalar_probe_actual_admission .word 0 continueValue rfl

theorem c_byte_logical_operand_admitted (continueValue : Bool) :
    NativeC.primitiveExpression? [("left".toList, .temporary 0 .byte)] 2
      (cProbeExpression continueValue) ⟨0⟩ [observedBool] =
      some (cScalarProbeOutput .byte 0 continueValue) :=
  c_scalar_probe_actual_admission .byte 0 continueValue rfl

theorem c_pointer_logical_operand_admitted (continueValue : Bool) :
    NativeC.primitiveExpression? [("left".toList, .temporary 0 (.ref .bool))] 2
      (cProbeExpression continueValue) ⟨0⟩ [observedBool] =
      some (cScalarProbeOutput (.ref .bool) 0 continueValue) :=
  c_scalar_probe_actual_admission (.ref .bool) 0 continueValue rfl

theorem c_compound_logical_operand_refused (name : String) (continueValue : Bool) :
    NativeC.primitiveExpression? [("left".toList, .temporary 0 (.named name))] 2
      (cProbeExpression continueValue) ⟨0⟩ [observedBool] = none := by
  cases continueValue <;> rfl

theorem c_array_logical_operand_refused (element : NativeType) (continueValue : Bool) :
    NativeC.primitiveExpression? [("left".toList, .temporary 0 (.array element))] 2
      (cProbeExpression continueValue) ⟨0⟩ [observedBool] = none := by
  cases continueValue <;> rfl

theorem c_logical_word_return_refused (continueValue : Bool) :
    NativeC.primitiveStatement? [("left".toList, .temporary 0 .word)] .word 3
      (.return (some (cProbeExpression continueValue))) ⟨0⟩ [observedBool] = none := by
  cases continueValue <;> rfl

theorem c_unknown_logical_call_refused (continueValue : Bool) :
    NativeC.primitiveExpression? [("left".toList, .temporary 0 .bool)] 2
      (cProbeExpression continueValue) ⟨0⟩ [] = none := by
  cases continueValue <;> rfl

theorem c_ambiguous_logical_call_refused (continueValue : Bool) :
    NativeC.primitiveExpression? [("left".toList, .temporary 0 .bool)] 2
      (cProbeExpression continueValue) ⟨0⟩ [observedBool, observedBool] = none := by
  cases continueValue <;> rfl

def cProbeHeader : Header := ⟨"logical", [⟨"left", .bool⟩], .bool⟩

def cProbeRepresentation : NativeC.Representation :=
  ⟨"Logical", ⟨[], [], [], [observedBool]⟩, []⟩

def cProbeText (continueValue : Bool) : String :=
  if continueValue then "bool logical(bool left) { return left && probe(); }"
  else "bool logical(bool left) { return left || probe(); }"

def cProbeTokens (continueValue : Bool) : List NativeC.Token :=
  [.identifier "bool".toList, .identifier "logical".toList, .punctuation "(".toList,
    .identifier "bool".toList, .identifier "left".toList, .punctuation ")".toList,
    .punctuation "{".toList, .identifier "return".toList, .identifier "left".toList,
    .punctuation (if continueValue then "&&".toList else "||".toList),
    .identifier "probe".toList, .punctuation "(".toList, .punctuation ")".toList,
    .punctuation ";".toList, .punctuation "}".toList]

def cProbeFunction (continueValue : Bool) : NativeC.CFunction :=
  ⟨⟨"bool".toList, 0⟩, "logical".toList, [⟨⟨"bool".toList, 0⟩, "left".toList⟩],
    [.return (some (cProbeExpression continueValue))]⟩

theorem c_probe_text_lexed (continueValue : Bool) :
    NativeC.lex (cProbeText continueValue).toList = .ok (cProbeTokens continueValue) := by
  cases continueValue <;> cbv

theorem c_probe_tokens_parsed (continueValue : Bool) :
    NativeC.function? (2 * (cProbeTokens continueValue).length + 4) ["bool".toList]
      (NativeC.ordinaryFunctionTokens (cProbeTokens continueValue)) =
      some (cProbeFunction continueValue, []) := by
  cases continueValue <;> rfl

theorem c_probe_full_text_admitted (continueValue : Bool) :
    NativeC.primitiveFunctionText? cProbeRepresentation ["bool".toList]
      cProbeHeader [] (cProbeText continueValue).toList =
      some ⟨cProbeHeader,
        NativeC.primitiveParameterCapture cProbeHeader.parameters ++
          (cProbeOutput 1 continueValue).code ++ [.return (cProbeOutput 1 continueValue).result],
        3⟩ := by
  rw [NativeC.primitive_function_text_of_parts cProbeRepresentation ["bool".toList]
    cProbeHeader [] _ _ _ (c_probe_text_lexed continueValue) (c_probe_tokens_parsed continueValue)]
  cases continueValue <;> rfl

def cScalarProbeText (name : String) (pointer continueValue : Bool) : String :=
  "bool logical(" ++ name ++ (if pointer then " *" else " ") ++
    "left) { return left " ++ (if continueValue then "&&" else "||") ++ " probe(); }"

def cScalarProbeTokens (name : NativeC.Name) (pointer continueValue : Bool) : List NativeC.Token :=
  [.identifier "bool".toList, .identifier "logical".toList, .punctuation "(".toList,
    .identifier name] ++ (if pointer then [.punctuation "*".toList] else []) ++
    [.identifier "left".toList, .punctuation ")".toList, .punctuation "{".toList,
      .identifier "return".toList, .identifier "left".toList,
      .punctuation (if continueValue then "&&".toList else "||".toList),
      .identifier "probe".toList, .punctuation "(".toList, .punctuation ")".toList,
      .punctuation ";".toList, .punctuation "}".toList]

def cScalarProbeFunction (name : NativeC.Name) (pointer continueValue : Bool) : NativeC.CFunction :=
  ⟨⟨"bool".toList, 0⟩, "logical".toList,
    [⟨⟨name, if pointer then 1 else 0⟩, "left".toList⟩],
    [.return (some (cProbeExpression continueValue))]⟩

theorem c_scalar_probe_word_tokens_parsed (continueValue : Bool) :
    NativeC.function? (2 * (cScalarProbeTokens "uint64_t".toList false continueValue).length + 4)
      ["bool".toList, "uint64_t".toList]
      (NativeC.ordinaryFunctionTokens (cScalarProbeTokens "uint64_t".toList false continueValue)) =
      some (cScalarProbeFunction "uint64_t".toList false continueValue, []) := by
  cases continueValue <;> rfl

theorem c_scalar_probe_byte_tokens_parsed (continueValue : Bool) :
    NativeC.function? (2 * (cScalarProbeTokens "uint8_t".toList false continueValue).length + 4)
      ["bool".toList, "uint8_t".toList]
      (NativeC.ordinaryFunctionTokens (cScalarProbeTokens "uint8_t".toList false continueValue)) =
      some (cScalarProbeFunction "uint8_t".toList false continueValue, []) := by
  cases continueValue <;> rfl

theorem c_scalar_probe_pointer_tokens_parsed (continueValue : Bool) :
    NativeC.function? (2 * (cScalarProbeTokens "bool".toList true continueValue).length + 4)
      ["bool".toList]
      (NativeC.ordinaryFunctionTokens (cScalarProbeTokens "bool".toList true continueValue)) =
      some (cScalarProbeFunction "bool".toList true continueValue, []) := by
  cases continueValue <;> rfl

theorem c_scalar_probe_word_lexed (continueValue : Bool) :
    NativeC.lex (cScalarProbeText "uint64_t" false continueValue).toList =
      .ok (cScalarProbeTokens "uint64_t".toList false continueValue) := by
  cases continueValue <;> cbv

theorem c_scalar_probe_byte_lexed (continueValue : Bool) :
    NativeC.lex (cScalarProbeText "uint8_t" false continueValue).toList =
      .ok (cScalarProbeTokens "uint8_t".toList false continueValue) := by
  cases continueValue <;> cbv

theorem c_scalar_probe_pointer_lexed (continueValue : Bool) :
    NativeC.lex (cScalarProbeText "bool" true continueValue).toList =
      .ok (cScalarProbeTokens "bool".toList true continueValue) := by
  cases continueValue <;> cbv

theorem c_scalar_probe_word_text_admitted (continueValue : Bool) :
    let header : Header := ⟨"logical", [⟨"left", .word⟩], .bool⟩
    NativeC.primitiveFunctionText? cProbeRepresentation ["bool".toList, "uint64_t".toList]
      header [] (cScalarProbeText "uint64_t" false continueValue).toList =
      some ⟨header, NativeC.primitiveParameterCapture header.parameters ++
        (cScalarProbeOutput .word 1 continueValue).code ++
          [.return (cScalarProbeOutput .word 1 continueValue).result], 4⟩ := by
  dsimp only
  rw [NativeC.primitive_function_text_of_parts _ _ _ _ _ _ _
    (c_scalar_probe_word_lexed continueValue)
    (c_scalar_probe_word_tokens_parsed continueValue)]
  cases continueValue <;> rfl

theorem c_scalar_probe_byte_text_admitted (continueValue : Bool) :
    let header : Header := ⟨"logical", [⟨"left", .byte⟩], .bool⟩
    NativeC.primitiveFunctionText? cProbeRepresentation ["bool".toList, "uint8_t".toList]
      header [] (cScalarProbeText "uint8_t" false continueValue).toList =
      some ⟨header, NativeC.primitiveParameterCapture header.parameters ++
        (cScalarProbeOutput .byte 1 continueValue).code ++
          [.return (cScalarProbeOutput .byte 1 continueValue).result], 4⟩ := by
  dsimp only
  rw [NativeC.primitive_function_text_of_parts _ _ _ _ _ _ _
    (c_scalar_probe_byte_lexed continueValue)
    (c_scalar_probe_byte_tokens_parsed continueValue)]
  cases continueValue <;> rfl

theorem c_scalar_probe_pointer_text_admitted (continueValue : Bool) :
    let header : Header := ⟨"logical", [⟨"left", .ref .bool⟩], .bool⟩
    NativeC.primitiveFunctionText? cProbeRepresentation ["bool".toList]
      header [] (cScalarProbeText "bool" true continueValue).toList =
      some ⟨header, NativeC.primitiveParameterCapture header.parameters ++
        (cScalarProbeOutput (.ref .bool) 1 continueValue).code ++
          [.return (cScalarProbeOutput (.ref .bool) 1 continueValue).result], 4⟩ := by
  dsimp only
  rw [NativeC.primitive_function_text_of_parts _ _ _ _ _ _ _
    (c_scalar_probe_pointer_lexed continueValue)
    (c_scalar_probe_pointer_tokens_parsed continueValue)]
  cases continueValue <;> rfl

/-- The skipped action can have arbitrary semantics: its entire pre-state is
retained, and no action contract is needed to justify skipping it. -/
theorem c_probe_skipped_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} (identity : Nat) (continueValue : Bool)
    (hscope : TemporariesScoped frame)
    (unused : frame.temporaryNames.contains (identity + 1) = false)
    (read : TargetAtomEval interface frame state (.temporary identity .bool) (.bool (!continueValue)))
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root (cProbeOutput identity continueValue).code frame state out ↔
      out = ⟨.normal, targetDeclareTemporary frame (identity + 1) (.bool (!continueValue)), state⟩ := by
  change TargetRun interface heap calls .bool root
    (.temporary (identity + 1) .bool (.copy (.temporary identity .bool)) :: _) frame state out ↔ _
  rw [target_short_circuit_copy_exact unused read]
  have copied : TargetAtomEval interface
      (targetDeclareTemporary frame (identity + 1) (.bool (!continueValue))) state
      (.temporary (identity + 1) .bool) (.bool (!continueValue)) :=
    .temporary (declare_temporary_read frame (identity + 1) _) (by simp [targetDeclareTemporary])
  exact target_short_circuit_skip_exact continueValue
    (declare_temporary_scoped frame (identity + 1) _ hscope) copied _ root out

/-- Selecting the arm invokes the admitted action once and retains its whole
post-state. Its returned Boolean replaces the outer copy before scope exit. -/
theorem c_probe_taken_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state final : TargetState World} (identity : Nat) (continueValue returned : Bool)
    (unusedCopy : frame.temporaryNames.contains (identity + 1) = false)
    (unusedCall : frame.temporaryNames.contains (identity + 2) = false)
    (read : TargetAtomEval interface frame state (.temporary identity .bool) (.bool continueValue))
    (action : ∀ raw post, calls (.external "probe") [] state raw post ↔
      raw = .bool returned ∧ post = final)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root (cProbeOutput identity continueValue).code frame state out ↔
      out = targetCloseBlock (targetDeclareTemporary frame (identity + 1) (.bool continueValue))
        ⟨.normal, targetUpdateTemporary
          (targetDeclareTemporary (targetDeclareTemporary frame (identity + 1) (.bool continueValue))
            (identity + 2) (.bool returned)) (identity + 1) (.bool returned), final⟩ := by
  let copied := targetDeclareTemporary frame (identity + 1) (.bool continueValue)
  let called := targetDeclareTemporary copied (identity + 2) (.bool returned)
  let body : List Instruction :=
    [.call (some (.temporary (identity + 2) .bool)) (.external "probe") [],
      .assign (.temporary (identity + 1) .bool) (.temporary (identity + 2) .bool)]
  have copiedRead : TargetAtomEval interface copied state
      (.temporary (identity + 1) .bool) (.bool continueValue) :=
    .temporary (declare_temporary_read frame (identity + 1) _) (by simp [copied, targetDeclareTemporary])
  have tested : TargetConditionEval interface copied state
      (shortCircuitCondition continueValue (.temporary (identity + 1) .bool)) true := by
    have self : (continueValue == continueValue) = true := by cases continueValue <;> rfl
    simpa only [self] using short_circuit_condition_evaluates continueValue copiedRead
  have freshCall : copied.temporaryNames.contains (identity + 2) = false := by
    simpa [copied, targetDeclareTemporary] using unusedCall
  have calledRead : TargetAtomEval interface called final
      (.temporary (identity + 2) .bool) (.bool returned) :=
    .temporary (declare_temporary_read copied (identity + 2) _) (by simp [called, targetDeclareTemporary])
  have liveCopy : called.temporaryNames.contains (identity + 1) = true := by
    simp [called, copied, targetDeclareTemporary]
  have bodyExact : ∀ inner, TargetRun interface heap calls .bool body body copied state inner ↔
      inner = ⟨.normal, targetUpdateTemporary called (identity + 1) (.bool returned), final⟩ := by
    intro inner
    rw [target_normal_then_exact
      (target_call_temporary_instruction_exact freshCall TargetAtomsEval.nil action)]
    exact target_assign_temporary_run_exact calledRead liveCopy _ inner
  change TargetRun interface heap calls .bool root
    (.temporary (identity + 1) .bool (.copy (.temporary identity .bool)) :: _) frame state out ↔ _
  rw [target_short_circuit_copy_exact unusedCopy read]
  change TargetRun interface heap calls .bool root
    [.branch (shortCircuitCondition continueValue (.temporary (identity + 1) .bool)) body []]
    copied state out ↔
      out = targetCloseBlock copied
        ⟨.normal, targetUpdateTemporary called (identity + 1) (.bool returned), final⟩
  rw [target_single_branch_exact tested (by simp [body, jumpFreeCode, jumpFreeInstruction])]
  constructor
  · rintro ⟨inner, ran, same⟩
    cases (bodyExact inner).mp ran
    exact same
  · intro same
    exact ⟨_, (bodyExact _).mpr rfl, same⟩

/-- The scalar reader's actual emitted code first computes truth, then uses
the same Boolean branch constructor. The right call remains inside its arm. -/
theorem c_scalar_probe_boolean_continuation {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} {type : NativeType} {value : SourceValue}
    (continueValue : Bool) (tagged : SourceOuterTag type value)
    (read : TargetAtomEval interface frame state (.temporary 0 type) (encodeValue value))
    (admitted : NativeLowering.scalarConditionOperation? (.temporary 0 type) =
      some (.binary (.compare .ne) (.temporary 0 type) (.zero type)))
    {test : Bool} (meaning : sourceScalarCondition value = some test)
    (unused : frame.temporaryNames.contains 1 = false)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root (cScalarProbeOutput type 0 continueValue).code
      frame state out ↔
      TargetRun interface heap calls .bool root (cProbeOutput 1 continueValue).code
        (targetDeclareTemporary frame 1 (.bool test)) state out := by
  have computed := (scalar_condition_source_exact (atom := .temporary 0 type)
    tagged read admitted).mpr
    ⟨test, meaning, rfl⟩
  change TargetRun interface heap calls .bool root
    (.temporary 1 .bool (.binary (.compare .ne) (.temporary 0 type) (.zero type)) :: _)
    frame state out ↔ _
  rw [target_normal_then_exact (target_temporary_instruction_exact unused computed)]
  rfl

/-- Skipped scalar guards preserve every external state field, not just the
returned Boolean. No semantics for the unreachable action is assumed. -/
theorem c_scalar_probe_skipped_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} {type : NativeType} {value : SourceValue}
    (continueValue : Bool) (tagged : SourceOuterTag type value)
    (read : TargetAtomEval interface frame state (.temporary 0 type) (encodeValue value))
    (admitted : NativeLowering.scalarConditionOperation? (.temporary 0 type) =
      some (.binary (.compare .ne) (.temporary 0 type) (.zero type)))
    (meaning : sourceScalarCondition value = some (!continueValue))
    (hscope : TemporariesScoped frame)
    (unusedTruth : frame.temporaryNames.contains 1 = false)
    (unusedCopy : frame.temporaryNames.contains 2 = false)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root (cScalarProbeOutput type 0 continueValue).code
      frame state out ↔
      out = ⟨.normal, targetDeclareTemporary
        (targetDeclareTemporary frame 1 (.bool (!continueValue))) 2 (.bool (!continueValue)), state⟩ := by
  rw [c_scalar_probe_boolean_continuation continueValue tagged read admitted meaning unusedTruth]
  exact c_probe_skipped_exact 1 continueValue
    (declare_temporary_scoped frame 1 _ hscope)
    (by simpa [targetDeclareTemporary] using unusedCopy)
    (declared_temporary_atom interface frame state 1 .bool (.bool (!continueValue))) root out

theorem c_scalar_probe_taken_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state final : TargetState World} {type : NativeType} {value : SourceValue}
    (continueValue returned : Bool) (tagged : SourceOuterTag type value)
    (read : TargetAtomEval interface frame state (.temporary 0 type) (encodeValue value))
    (admitted : NativeLowering.scalarConditionOperation? (.temporary 0 type) =
      some (.binary (.compare .ne) (.temporary 0 type) (.zero type)))
    (meaning : sourceScalarCondition value = some continueValue)
    (unusedTruth : frame.temporaryNames.contains 1 = false)
    (unusedCopy : frame.temporaryNames.contains 2 = false)
    (unusedCall : frame.temporaryNames.contains 3 = false)
    (action : ∀ raw post, calls (.external "probe") [] state raw post ↔
      raw = .bool returned ∧ post = final)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root (cScalarProbeOutput type 0 continueValue).code
      frame state out ↔
      out = targetCloseBlock
        (targetDeclareTemporary (targetDeclareTemporary frame 1 (.bool continueValue)) 2 (.bool continueValue))
        ⟨.normal, targetUpdateTemporary
          (targetDeclareTemporary
            (targetDeclareTemporary (targetDeclareTemporary frame 1 (.bool continueValue)) 2 (.bool continueValue))
            3 (.bool returned)) 2 (.bool returned), final⟩ := by
  rw [c_scalar_probe_boolean_continuation continueValue tagged read admitted meaning unusedTruth]
  exact c_probe_taken_exact 1 continueValue returned
    (by simpa [targetDeclareTemporary] using unusedCopy)
    (by simpa [targetDeclareTemporary] using unusedCall)
    (declared_temporary_atom interface frame state 1 .bool (.bool continueValue)) action root out

def counterFrame (value : TargetValue) : TargetFrame :=
  ⟨0, 0, [], [0], fun identity => if identity = 0 then some value else none⟩

def counterState : TargetState Nat :=
  ⟨⟨fun _ _ => none, fun _ => none⟩, none, true, true, 0, AllocatorStats.targetEmpty⟩

def counterCalls : TargetCalls Nat := fun target arguments before value after =>
  target = .external "probe" ∧ arguments = [] ∧ value = .bool true ∧
    after = { before with external := before.external + 1 }

theorem counter_frame_scoped (value : TargetValue) : TemporariesScoped (counterFrame value) := by
  intro identity absent
  by_cases same : identity = 0
  · subst identity
    simp [counterFrame] at absent
  · simp [counterFrame, same]

/-- A genuine effect discriminates the two arms: skipping retains zero calls,
while selecting changes the external counter to exactly one. -/
theorem c_probe_counter_controls (heap : TargetHeapSemantics Nat) (continueValue : Bool) :
    (∃ out, TargetRun cProbeRepresentation.interface heap counterCalls .bool
      (cProbeOutput 0 continueValue).code (cProbeOutput 0 continueValue).code
      (counterFrame (.bool (!continueValue))) counterState out ∧ out.state.external = 0) ∧
    (∃ out, TargetRun cProbeRepresentation.interface heap counterCalls .bool
      (cProbeOutput 0 continueValue).code (cProbeOutput 0 continueValue).code
      (counterFrame (.bool continueValue)) counterState out ∧ out.state.external = 1) := by
  constructor
  · refine ⟨⟨.normal, targetDeclareTemporary (counterFrame (.bool (!continueValue)))
      1 (.bool (!continueValue)), counterState⟩, ?_, rfl⟩
    exact (c_probe_skipped_exact 0 continueValue (counter_frame_scoped _) rfl
      (TargetAtomEval.temporary (by simp [counterFrame]) rfl) _ _).mpr rfl
  · let final := { counterState with external := 1 }
    let out := targetCloseBlock (targetDeclareTemporary (counterFrame (.bool continueValue)) 1 (.bool continueValue))
      ⟨.normal, targetUpdateTemporary
        (targetDeclareTemporary (targetDeclareTemporary (counterFrame (.bool continueValue)) 1 (.bool continueValue))
          2 (.bool true)) 1 (.bool true), final⟩
    refine ⟨out, ?_, rfl⟩
    exact (c_probe_taken_exact 0 continueValue true rfl rfl
      (TargetAtomEval.temporary (by simp [counterFrame]) rfl)
      (by intro raw post; simp [counterCalls, counterState, final]) _ _).mpr rfl

theorem c_scalar_probe_counter_effect (heap : TargetHeapSemantics Nat)
    (type : NativeType) (value : SourceValue) (selected continueValue : Bool)
    (tagged : SourceOuterTag type value)
    (admitted : NativeLowering.scalarConditionOperation? (.temporary 0 type) =
      some (.binary (.compare .ne) (.temporary 0 type) (.zero type)))
    (meaning : sourceScalarCondition value = some selected) (root : List NativeIR.Instruction) :
    ∃ out, TargetRun cProbeRepresentation.interface heap counterCalls .bool
      root (cScalarProbeOutput type 0 continueValue).code
      (counterFrame (encodeValue value)) counterState out ∧
      out.state.external = if selected == continueValue then 1 else 0 := by
  have read : TargetAtomEval cProbeRepresentation.interface (counterFrame (encodeValue value))
      counterState (.temporary 0 type) (encodeValue value) :=
    .temporary (by simp [counterFrame]) rfl
  by_cases chose : selected = continueValue
  · subst selected
    let frame := counterFrame (encodeValue value)
    let final := { counterState with external := 1 }
    let out := targetCloseBlock
      (targetDeclareTemporary (targetDeclareTemporary frame 1 (.bool continueValue)) 2 (.bool continueValue))
      ⟨.normal, targetUpdateTemporary
        (targetDeclareTemporary
          (targetDeclareTemporary (targetDeclareTemporary frame 1 (.bool continueValue)) 2 (.bool continueValue))
          3 (.bool true)) 2 (.bool true), final⟩
    refine ⟨out, ?_, ?_⟩
    · exact (c_scalar_probe_taken_exact continueValue true tagged read admitted meaning rfl rfl rfl
        (by intro raw post; simp [counterCalls, counterState, final]) _ _).mpr rfl
    · change 1 = if continueValue == continueValue then 1 else 0
      simp only [beq_self_eq_true, if_true]
  · have selectedEq : selected = !continueValue := by
      cases selected <;> cases continueValue <;> simp_all
    subst selected
    let frame := counterFrame (encodeValue value)
    let out : TargetBlockOutcome Nat :=
      ⟨.normal, targetDeclareTemporary
        (targetDeclareTemporary frame 1 (.bool (!continueValue))) 2 (.bool (!continueValue)), counterState⟩
    refine ⟨out, ?_, by cases continueValue <;> rfl⟩
    exact (c_scalar_probe_skipped_exact continueValue tagged read admitted meaning
      (counter_frame_scoped _) rfl rfl _ _).mpr rfl

theorem c_scalar_truth_effect_controls (heap : TargetHeapSemantics Nat) :
    (∃ out, TargetRun cProbeRepresentation.interface heap counterCalls .bool []
      (cScalarProbeOutput .word 0 true).code (counterFrame (.word 0)) counterState out ∧
      out.state.external = 0) ∧
    (∃ out, TargetRun cProbeRepresentation.interface heap counterCalls .bool []
      (cScalarProbeOutput .word 0 true).code (counterFrame (.word 65536)) counterState out ∧
      out.state.external = 1) ∧
    (∃ out, TargetRun cProbeRepresentation.interface heap counterCalls .bool []
      (cScalarProbeOutput .byte 0 false).code (counterFrame (.byte 255)) counterState out ∧
      out.state.external = 0) ∧
    (∃ out, TargetRun cProbeRepresentation.interface heap counterCalls .bool []
      (cScalarProbeOutput (.ref .bool) 0 true).code (counterFrame (.reference none)) counterState out ∧
      out.state.external = 0) ∧
    (∃ out, TargetRun cProbeRepresentation.interface heap counterCalls .bool []
      (cScalarProbeOutput (.ref .bool) 0 true).code
        (counterFrame (.reference (some ⟨99, 7, []⟩))) counterState out ∧ out.state.external = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | exact c_scalar_probe_counter_effect heap .word (.word 0) false true (.word 0) rfl rfl []
    | exact c_scalar_probe_counter_effect heap .word (.word 65536) true true (.word 65536) rfl rfl []
    | exact c_scalar_probe_counter_effect heap .byte (.byte 255) true false (.byte 255) rfl rfl []
    | exact c_scalar_probe_counter_effect heap (.ref .bool) (.reference none) false true
        (.reference _ _) rfl rfl []
    | exact c_scalar_probe_counter_effect heap (.ref .bool) (.reference (some ⟨99, 7, []⟩)) true true
        (.reference _ _) rfl rfl []

theorem non_null_condition_does_not_validate_dereference (value : TargetValue) :
    targetScalarCondition (.reference (some ⟨99, 7, []⟩)) = some true ∧
      ¬ TargetPureEval cProbeRepresentation.interface
        (counterFrame (.reference (some ⟨99, 7, []⟩))) counterState
        (.indirectRead (.temporary 0 (.ref .bool))) value := by
  refine ⟨rfl, ?_⟩
  intro ran
  cases ran with
  | indirect pointer read =>
      have actual : TargetAtomEval cProbeRepresentation.interface
          (counterFrame (.reference (some ⟨99, 7, []⟩))) counterState
          (.temporary 0 (.ref .bool)) (.reference (some ⟨99, 7, []⟩)) :=
        .temporary rfl rfl
      cases target_atom_unique actual pointer
      cases read

theorem c_scalar_not_actual_admission (type : NativeType)
    (admitted : NativeLowering.scalarConditionOperation? (.temporary 0 type) =
      some (.binary (.compare .ne) (.temporary 0 type) (.zero type))) :
    NativeC.primitiveExpression? [("left".toList, .temporary 0 type)] 2
      (.unary .not (.identifier "left".toList)) ⟨0⟩ =
      some ⟨[.temporary 1 .bool (.binary (.compare .ne) (.temporary 0 type) (.zero type)),
        .temporary 2 .bool (.unary .not (.temporary 1 .bool))], .temporary 2 .bool, ⟨2⟩⟩ := by
  cases type <;> simp only [NativeLowering.scalarConditionOperation?, NativeIR.Atom.type,
    reduceCtorEq, Option.some.injEq] at admitted
  all_goals rfl

theorem c_not_word_arithmetic_refused :
    NativeC.primitiveExpression? [("left".toList, .temporary 0 .word)] 3
      (.binary .add (.unary .not (.identifier "left".toList)) (.word 1)) ⟨0⟩ = none := by rfl

theorem c_scalar_branch_actual_admission (type : NativeType)
    (admitted : NativeLowering.scalarConditionOperation? (.temporary 0 type) =
      some (.binary (.compare .ne) (.temporary 0 type) (.zero type))) :
    NativeC.primitiveStatement? [("left".toList, .temporary 0 type)] .word 4
      (.branch (.identifier "left".toList)
        [.return (some (.word 7))] [.return (some (.word 9))]) ⟨0⟩ =
      some ([.temporary 1 .bool (.binary (.compare .ne) (.temporary 0 type) (.zero type)),
        .branch (.value (.temporary 1 .bool)) [.return (.word 7)] [.return (.word 9)]], ⟨1⟩) := by
  cases type <;> simp only [NativeLowering.scalarConditionOperation?, NativeIR.Atom.type,
    reduceCtorEq, Option.some.injEq] at admitted
  all_goals rfl

theorem c_scalar_conditional_return_actual_admission (type : NativeType)
    (admitted : NativeLowering.scalarConditionOperation? (.temporary 0 type) =
      some (.binary (.compare .ne) (.temporary 0 type) (.zero type))) :
    NativeC.primitiveStatement? [("left".toList, .temporary 0 type)] .word 3
      (.return (some (.conditional (.identifier "left".toList) (.word 7) (.word 9)))) ⟨0⟩ =
      some ([.temporary 1 .bool (.binary (.compare .ne) (.temporary 0 type) (.zero type)),
        .branch (.value (.temporary 1 .bool)) [.return (.word 7)] [.return (.word 9)]], ⟨1⟩) := by
  cases type <;> simp only [NativeLowering.scalarConditionOperation?, NativeIR.Atom.type,
    reduceCtorEq, Option.some.injEq] at admitted
  all_goals rfl

theorem c_scalar_conditional_return_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} {type : NativeType} {value : SourceValue}
    (tagged : SourceOuterTag type value)
    (read : TargetAtomEval interface frame state (.temporary 0 type) (encodeValue value))
    (admitted : NativeLowering.scalarConditionOperation? (.temporary 0 type) =
      some (.binary (.compare .ne) (.temporary 0 type) (.zero type)))
    {test : Bool} (meaning : sourceScalarCondition value = some test)
    (hscope : TemporariesScoped frame) (unused : frame.temporaryNames.contains 1 = false)
    (root : List NativeIR.Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .word root
      [.temporary 1 .bool (.binary (.compare .ne) (.temporary 0 type) (.zero type)),
        .branch (.value (.temporary 1 .bool)) [.return (.word 7)] [.return (.word 9)]]
      frame state out ↔
      out = ⟨.returned (.word (if test then 7 else 9)),
        targetDeclareTemporary frame 1 (.bool test), state⟩ := by
  have computed := (scalar_condition_source_exact (atom := .temporary 0 type)
    tagged read admitted).mpr ⟨test, meaning, rfl⟩
  rw [target_normal_then_exact (target_temporary_instruction_exact unused computed)]
  let marker := targetDeclareTemporary frame 1 (.bool test)
  have markerScoped : TemporariesScoped marker := declare_temporary_scoped frame 1 _ hscope
  have tested : TargetConditionEval interface marker state (.value (.temporary 1 .bool)) test :=
    .value (declared_temporary_atom interface frame state 1 .bool (.bool test))
  rw [target_single_branch_exact tested
    (by cases test <;> simp [jumpFreeCode, jumpFreeInstruction])]
  cases test <;> simp only [Bool.false_eq_true, if_false, if_true]
  all_goals
    constructor
    · rintro ⟨inner, ran, same⟩
      cases (target_return_then_exact (.word _) _ [] inner).mp ran
      simpa only [targetCloseBlock, targetLeaveScope_self marker state markerScoped] using same
    · intro same
      refine ⟨_, (target_return_then_exact (.word _) _ [] _).mpr rfl, ?_⟩
      simpa only [targetCloseBlock, targetLeaveScope_self marker state markerScoped] using same

theorem c_scalar_not_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    {frame : TargetFrame} {state : TargetState World} {type : NativeType} {value : SourceValue}
    (tagged : SourceOuterTag type value)
    (read : TargetAtomEval interface frame state (.temporary 0 type) (encodeValue value))
    (admitted : NativeLowering.scalarConditionOperation? (.temporary 0 type) =
      some (.binary (.compare .ne) (.temporary 0 type) (.zero type)))
    {test : Bool} (meaning : sourceScalarCondition value = some test)
    (unusedTruth : frame.temporaryNames.contains 1 = false)
    (unusedNot : frame.temporaryNames.contains 2 = false)
    (root : List NativeIR.Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls .bool root
      [.temporary 1 .bool (.binary (.compare .ne) (.temporary 0 type) (.zero type)),
        .temporary 2 .bool (.unary .not (.temporary 1 .bool))] frame state out ↔
      out = ⟨.normal,
        targetDeclareTemporary (targetDeclareTemporary frame 1 (.bool test)) 2 (.bool (!test)), state⟩ := by
  have computed := (scalar_condition_source_exact (atom := .temporary 0 type)
    tagged read admitted).mpr ⟨test, meaning, rfl⟩
  rw [target_normal_then_exact (target_temporary_instruction_exact unusedTruth computed)]
  exact target_run_temporary_exact
    (by simpa [targetDeclareTemporary] using unusedNot)
    (.unary (declared_temporary_atom interface frame state 1 .bool (.bool test)) rfl) root out

end Mettapedia.GSLT.LanguageDef.NativeOps.ShortCircuitControls
