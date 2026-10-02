import Mettapedia.Languages.VibeITP.Native.BuiltinArityCorrespondence

/-!
# Whole-function signature controls

These statements construct actual target executions and rule out extra return
values, altered states, and malformed argument counts. Every builtin is covered,
with marker and largest-word default cases, as well as fault-entry short circuit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.BuiltinArityControls

open Mettapedia.GSLT.LanguageDef
open NativeOps
open NativeWord64 (Word bounded encode)
open Spec BuiltinArityLowering

theorem all_builtin_arities_execute {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World) (clear : state.fault = none)
    (available : ∃ storage, targetFreshFrame state.memory storage) (builtin : Builtin) :
    TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls actualFunction
      [.word (encode (bounded 64 builtin.slot))] state
      ⟨.word (encode (bounded 64 builtin.arity)), state⟩ := by
  apply (BuiltinArityTarget.actual_function_exact state _ _ clear).mpr
  rw [BuiltinAritySource.all_builtin_arities builtin]
  exact ⟨available, rfl⟩

theorem marker_slots_execute_zero {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World) (clear : state.fault = none)
    (available : ∃ storage, targetFreshFrame state.memory storage) :
    TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls actualFunction
      [.word (encode (bounded 64 0))] state ⟨.word 0, state⟩ ∧
    TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls actualFunction
      [.word (encode (bounded 64 1))] state ⟨.word 0, state⟩ := by
  constructor
  · apply (BuiltinArityTarget.actual_function_exact state _ _ clear).mpr
    rw [BuiltinAritySource.marker_slots_return_zero.1]
    exact ⟨available, rfl⟩
  · apply (BuiltinArityTarget.actual_function_exact state _ _ clear).mpr
    rw [BuiltinAritySource.marker_slots_return_zero.2]
    exact ⟨available, rfl⟩

theorem largest_word_executes_zero {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World) (clear : state.fault = none)
    (available : ∃ storage, targetFreshFrame state.memory storage) :
    TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls actualFunction
      [.word (encode (bounded 64 (2^64 - 1)))] state ⟨.word 0, state⟩ := by
  apply (BuiltinArityTarget.actual_function_exact state _ _ clear).mpr
  rw [BuiltinAritySource.largest_word_returns_zero]
  exact ⟨available, rfl⟩

theorem extra_arity_has_no_target_run {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World) (clear : state.fault = none) (builtin : Builtin) (claimed : Word)
    (different : claimed ≠ bounded 64 builtin.arity) (after : TargetState World) :
    ¬ TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls actualFunction
      [.word (encode (bounded 64 builtin.slot))] state ⟨.word (encode claimed), after⟩ := by
  intro ran
  have same := ((BuiltinArityTarget.actual_function_exact state _ _ clear).mp ran).2
  rw [BuiltinAritySource.all_builtin_arities builtin] at same
  have words := TargetValue.word.inj (congrArg TargetRawResult.value same)
  exact different (Fin.ext (congrArg BitVec.toNat words))

theorem changed_post_state_has_no_target_run {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World) (clear : state.fault = none) (slot : Word)
    (value : TargetValue) (after : TargetState World) (different : after ≠ state) :
    ¬ TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls actualFunction
      [.word (encode slot)] state ⟨value, after⟩ := by
  intro ran
  have same := ((BuiltinArityTarget.actual_function_exact state _ _ clear).mp ran).2
  exact different (congrArg TargetRawResult.state same)

theorem missing_argument_has_no_target_run {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World) (out : TargetRawResult World) :
    ¬ TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls actualFunction [] state out := by
  intro ran
  cases ran with
  | run _ parameters _ _ =>
      change none = some _ at parameters
      cases parameters

theorem extra_argument_has_no_target_run {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World) (first second : TargetValue) (out : TargetRawResult World) :
    ¬ TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls actualFunction
      [first, second] state out := by
  intro ran
  cases ran with
  | run _ parameters _ _ =>
      change none = some _ at parameters
      cases parameters

theorem entry_fault_returns_zero {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World) {fault : NativeWord64.Fault} (failed : state.fault = some fault)
    (available : ∃ storage, targetFreshFrame state.memory storage) (slot : Word) :
    TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls actualFunction
      [.word (encode slot)] state ⟨.word 0, state⟩ :=
  (BuiltinArityTarget.actual_function_entry_fault_exact state slot _ failed).mpr ⟨available, rfl⟩

theorem entry_fault_rejects_nonzero {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World) {fault : NativeWord64.Fault} (failed : state.fault = some fault)
    (slot claimed : Word) (nonzero : claimed.val ≠ 0) (after : TargetState World) :
    ¬ TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls actualFunction
      [.word (encode slot)] state ⟨.word (encode claimed), after⟩ := by
  intro ran
  have same := ((BuiltinArityTarget.actual_function_entry_fault_exact state slot _ failed).mp ran).2
  have words := TargetValue.word.inj (congrArg TargetRawResult.value same)
  exact nonzero (congrArg BitVec.toNat words)

theorem entry_fault_does_not_read_selector {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (frame : TargetFrame) (state : TargetState World) {fault : NativeWord64.Fault}
    (failed : state.fault = some fault)
    (root : List NativeIR.Instruction) :
    TargetRun NativeOpsSourceGuestSnapshot.expectedInterface heap calls .word root actualFunction.body
      frame state ⟨.returned (.word 0), frame, state⟩ :=
  (BuiltinArityTarget.actual_body_entry_fault_exact frame state failed root _).mpr rfl

theorem unavailable_frame_has_no_target_run {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World) (slot : Word)
    (unavailable : ∀ storage, ¬ targetFreshFrame state.memory storage)
    (out : TargetRawResult World) :
    ¬ TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls actualFunction
      [.word (encode slot)] state out := by
  intro ran
  cases ran with
  | run fresh _ _ _ => exact unavailable _ fresh

end Mettapedia.Languages.VibeITP.Native.BuiltinArityControls
