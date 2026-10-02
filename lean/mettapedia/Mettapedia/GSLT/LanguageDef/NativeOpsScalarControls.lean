import Mettapedia.GSLT.LanguageDef.NativeOpsScalarObservation

/-! Controls for actual emitted scalar runs, including missing-guard behavior. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.ScalarControls

open NativeIR (Instruction)
open NativeWord64 (Word encode)

theorem wraparound_addition_executes {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (frame : TargetFrame) (state : TargetState World) (identity : Nat)
    (unused : frame.temporaryNames.contains identity = false) :
    TargetRun interface heap calls .word []
      [.temporary identity .word (.binary (.word .add) (.word (BitVec.allOnes 64)) (.word 1))]
      frame state ⟨.normal, targetDeclareTemporary frame identity (.word 0), state⟩ := by
  exact (lowered_word_success_exact .add (NativeWord64.bounded 64 (2 ^ 64 - 1)) 1 0
    (.word _) (.word _) unused (by decide +kernel) [] _).mpr rfl

theorem division_by_zero_cannot_complete_normally {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (frame : TargetFrame) (state : TargetState World) (identity : Nat) (left : Word)
    {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls .bool []
      [.checkedNumericGuard .div (.word 0),
        .temporary identity .word (.binary (.word .div) (.word (encode left)) (.word 0))]
      frame state out) : out.flow ≠ .normal := by
  have exactOut := (lowered_word_fault_exact .div left 0 .divisionByZero
    (.word 0) rfl .boolean [] out).mp ran
  rw [exactOut]
  intro impossible; cases impossible

theorem shift_by_word_width_cannot_complete_normally {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (frame : TargetFrame) (state : TargetState World) (identity : Nat) (left : Word)
    {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls .word []
      [.checkedNumericGuard .shl (.word 64),
        .temporary identity .word (.binary (.word .shl) (.word (encode left)) (.word 64))]
      frame state out) : out.flow ≠ .normal := by
  have exactOut := (lowered_word_fault_exact .shl left 64 .shiftOutOfRange
    (.word 64) rfl .unsignedWord [] out).mp ran
  rw [exactOut]
  intro impossible; cases impossible

theorem refusal_keeps_the_function_default_type {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (frame : TargetFrame) (state : TargetState World) (identity : Nat) (left : Word)
    {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls (.ref (.named "Term")) []
      [.checkedNumericGuard .div (.word 0),
        .temporary identity .word (.binary (.word .div) (.word (encode left)) (.word 0))]
      frame state out) : out.flow = .returned (.reference none) := by
  have exactOut := (lowered_word_fault_exact .div left 0 .divisionByZero
    (.word 0) rfl (.nullPointer _) [] out).mp ran
  rw [exactOut]

theorem numeric_refusal_keeps_an_earlier_fault {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (frame : TargetFrame) (state : TargetState World) (identity : Nat) (left : Word)
    (previous : state.fault = some .resourceFault) {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls .word []
      [.checkedNumericGuard .div (.word 0),
        .temporary identity .word (.binary (.word .div) (.word (encode left)) (.word 0))]
      frame state out) : out.state.fault = some .resourceFault := by
  have exactOut := (lowered_word_fault_exact .div left 0 .divisionByZero
    (.word 0) rfl .unsignedWord [] out).mp ran
  rw [exactOut, target_first_fault state .resourceFault .divisionByZero previous]
  exact previous

theorem missing_division_guard_has_no_run {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (frame : TargetFrame) (state : TargetState World) (identity : Nat) (left : BitVec 64)
    (out : TargetBlockOutcome World) :
    ¬ TargetRun interface heap calls .word []
      [.temporary identity .word (.binary (.word .div) (.word left) (.word 0))] frame state out := by
  have noInstruction : ∀ out, ¬ TargetInstructionEval interface heap calls .word
      (.temporary identity .word (.binary (.word .div) (.word left) (.word 0))) frame state out := by
    intro out ran
    cases ran with
    | temporary _ computed =>
        cases computed with
        | binary readLeft readRight computed =>
            cases target_atom_unique readLeft (.word left)
            cases target_atom_unique readRight (.word 0)
            rw [unchecked_division_zero_is_undefined] at computed
            cases computed
  intro ran
  cases ran with
  | next first _ => exact noInstruction _ first
  | «return» first => exact noInstruction _ first
  | resume first _ _ => exact noInstruction _ first
  | escape first _ => exact noInstruction _ first

theorem unsigned_byte_cast_executes {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (frame : TargetFrame) (state : TargetState World) (identity : Nat)
    (unused : frame.temporaryNames.contains identity = false) :
    TargetRun interface heap calls .byte []
      [.temporary identity .byte (.unary .toByte (.word (BitVec.allOnes 64)))]
      frame state ⟨.normal, targetDeclareTemporary frame identity (.byte 255), state⟩ := by
  exact (lowered_unary_success_exact .toByte
    (.word (NativeWord64.bounded 64 (2 ^ 64 - 1))) (.byte 255)
    (.word _) unused rfl [] _).mpr rfl

end Mettapedia.GSLT.LanguageDef.NativeOps.ScalarControls
