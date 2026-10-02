import Mettapedia.GSLT.LanguageDef.NativeWord64Expression

/-! # Boundary and refusal controls for the native unsigned primitive profile -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeWord64.Controls

theorem addition_wraps :
    targetBinary .add 18446744073709551615 1 = .ok 0 := by decide +kernel

theorem subtraction_wraps :
    targetBinary .sub 0 1 = .ok 18446744073709551615 := by decide +kernel

theorem multiplication_wraps :
    targetBinary .mul 18446744073709551615 2 = .ok 18446744073709551614 := by decide +kernel

theorem division_large_word :
    targetBinary .div 18446744073709551615 3 = .ok 6148914691236517205 := by decide +kernel

theorem remainder_large_word :
    targetBinary .mod 18446744073709551615 10 = .ok 5 := by decide +kernel

theorem division_zero_fault :
    targetBinary .div 1 0 = .error .divisionByZero := by decide +kernel

theorem remainder_zero_fault :
    targetBinary .mod 1 0 = .error .divisionByZero := by decide +kernel

theorem division_zero_has_no_result :
    targetBinary .div 1 0 ≠ .ok 0 := by decide +kernel

theorem left_shift_last_count :
    targetBinary .shl 1 63 = .ok 9223372036854775808 := by decide +kernel

theorem left_shift_wraps :
    targetBinary .shl 9223372036854775808 1 = .ok 0 := by decide +kernel

theorem right_shift_unsigned :
    targetBinary .shr 18446744073709551615 63 = .ok 1 := by decide +kernel

theorem left_shift_64_fault :
    targetBinary .shl 1 64 = .error .shiftOutOfRange := by decide +kernel

theorem right_shift_64_fault :
    targetBinary .shr 18446744073709551615 64 = .error .shiftOutOfRange := by decide +kernel

theorem zero_left_shift_64_fault :
    targetBinary .shl 0 64 = .error .shiftOutOfRange := by decide +kernel

theorem maximal_shift_fault :
    targetBinary .shr 1 18446744073709551615 = .error .shiftOutOfRange := by decide +kernel

theorem bit_and_result : targetBinary .band 240 170 = .ok 160 := by decide +kernel
theorem bit_or_result : targetBinary .bor 240 170 = .ok 250 := by decide +kernel
theorem bit_xor_result : targetBinary .bxor 240 170 = .ok 90 := by decide +kernel

theorem complement_zero : targetComplement 0 = 18446744073709551615 := by decide +kernel
theorem complement_maximal : targetComplement 18446744073709551615 = 0 := by decide +kernel

theorem unsigned_high_bit_order :
    targetComparison .gt (9223372036854775808 : BitVec 64) 1 = true := by decide +kernel

theorem unsigned_maximal_not_negative :
    targetComparison .lt (18446744073709551615 : BitVec 64) 0 = false := by decide +kernel

theorem truncation_maximal : targetToByte 18446744073709551615 = 255 := by decide +kernel
theorem truncation_boundary : targetToByte 256 = 0 := by decide +kernel
theorem widening_byte : targetToWord 255 = 255 := by decide +kernel

theorem promoted_byte_order :
    targetComparison .gt (targetToWord 255) (targetToWord 128) = true := by decide +kernel

theorem out_of_range_word_refused : admitWord 18446744073709551616 = none := by decide +kernel

theorem maximal_word_admitted :
    (admitWord 18446744073709551615).map Fin.val = some 18446744073709551615 := by decide +kernel

theorem operand_fault_precedes_division_guard :
    targetOrdered .div (.ok 1) (fun _ => .error .indexOutOfBounds) =
      .error .indexOutOfBounds := rfl

theorem left_fault_precedes_right_fault :
    targetOrdered .add (.error .resourceFault) (fun _ => .error .lengthOverflow) =
      .error .resourceFault := rfl

theorem failed_context_zero_is_refused :
    (targetWithContext .div none 1 0).returned = 0 ∧
      observeContext (targetWithContext .div none 1 0) = .error .divisionByZero :=
  context_zero_placeholder_refused .div 1 0 .divisionByZero division_zero_fault

theorem prior_context_fault_precedes_operator_fault :
    observeContext (targetWithContext .div (some .notOwned) 1 0) = .error .notOwned := rfl

theorem false_and_prunes_fault :
    targetBoolean .and (.ok false) (fun _ => .error .divisionByZero) = .ok false := rfl

theorem true_or_prunes_fault :
    targetBoolean .or (.ok true) (fun _ => .error .shiftOutOfRange) = .ok true := rfl

theorem true_and_preserves_fault :
    targetBoolean .and (.ok true) (fun _ => .error .divisionByZero) = .error .divisionByZero := rfl

theorem false_or_preserves_fault :
    targetBoolean .or (.ok false) (fun _ => .error .shiftOutOfRange) = .error .shiftOutOfRange := rfl

private def faultingEnvironment : TargetEnvironment := fun _ _ => .error .invalidRequest

private def divideByZero : SourceExpression .word :=
  .binary (.word .div) (.literal (bounded 64 1)) (.literal (bounded 64 0))

private def shiftBy64 : SourceExpression .word :=
  .binary (.word .shl) (.literal (bounded 64 1)) (.literal (bounded 64 64))

theorem composed_false_and_prunes_division :
    targetEvaluate faultingEnvironment (lowerScalar
      (.binary .and (.literal false)
        (.binary (.compareWord .eq) divideByZero (.literal (bounded 64 0))))) =
      .ok false := by decide +kernel

theorem composed_true_and_propagates_division :
    targetEvaluate faultingEnvironment (lowerScalar
      (.binary .and (.literal true)
        (.binary (.compareWord .eq) divideByZero (.literal (bounded 64 0))))) =
      .error .divisionByZero := by decide +kernel

theorem composed_operand_order :
    targetEvaluate faultingEnvironment (lowerScalar
      (.binary (.word .add) divideByZero shiftBy64)) = .error .divisionByZero := by decide +kernel

theorem composed_reverse_operand_order :
    targetEvaluate faultingEnvironment (lowerScalar
      (.binary (.word .add) shiftBy64 divideByZero)) = .error .shiftOutOfRange := by decide +kernel

end Mettapedia.GSLT.LanguageDef.NativeWord64.Controls
