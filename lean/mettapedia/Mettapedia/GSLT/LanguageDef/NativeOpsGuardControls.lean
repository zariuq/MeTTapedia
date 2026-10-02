import Mettapedia.GSLT.LanguageDef.NativeOpsMemoryGuards
import Mettapedia.GSLT.LanguageDef.NativeOpsTyping

/-! Concrete storage refusal order and lexical admission controls. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOpsGuardControls

open NativeWord64 NativeOpsMemoryGuards NativeOps

private def w (n : Nat) : Word := bounded 64 n

theorem zero_width_refuses_even_empty :
    targetExtent (encode (w 0)) (encode (w 0)) = .error .invalidRequest := by decide +kernel

theorem overflowing_extent_precedes_index_and_null :
    targetIndex (encode (w (2 ^ 64 - 1))) (encode (w 2)) (encode (w (2 ^ 64 - 1))) false =
      .error .lengthOverflow := by decide +kernel

theorem index_bound_precedes_null :
    targetIndex (encode (w 4)) (encode (w 8)) (encode (w 4)) false =
      .error .indexOutOfBounds := by decide +kernel

theorem valid_index_reports_exact_offset :
    targetIndex (encode (w 4)) (encode (w 8)) (encode (w 3)) true =
      .ok (encode (w 24)) := by decide +kernel

theorem null_valid_index_refuses :
    targetIndex (encode (w 4)) (encode (w 8)) (encode (w 3)) false =
      .error .nullReference := by decide +kernel

theorem empty_slice_ignores_null :
    targetSlice (encode (w 4)) (encode (w 8)) (encode (w 4)) (encode (w 0)) false =
      .ok none := by decide +kernel

theorem beyond_end_empty_slice_refuses :
    targetSlice (encode (w 4)) (encode (w 8)) (encode (w 5)) (encode (w 0)) false =
      .error .indexOutOfBounds := by decide +kernel

theorem slice_offset_and_count_are_independent :
    targetSlice (encode (w 9)) (encode (w 4)) (encode (w 3)) (encode (w 6)) true =
      .ok (some (encode (w 12))) := by decide +kernel

theorem slice_count_cannot_wrap_remaining :
    targetSlice (encode (w 9)) (encode (w 4)) (encode (w 3)) (encode (w (2 ^ 64 - 1))) true =
      .error .indexOutOfBounds := by decide +kernel

theorem empty_null_free_accepts :
    targetFreeGuard (encode (w 0)) (encode (w 8)) false none = .ok () := by decide +kernel

theorem wrong_owned_extent_refuses :
    targetFreeGuard (encode (w 2)) (encode (w 8)) true (some (encode (w 8))) =
      .error .notOwned := by decide +kernel

theorem borrowed_storage_cannot_be_freed :
    targetFreeGuard (encode (w 1)) (encode (w 8)) true none =
      .error .notOwned := by decide +kernel

theorem null_nonempty_free_cannot_claim_ownership :
    targetFreeGuard (encode (w 1)) (encode (w 8)) false (some (encode (w 8))) =
      .error .notOwned := by decide +kernel

theorem exact_owned_extent_free_accepts :
    targetFreeGuard (encode (w 2)) (encode (w 8)) true (some (encode (w 16))) =
      .ok () := by decide +kernel

theorem empty_allocation_ignores_metadata_and_live_bytes :
    targetAllocationExtent (encode (w 0)) (encode (w 8)) (encode (w (2 ^ 64 - 1)))
      (encode (w (2 ^ 64 - 1))) = .ok none := by decide +kernel

theorem allocation_metadata_overflow_refuses :
    targetAllocationExtent (encode (w (2 ^ 64 - 1))) (encode (w 1)) (encode (w 1))
      (encode (w 0)) = .error .lengthOverflow := by decide +kernel

theorem allocation_live_bytes_overflow_refuses :
    targetAllocationExtent (encode (w 1)) (encode (w 8)) (encode (w 24))
      (encode (w (2 ^ 64 - 8))) = .error .lengthOverflow := by decide +kernel

theorem prior_fault_precedes_invalid_allocator :
    targetChecked (some .divisionByZero) false false (fun _ => .ok (w 7)) =
      .error .divisionByZero := rfl

private def pairInterface : Interface :=
  { records := [{ name := "Pair", fields := [{name := "n", type := .word}] }]
    opaques := []
    functions := [{name := "make", parameters := [], result := .named "Pair"}]
    externals := [] }

theorem value_record_field_reads_accept :
    inferExpr pairInterface [] (.field (.call "make" []) "n") = some .word := by decide +kernel

theorem temporary_value_record_field_address_refuses :
    inferLocation pairInterface [] (.field (.call "make" []) "n") = none := by decide +kernel

theorem stored_value_record_field_address_accepts :
    inferLocation pairInterface [("p", .named "Pair")]
      (.field (.variable "p") "n") = some .word := by decide +kernel

theorem active_variable_shadow_refuses :
    checkBlock pairInterface .unit 0 [("x", .word)]
      [.declare "x" .word (.word (w 0))] = none := by decide +kernel

theorem nested_variable_does_not_escape :
    checkBlock pairInterface .unit 0 []
      [.block [.declare "x" .word (.word (w 0))], .effect (.variable "x")] = none :=
  by decide +kernel

theorem switch_does_not_authorize_loop_break :
    checkBlock pairInterface .unit 0 [] [.switch (.word (w 0)) [] [.break]] = none :=
  by decide +kernel

theorem switch_inside_loop_break_accepts :
    checkBlock pairInterface .unit 0 []
      [.while (.bool true) [.switch (.word (w 0)) [] [.break]]] = some [] := by decide +kernel

theorem while_does_not_manufacture_nonunit_return :
    checkFunction pairInterface
      { header := { name := "bad", parameters := [], result := .word }
        body := [.while (.bool true) [.return (some (.word (w 0)))]] } = false :=
  by decide +kernel

end Mettapedia.GSLT.LanguageDef.NativeOpsGuardControls
