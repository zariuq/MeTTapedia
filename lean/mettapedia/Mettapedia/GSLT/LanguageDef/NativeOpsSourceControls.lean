import Mettapedia.GSLT.LanguageDef.NativeOpsSource

/-! Admission controls for authored numeric, catalogue and control forms. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.SourceControls

open Algorithms.MeTTa.Simple.Parser (SExpr)

private def scalarFunction : SExpr :=
  .list [.atom "function", .atom "increment", .list [.list [.atom "x", .atom "u64"]],
    .atom "u64", .list [.atom "block", .list [.atom "return",
      .list [.atom "add", .list [.atom "var", .atom "x"], .list [.atom "u64", .atom "1"]]]]]

private def scalarSource : SExpr :=
  .list [.atom "gslt-native-ops-v1", .atom "Counter", scalarFunction]

private def callback : External :=
  ⟨⟨"observe", [⟨"value", .word⟩], .bool⟩, "native_observe", .pure, some "native.h"⟩

private def supplied : Catalogue := ⟨[], [callback]⟩

private def callbackSource : SExpr :=
  .list [.atom "extern", .atom "observe", .atom "\"native_observe\"",
    .list [.list [.atom "value", .atom "u64"]], .atom "bool", .atom "pure"]

theorem maximum_word_admits :
    (word? (.atom "18446744073709551615")).isSome = true := by cbv

theorem next_word_refuses : word? (.atom "18446744073709551616") = none := by cbv

theorem nonminimal_decimal_admits : natural? (.atom "0007") = some 7 := by cbv

theorem negative_zero_admits : natural? (.atom "-000") = some 0 := by cbv

theorem negative_nonzero_refuses : natural? (.atom "-1") = none := by cbv

theorem separated_digits_refuse : natural? (.atom "1_000") = none := by cbv

theorem prefixed_hex_refuses : natural? (.atom "0xff") = none := by cbv

theorem empty_decimal_refuses : natural? (.atom "") = none := by cbv

theorem signed_plus_refuses : natural? (.atom "+1") = none := by cbv

theorem leading_underscore_c_name_refuses : validCName "_kernel" = false := by cbv

theorem ordinary_c_name_admits : validCName "native_observe" = true := by cbv

theorem c_keyword_refuses : validCName "return" = false := by cbv

theorem nested_header_admits : validHeader "native/ops_v1.h" = true := by cbv

theorem empty_header_component_refuses : validHeader "native//ops.h" = false := by cbv

theorem parent_directory_header_refuses : validHeader "../ops.h" = false := by cbv

theorem exact_callback_admits :
    declaration? supplied callbackSource = some (.external callback) := by cbv

theorem callback_requires_catalogue : declaration? ⟨[], []⟩ callbackSource = none := by cbv

theorem callback_effect_mismatch_refuses : declaration? supplied
    (.list [.atom "extern", .atom "observe", .atom "\"native_observe\"",
      .list [.list [.atom "value", .atom "u64"]], .atom "bool", .atom "effect"]) = none := by cbv

theorem callback_result_mismatch_refuses : declaration? supplied
    (.list [.atom "extern", .atom "observe", .atom "\"native_observe\"",
      .list [.list [.atom "value", .atom "u64"]], .atom "u64", .atom "pure"]) = none := by cbv

theorem executable_scalar_source_admits :
    (admitProgram? ⟨[], []⟩ scalarSource).isSome = true := by cbv

theorem opaque_unlisted_c_body_refuses : declaration? ⟨[], []⟩
    (.list [.atom "extern", .atom "kernel", .atom "\"arbitrary_kernel_body\"",
      .list [], .atom "bool", .atom "pure"]) = none := by cbv

theorem malformed_expression_arity_refuses : expr?
    (.list [.atom "add", .list [.atom "u64", .atom "1"]]) = none := by cbv

theorem unknown_expression_operator_refuses : expr?
    (.list [.atom "raw-c", .atom "\"return true;\""]) = none := by cbv

end Mettapedia.GSLT.LanguageDef.NativeOps.SourceControls
