import Mettapedia.Languages.MeTTa.PeTTa.GSLTBindingPatterns

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.GSLTBindingPatterns.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open GSLTDataPatterns Unifying ListView

private def consData : Atom :=
  .expression [.symbol "cons", .symbol "a", .expression [.symbol "b"]]

theorem literal_cons_data_accepts :
    unifyBinding [] (quoted consData) consData = .ok [] := by decide +kernel

theorem literal_cons_data_is_not_a_list_view :
    unifyBinding [] (quoted consData) (.expression [.symbol "a", .symbol "b"]) = .clash := by
  decide +kernel

theorem literal_quote_data_accepts :
    unifyBinding [] (quoted (.expression [.symbol "quote", .symbol "a"]))
      (.expression [.symbol "quote", .symbol "a"]) = .ok [] := by decide +kernel

theorem literal_quote_data_is_not_activated :
    unifyBinding [] (quoted (.expression [.symbol "quote", .symbol "a"]))
      (.symbol "a") = .clash := by decide +kernel

theorem nullary_constructor_is_not_its_symbol :
    unifyBinding [] (quoted (.expression [.symbol "Nullary"])) (.symbol "Nullary") = .clash := by
  decide +kernel

theorem string_is_not_a_symbol :
    unifyBinding [] (quoted (.grounded (.string "a"))) (.symbol "a") = .clash := by decide +kernel

theorem boolean_is_not_its_spelling :
    unifyBinding [] (quoted (.grounded (.bool true))) (.symbol "True") = .clash := by decide +kernel

theorem incoming_bindings_are_respected :
    unifyBinding [("x", .grounded (.int 7))] (quoted (.var "x"))
      (.grounded (.int 9)) = .clash := by decide +kernel

theorem repeated_variables_reject_conflicting_values :
    unifyBinding [] (quoted (.expression [.var "x", .var "x"]))
      (.expression [.grounded (.int 7), .grounded (.int 9)]) = .clash := by decide +kernel

theorem repeated_variables_accept_open_values :
    ∃ bound, unifyBinding []
      (quoted (.expression [.symbol "Pair", .var "x", .var "x"]))
      (.expression [.symbol "Pair", .var "u", .grounded (.int 7)]) = .ok bound := by
  apply (quoted_accepts_iff _ _ _ idempotent_nil).mpr
  refine ⟨fun _ => .grounded (.int 7), ?_, ?_⟩
  · intro equation member
    cases member
  · change PatternHolds _ _ _
    rw [patternHolds_iff]
    rfl

theorem open_tail_uses_the_general_path :
    checked "cons-atom" (.expression [.symbol "cons-atom", .var "head", .var "tail"]) = none := by
  decide +kernel

theorem computation_uses_the_general_path :
    checked "cons-atom" (.expression [.symbol "cons-atom",
      .expression [.symbol "+", .grounded (.int 1), .grounded (.int 1)], .expression []]) = none := by
  decide +kernel

/-- The same words remain legal source data when explicitly encoded. -/
theorem open_tail_words_are_valid_source_data :
    checked "cons-atom" (encode "cons-atom"
      (.expression [.symbol "cons-atom", .var "head", .var "tail"])) =
      some (quoted (.expression [.symbol "cons-atom", .var "head", .var "tail"])) :=
  checked_encode _ _

theorem unicode_and_unknown_escape_text_roundtrip :
    checked "cons-atom" (encode "cons-atom"
      (.expression [.symbol "λ", .grounded (.string "\\q"), .var "x", .var "x"])) =
      some (quoted (.expression [.symbol "λ", .grounded (.string "\\q"), .var "x", .var "x"])) :=
  checked_encode _ _

end Mettapedia.Languages.MeTTa.PeTTa.GSLTBindingPatterns.Controls
