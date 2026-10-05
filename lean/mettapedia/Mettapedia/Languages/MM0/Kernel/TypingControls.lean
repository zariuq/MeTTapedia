import Mettapedia.Languages.MM0.Kernel.Typing

/-! # Saturation, sorts and bound-slot controls for MM0 expression typing -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.TypingControls

private def signature : TermSignature
  | 0 => some ⟨[.bound 0, .regular 1 {0}], 1, ∅⟩
  | 1 => some ⟨[], 0, ∅⟩
  | 2 => some ⟨[.regular 0 ∅], 1, ∅⟩
  | _ => none

private def context : Context := [.bound 0, .regular 1 {0}, .regular 0 ∅, .bound 1]

theorem partial_application_retains_binders :
    Preterm.infer signature context (.app (.term 0) (.var 0)) =
      some ([.regular 1 {0}], 1) := by decide

theorem saturated_application_accepted :
    Preterm.infer signature context (.applyArgs (.term 0) [.var 0, .var 1]) =
      some ([], 1) := by decide

theorem regular_variable_in_bound_slot_rejected :
    Preterm.infer signature context (.app (.term 0) (.var 2)) = none := by decide

theorem constant_of_same_sort_in_bound_slot_rejected :
    Preterm.infer signature context (.app (.term 0) (.term 1)) = none := by decide

theorem wrong_sort_bound_variable_rejected :
    Preterm.infer signature context (.app (.term 0) (.var 3)) = none := by decide

theorem partial_argument_in_regular_slot_rejected :
    Preterm.infer signature context (.app (.term 2) (.term 0)) = none := by decide

theorem bound_variable_in_regular_slot_accepted :
    Preterm.infer signature context (.app (.term 2) (.var 0)) = some ([], 1) := by decide

theorem overapplication_rejected :
    Preterm.infer signature context (.app (.term 1) (.var 0)) = none := by decide

theorem undefined_symbol_rejected : Preterm.infer signature context (.term 3) = none := by decide

theorem ill_typed_bound_application_has_no_derivation :
    ¬ ∃ remaining sort,
      Preterm.HasType signature context (.app (.term 0) (.term 1)) remaining sort :=
  (Preterm.infer_none_iff _ _ _).mp constant_of_same_sort_in_bound_slot_rejected

end Mettapedia.Languages.MM0.Kernel.TypingControls
