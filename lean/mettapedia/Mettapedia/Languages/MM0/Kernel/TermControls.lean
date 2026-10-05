import Mettapedia.Languages.MM0.Kernel.Term

/-! # Positive and refusal controls for MM0 simultaneous substitution -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.TermControls

open Preterm

/-- A replacement is inserted once, not recursively resubstituted. -/
theorem simultaneous_not_recursive :
    substitute (Substitution.ofList [.var 1, .term 7]) (.var 0) = some (.var 1) := by
  decide

theorem simultaneous_wrong_result_rejected :
    ¬ Substitutes (Substitution.ofList [.var 1, .term 7]) (.var 0) (.term 7) := by
  intro derivation
  have accepted := derivation.eval
  simp [substitute, Substitution.ofList] at accepted

/-- Nested applications preserve the original symbol and argument positions. -/
theorem nested_application :
    substitute (Substitution.ofList [.term 3, .app (.term 4) (.var 9)])
      (.app (.app (.term 2) (.var 0)) (.var 1)) =
      some (.app (.app (.term 2) (.term 3)) (.app (.term 4) (.var 9))) := by
  decide

theorem missing_entry_refuses :
    substitute (Substitution.ofList [.term 8]) (.app (.term 2) (.var 1)) = none := by
  decide

theorem missing_entry_has_no_derivation :
    ¬ ∃ result, Substitutes (Substitution.ofList [.term 8])
      (.app (.term 2) (.var 1)) result :=
  (substitute_none_iff _ _).mp missing_entry_refuses

/-- Unsupported indices matter only when they occur in the source. -/
theorem closed_term_needs_no_entries :
    substitute (Substitution.ofList []) (.app (.term 2) (.term 3)) =
      some (.app (.term 2) (.term 3)) := by
  decide

theorem two_stage_substitution :
    substitute
      (Substitution.compose (Substitution.ofList [.term 5, .term 6])
        (Substitution.ofList [.app (.term 2) (.var 1)]))
      (.app (.term 3) (.var 0)) =
      some (.app (.term 3) (.app (.term 2) (.term 6))) := by
  decide

/-- The second stage can refuse a variable inserted successfully by the first. -/
theorem composition_propagates_refusal :
    substitute
      (Substitution.compose (Substitution.ofList []) (Substitution.ofList [.var 1]))
      (.var 0) = none := by
  decide

end Mettapedia.Languages.MM0.Kernel.TermControls
