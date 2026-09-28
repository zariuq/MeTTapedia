import Mettapedia.GSLT.LanguageDef.AffineExpressionNativeTypes
import Mettapedia.GSLT.LanguageDef.AffineExpressionControls

/-!
# Native-type controls for affine optimization

Concrete examples distinguish structural admission, behavioral result
refinement, source arithmetic safety and budget. The endpoint checker is
exercised for positive, zero and negative slopes.
-/

namespace Mettapedia.GSLT.AffineExpression.NativeTypes.Controls

open Mettapedia.GSLT.AffineExpression.Controls

theorem horner_range :
    ∀ state : Int, 0 ≤ state → state ≤ 10 →
      Holds ![2, 3] state horner (resultType ![2, 3] state (InRange 3 23)) := by
  apply (checkEndpoints_exact _ _ _ horner_admitted 0 10 3 23 (by decide)).mp
  decide

theorem negative_slope_range :
    ∀ state : Int, 0 ≤ state → state ≤ 10 →
      Holds ![-2, 3] state horner (resultType ![-2, 3] state (InRange (-17) 3)) := by
  apply (checkEndpoints_exact _ _ _ horner_admitted 0 10 (-17) 3 (by decide)).mp
  decide

theorem constant_range : checkEndpoints ![0, 3] hornerForm (-100) 100 3 3 = true := by
  decide

theorem narrower_range_rejected :
    checkEndpoints ![2, 3] hornerForm 0 10 3 22 = false := by decide

theorem source_guard_accepts : checkGuard ![2, 3] 10 (-128) 127 5 horner = true := by
  decide

theorem insufficient_budget_rejected :
    checkGuard ![2, 3] 10 (-128) 127 4 horner = false := by decide

/-- Behavioral eventual admission cannot replace structural admission. -/
theorem eventual_is_insufficient :
    Holds Fin.elim0 9 square (eventuallyAdmittedType Fin.elim0 9) ∧
      ¬ Holds Fin.elim0 9 square (admissionType Fin.elim0 9) := by
  constructor
  · exact every_expression_eventually_admitted _ _ _
  · rw [admission_membership]
    decide

/-- Result refinement and intermediate safety are different native types. -/
theorem final_range_does_not_imply_word_safety :
    Holds Fin.elim0 0 intermediateOverflow
      (resultType Fin.elim0 0 (InRange (-128) 127)) ∧
      ¬ Holds Fin.elim0 0 intermediateOverflow (wordSafeType Fin.elim0 0 (-128) 127) := by
  constructor
  · rw [result_membership]
    decide
  · change ¬ (intermediateOverflow.evalChecked (-128) 127 Fin.elim0 0).isSome = true
    decide

/-- Equal terminal behavior does not preserve every native refinement: the
source budget can distinguish a literal from a computation returning it. -/
theorem terminal_equivalence_is_not_all_native_types :
    (∀ P : Int → Prop,
      Holds Fin.elim0 7 (Expr.lit 0) (resultType Fin.elim0 7 P) ↔
        Holds Fin.elim0 7 (.bin .mul .acc (.lit 0)) (resultType Fin.elim0 7 P)) ∧
    Holds Fin.elim0 7 (Expr.lit 0) (budgetType Fin.elim0 7 0) ∧
    ¬ Holds Fin.elim0 7 (.bin .mul .acc (.lit 0)) (budgetType Fin.elim0 7 0) := by
  constructor
  · intro P
    simp only [result_membership]
    rfl
  · constructor
    · change (Expr.lit (n := 0) 0).work ≤ 0
      decide
    · change ¬ (Expr.bin (n := 0) .mul .acc (.lit 0)).work ≤ 0
      decide

end Mettapedia.GSLT.AffineExpression.NativeTypes.Controls
