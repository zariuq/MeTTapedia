import Mettapedia.GSLT.LanguageDef.FirstOrderRules

/-! # Soundness of a checked first-order rule instance -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.FirstOrderRules

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)

/-- Read an ordered list of premises as curried hypotheses of a conclusion. -/
def premisesImply {α : Type*} (holds : α → Prop) (conclusion : Prop) : List α → Prop
  | [] => conclusion
  | premise :: rest => holds premise → premisesImply holds conclusion rest

theorem premisesImply_iff {α : Type*} (holds : α → Prop) (conclusion : Prop)
    (premises : List α) :
    premisesImply holds conclusion premises ↔ ((∀ premise ∈ premises, holds premise) → conclusion) := by
  induction premises with
  | nil => simp [premisesImply]
  | cons premise rest inductionHypothesis =>
      simp [premisesImply, inductionHypothesis, and_imp]

theorem FORule.sound_of_shape {rule : FORule} {args premises : List Pattern} {conclusion : Pattern}
    {P : Pattern → Prop}
    (shape : rule.instPremises args = premises ∧ rule.instConclusion args = conclusion)
    (sound : premisesImply P (P conclusion) premises)
    (valid : ∀ premise ∈ rule.instPremises args, P premise) : P (rule.instConclusion args) := by
  rw [shape.1] at valid
  rw [shape.2]
  exact (premisesImply_iff P (P conclusion) premises).mp sound valid

end Mettapedia.GSLT.LanguageDef.FirstOrderRules
