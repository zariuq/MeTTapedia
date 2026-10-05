import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ExtractionComparisonLaws

/-! # Checked standard-library composition for extracted computations -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction

/-- The second operand belongs only to the true branch. -/
theorem applies_and_elimination {program : Program} {host : Host}
    (head : String) (captures : List Term) (left right : Bool)
    (whenFalse : Applies program host head (.sym "False" :: captures) (.sym "False"))
    (whenTrue : Applies program host head (.sym "True" :: captures) (boolean right)) :
    Applies program host head (boolean left :: captures) (boolean (left && right)) := by
  cases left with
  | false => exact whenFalse
  | true => exact whenTrue

theorem decision_not (condition : Prop) [Decidable condition] [Decidable (¬ condition)] :
    decide (¬ condition) = (if condition then false else true) := by
  by_cases holds : condition <;> simp [holds]

theorem boolean_decision_true (condition : Prop) [Decidable condition] (holds : condition) :
    boolean (decide condition) = .sym "True" := by simp [boolean, holds]

theorem boolean_decision_false (condition : Prop) [Decidable condition] (fails : ¬ condition) :
    boolean (decide condition) = .sym "False" := by simp [boolean, fails]

theorem applies_arguments_congr {program : Program} {host : Host} {head : String}
    {actual reduced : List Term} {result : Term}
    (computed : Applies program host head reduced result) (same : actual = reduced) :
    Applies program host head actual result := by cases same; exact computed

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction
