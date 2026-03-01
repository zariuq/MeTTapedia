import Mathlib.Data.Bool.Basic

namespace Mettapedia.Logic.Bridges

/-- Canonical Boolean checker for a decidable proposition. -/
def propChecker (p : Prop) [Decidable p] : Bool := decide p

theorem prop_of_checker_true {p : Prop} [Decidable p]
    (h : propChecker p = true) : p := by
  exact Bool.of_decide_true (by simpa [propChecker] using h)

theorem not_prop_of_checker_false {p : Prop} [Decidable p]
    (h : propChecker p = false) : ¬ p := by
  exact Bool.of_decide_false (by simpa [propChecker] using h)

theorem checker_true_of_prop {p : Prop} [Decidable p]
    (hp : p) : propChecker p = true := by
  unfold propChecker
  by_cases h : p
  · simp [h]
  · exact (h hp).elim

theorem checker_false_of_not_prop {p : Prop} [Decidable p]
    (hp : ¬ p) : propChecker p = false := by
  unfold propChecker
  by_cases h : p
  · exact (hp h).elim
  · simp [h]

theorem spec_of_checker_true {α : Type*} {P : α → Prop}
    [DecidablePred P] (checker : α → Bool)
    (hspec : ∀ x, checker x = decide (P x))
    {x : α} (h : checker x = true) : P x := by
  have hdec : decide (P x) = true := by simpa [hspec x] using h
  exact Bool.of_decide_true hdec

theorem not_spec_of_checker_false {α : Type*} {P : α → Prop}
    [DecidablePred P] (checker : α → Bool)
    (hspec : ∀ x, checker x = decide (P x))
    {x : α} (h : checker x = false) : ¬ P x := by
  have hdec : decide (P x) = false := by simpa [hspec x] using h
  exact Bool.of_decide_false hdec

end Mettapedia.Logic.Bridges
