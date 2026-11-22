import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.Buckets

/-!
# Budgets, hints and regions answer yes under one condition

The tree's budgeted certificate checker (`CheckerTower.certDecider`, a `Decider` whose procedure takes
the first answer up to the budget) answers yes at budget `k` exactly on the budget region `k`
(`certDecider_equal_iff`): the instances with a certificate at most `k`. A hint `k` is the same search
(`hinted_eq_budgetRegion`). So on a certified instance the ambient check at budget `k`, the tree's
procedure at budget `k`, and a region's search with the bound `k` all say yes exactly when the least
certificate is at most `k` (`same_yes_condition`): **a region does not find certificates sooner**. What
a region adds is the no: with its computed bound, "not found" is a refutation
(`not_certified_of_hinted_false`), where the ambient check is never decided on an uncertified instance
(`certDecider_never_different`, `certDecider_undecided_of_uncertified`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions

open CheckerTower (Certified certDecider)
open NativeTypesOnTheStep.Computing
open UnificationWithLevels.TreeFibre.Budgets

section SearchBudgets

variable {Q : Type} (R : ℕ → Q → Bool)

/-- **A hint is a budget of the ambient search.** -/
theorem hinted_eq_budgetRegion (q : Q) (k : ℕ) : hinted R q k = budgetRegion R k q := rfl

/-- **The tree's budgeted certificate checker answers yes at budget `k` exactly on the budget region
`k`.** -/
theorem certDecider_equal_iff (q : Q) (k : ℕ) :
    (certDecider R).procedure.verdict k q = .equal ↔ budgetRegion R k q = true := by
  unfold budgetRegion
  rw [anyBelow_iff]
  constructor
  · intro equal
    by_contra absentAll
    have undecided : (certDecider R).verdict k q = .undecided := by
      refine (certDecider R).verdict_undecided_iff.mpr fun j le => ?_
      have notFound : ¬ R j q = true := fun found => absentAll ⟨j, Nat.lt_succ_of_le le, found⟩
      simp [certDecider, notFound]
    have same : (certDecider R).procedure.verdict k q = (certDecider R).verdict k q := rfl
    rw [same, undecided] at equal
    exact Budgeted.Verdict.noConfusion equal
  · rintro ⟨n, lt, found⟩
    have decided : (certDecider R).procedure.verdict k q ≠ .undecided := by
      intro undecided
      have absent := ((certDecider R).verdict_undecided_iff.mp undecided) n (Nat.le_of_lt_succ lt)
      have present : (certDecider R).attempt n q = some ⟨n, found⟩ := dif_pos found
      rw [present] at absent
      exact Option.some_ne_none _ absent
    have notDifferent : (certDecider R).procedure.verdict k q ≠ .different :=
      (certDecider R).verdict_ne_different (fun _ => rfl) k
    cases h : (certDecider R).procedure.verdict k q with
    | equal => rfl
    | different => exact absurd h notDifferent
    | undecided => exact absurd h decided

/-- **The ambient check never says no.** -/
theorem certDecider_never_different (q : Q) (k : ℕ) :
    (certDecider R).procedure.verdict k q ≠ .different :=
  (certDecider R).verdict_ne_different (fun _ => rfl) k

/-- **On an uncertified instance the ambient check is undecided at every budget.** -/
theorem certDecider_undecided_of_uncertified {q : Q} (uncertified : ¬ Certified R q) (k : ℕ) :
    (certDecider R).procedure.verdict k q = .undecided := by
  cases h : (certDecider R).procedure.verdict k q with
  | equal =>
    obtain ⟨n, _, found⟩ := (anyBelow_iff R q (k + 1)).mp ((certDecider_equal_iff R q k).mp h)
    exact absurd ⟨n, found⟩ uncertified
  | different => exact absurd h (certDecider_never_different R q k)
  | undecided => rfl

/-- **One condition for yes**: on a certified instance the tree's procedure at budget `k`, the ambient
search at budget `k` and the search with hint `k` all answer exactly when the least certificate is at
most `k`. -/
theorem same_yes_condition {q : Q} (certified : Certified R q) (k : ℕ) :
    ((certDecider R).procedure.verdict k q = .equal ↔ Nat.find certified ≤ k) ∧
      (budgetRegion R k q = true ↔ Nat.find certified ≤ k) ∧
      (hinted R q k = true ↔ Nat.find certified ≤ k) :=
  ⟨(certDecider_equal_iff R q k).trans (hinted_iff_least_le R certified k),
    hinted_iff_least_le R certified k, hinted_iff_least_le R certified k⟩

end SearchBudgets

namespace Controls

/-- Control: for `9` the tree's procedure says yes at budget `3` and not at budget `2`. -/
theorem square_procedure :
    (certDecider squareR).procedure.verdict 3 9 = .equal ∧
      (certDecider squareR).procedure.verdict 2 9 ≠ .equal :=
  ⟨(certDecider_equal_iff squareR 9 3).mpr (by decide),
    fun yes => absurd ((certDecider_equal_iff squareR 9 2).mp yes) (by decide)⟩

end Controls

#print axioms hinted_eq_budgetRegion
#print axioms certDecider_equal_iff
#print axioms certDecider_never_different
#print axioms certDecider_undecided_of_uncertified
#print axioms same_yes_condition
#print axioms Controls.square_procedure

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions
