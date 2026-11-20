import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.Cast.Order

/-!
# Exact budget allocation over additive task values

Each task offers finitely many amounts of computation. Each offer has
an additional value and a nonnegative work cost. A task can be skipped.
The table computes one optimum per available budget.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.FiniteBudgetAllocation

structure Offer where
  cost : Nat
  gain : ℚ

abbrev Tasks := List (List Offer)

inductive Feasible : Tasks → Nat → ℚ → Prop
  | done (budget : Nat) : Feasible [] budget 0
  | skip {options : List Offer} {rest : Tasks} {budget : Nat} {gain : ℚ}
      (later : Feasible rest budget gain) : Feasible (options :: rest) budget gain
  | take {options : List Offer} {rest : Tasks} {budget : Nat} {gain : ℚ} (chosen : Offer)
      (present : chosen ∈ options) (affordable : chosen.cost ≤ budget)
      (later : Feasible rest (budget - chosen.cost) gain) :
      Feasible (options :: rest) budget (chosen.gain + gain)

private def remainder {limit : Nat} (budget : Fin (limit + 1)) (cost : Nat) : Fin (limit + 1) :=
  ⟨budget.val - cost, (Nat.sub_le _ _).trans_lt budget.isLt⟩

private def takeValue {limit : Nat} (tail : Vector ℚ (limit + 1)) (budget : Fin (limit + 1))
    (offer : Offer) : ℚ :=
  if offer.cost ≤ budget.val then offer.gain + tail.get (remainder budget offer.cost)
  else tail.get budget

private def values {limit : Nat} (options : List Offer) (tail : Vector ℚ (limit + 1))
    (budget : Fin (limit + 1)) : Finset ℚ :=
  (tail.get budget :: options.map (takeValue tail budget)).toFinset

private theorem values_nonempty {limit : Nat} (options : List Offer) (tail : Vector ℚ (limit + 1))
    (budget : Fin (limit + 1)) : (values options tail budget).Nonempty := by
  exact ⟨tail.get budget, by simp [values]⟩

def table (limit : Nat) : Tasks → Vector ℚ (limit + 1)
  | [] => Vector.replicate _ 0
  | options :: rest =>
    let tail := table limit rest
    Vector.ofFn fun budget => (values options tail budget).max' (values_nonempty options tail budget)

def best (tasks : Tasks) (budget : Nat) : ℚ :=
  (table budget tasks).get (Fin.last budget)

private theorem table_step {limit : Nat} (options : List Offer) (rest : Tasks)
    (budget : Fin (limit + 1)) :
    (table limit (options :: rest)).get budget =
      (values options (table limit rest) budget).max'
        (values_nonempty options (table limit rest) budget) := by
  simp [table, Vector.get, Fin.cast]

theorem feasible_le {limit : Nat} (tasks : Tasks) (budget : Fin (limit + 1))
    (gain : ℚ) (choice : Feasible tasks budget.val gain) : gain ≤ (table limit tasks).get budget := by
  induction tasks generalizing budget gain with
  | nil =>
    cases choice
    simp [table, Vector.get]
  | cons options rest ih =>
    rw [table_step]
    cases choice with
    | skip later =>
      exact (ih budget _ later).trans (Finset.le_max' _ _ (by simp [values]))
    | take chosen present affordable later =>
      have member : takeValue (table limit rest) budget chosen ∈ values options (table limit rest) budget := by
        simp only [values, List.mem_toFinset, List.mem_cons]
        exact Or.inr (List.mem_map.mpr ⟨chosen, present, rfl⟩)
      apply le_trans _ (Finset.le_max' _ _ member)
      simpa only [takeValue, if_pos affordable] using
        add_le_add_right (ih (remainder budget chosen.cost) _ later) chosen.gain

theorem table_attains {limit : Nat} (tasks : Tasks) (budget : Fin (limit + 1)) :
    Feasible tasks budget.val ((table limit tasks).get budget) := by
  induction tasks generalizing budget with
  | nil => simpa [table, Vector.get] using Feasible.done budget.val
  | cons options rest ih =>
    rw [table_step]
    let scores := values options (table limit rest) budget
    let winner := scores.max' (values_nonempty options (table limit rest) budget)
    change Feasible (options :: rest) budget.val winner
    have member : winner ∈ scores := Finset.max'_mem _ _
    have choice : winner ∈ (table limit rest).get budget ::
        options.map (takeValue (table limit rest) budget) := List.mem_toFinset.mp member
    rcases List.mem_cons.mp choice with skipped | candidate
    · rw [skipped]
      exact .skip (ih budget)
    · obtain ⟨chosen, present, value⟩ := List.mem_map.mp candidate
      rw [← value]
      by_cases affordable : chosen.cost ≤ budget.val
      · simp only [takeValue, if_pos affordable]
        exact .take chosen present affordable (ih (remainder budget chosen.cost))
      · simp only [takeValue, if_neg affordable]
        exact .skip (ih budget)

theorem best_optimal (tasks : Tasks) (budget : Nat) :
    Feasible tasks budget (best tasks budget) ∧
      ∀ gain, Feasible tasks budget gain → gain ≤ best tasks budget :=
  ⟨table_attains tasks (Fin.last budget), fun gain h => feasible_le tasks (Fin.last budget) gain h⟩

end Mettapedia.Algorithms.FiniteBudgetAllocation
