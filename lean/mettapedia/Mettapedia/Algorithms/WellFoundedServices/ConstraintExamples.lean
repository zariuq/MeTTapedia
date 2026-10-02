import Mettapedia.Algorithms.WellFoundedServices.ConstraintPlanning

/-!
# Constraint planning: choosing package versions

Four packages, each with a few versions, and compatibility rules between them.
The kernel runs the measure-based search; `solveAcc_eq` transfers every
result to the accessibility route.

Positive controls: a plan found with either strategy, and a refutation of the
tightened problem that the checker accepts. Negative controls: certificates the
checker rejects, and a plan that is not a solution.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.WellFoundedServices.ConstraintExamples

inductive Pkg where
  | web | db | log | auth
  deriving DecidableEq, Repr

open Pkg

def versions : Pkg → List ℕ
  | web => [1, 2, 3]
  | db => [1, 2]
  | log => [1, 2, 3]
  | auth => [1, 2]

/-- `x` at version `v` or later requires `y` to satisfy `ok`. -/
def needs (x : Pkg) (v : ℕ) (y : Pkg) (ok : ℕ → Bool) : Constraint Pkg ℕ where
  scope := [x, y]
  allows
    | [a, b] => decide (a < v) || ok b
    | _ => true

/-- `x` at version `v` cannot be combined with `y` at version `w`. -/
def conflicts (x : Pkg) (v : ℕ) (y : Pkg) (w : ℕ) : Constraint Pkg ℕ where
  scope := [x, y]
  allows
    | [a, b] => !(a == v && b == w)
    | _ => true

/-- The request: `x` at version `v` or later. -/
def atLeast (x : Pkg) (v : ℕ) : Constraint Pkg ℕ where
  scope := [x]
  allows
    | [a] => decide (v ≤ a)
    | _ => true

def rules : List (Constraint Pkg ℕ) :=
  [atLeast web 2, needs web 2 db (· == 2), needs web 3 log (2 ≤ ·), conflicts auth 2 db 2,
    needs log 3 auth (· == 2)]

/-- The planning problem. -/
def problem : Problem Pkg ℕ := ⟨[web, db, log, auth], versions, rules⟩

theorem problem_wellFormed : problem.WellFormed where
  nodup := by decide
  scopes := by decide

/-- The plan found with the first-variable strategy. -/
example : (problem.solve .first).getLeft? = some [(auth, 1), (log, 1), (db, 2), (web, 2)] := by
  decide

/-- The plan found with the fewest-values strategy. -/
example : (problem.solve (.fewestValues problem)).getLeft? =
    some [(log, 1), (auth, 1), (db, 2), (web, 2)] := by
  decide

theorem plan_is_solution : problem.Solution [(auth, 1), (log, 1), (db, 2), (web, 2)] :=
  problem.solve_inl .first problem_wellFormed (Sum.getLeft?_eq_some_iff.1 (by decide))

/-- Negative control: web version 1 violates the request. -/
theorem old_web_not_solution : ¬ problem.Solution [(auth, 1), (log, 1), (db, 2), (web, 1)] := by
  rintro ⟨-, h⟩
  obtain ⟨ds, hds, hallow⟩ := h (atLeast web 2) List.mem_cons_self
  have e : values [(auth, 1), (log, 1), (db, 2), (web, 1)] (atLeast web 2).scope = some [1] := by
    decide
  rw [e] at hds
  cases hds
  exact absurd hallow (by decide)

/-! ## A problem without a plan -/

/-- The same problem with one more rule: web 2 or later also requires auth 2,
which conflicts with db 2. -/
def tightened : Problem Pkg ℕ :=
  ⟨[web, db, log, auth], versions, rules ++ [needs web 2 auth (· == 2)]⟩

theorem tightened_wellFormed : tightened.WellFormed where
  nodup := by decide
  scopes := by decide

/-- The search returns a refutation, and the checker accepts it. -/
example : (tightened.solve .first).isRight = true := by decide
example : (tightened.solve .first).elim (fun _ => false) (tightened.check []) = true := by decide

/-- Hence the tightened problem has no plan. -/
theorem tightened_unsolvable (f : Assignment Pkg ℕ) : ¬ tightened.Solution f := by
  have h : (tightened.solve .first).isRight = true := by decide
  cases e : tightened.solve .first with
  | inl g => rw [e] at h; cases h
  | inr r => exact (tightened.solve_inr .first e).2 f

/-- The certificate returned with the fewest-values strategy: web 1 violates the
request (rule 0), db 1 violates rule 1, and with db 2 either auth version breaks
rule 5 or rule 3. -/
def certificate : Refutation Pkg :=
  .split web [.conflict 0,
    .split db [.conflict 1, .split auth [.conflict 5, .conflict 3]],
    .split db [.conflict 1, .split auth [.conflict 5, .conflict 3]]]

example : (tightened.solve (.fewestValues tightened)).getRight? = some certificate := by rfl

example : tightened.check [] certificate = true := by decide

/-! ## Rejected certificates -/

/-- Negative control: no constraint is violated before anything is assigned. -/
example : tightened.check [] (.conflict 0) = false := by decide

/-- Negative control: a split must have one branch per version. -/
example : tightened.check [] (.split web [.conflict 0]) = false := by decide

/-- Negative control: the satisfiable problem accepts no certificate. -/
example (r : Refutation Pkg) : problem.check [] r = false := by
  cases h : problem.check [] r with
  | false => rfl
  | true => exact absurd plan_is_solution (problem.no_solution h _)

end Mettapedia.Algorithms.WellFoundedServices.ConstraintExamples
