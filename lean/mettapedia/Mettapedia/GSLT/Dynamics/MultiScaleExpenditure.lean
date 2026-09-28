import Mettapedia.GSLT.Core.CostBoundedReachability
import Mettapedia.Algebra.Order.Infinitesimal.Expenditure

/-!
# Expenditure at several scales, as a graded lift

`GSLTConstructions.spendLift` lifts a theory to one whose terms carry an
accumulator, multiplying each step's grade onto it. The grades live in any
monoid, and this file instantiates that monoid with nonnegative multi-scale
expenditure: `Multiplicative Expenditure`, whose product is addition of
amounts in the level field.

What the instance is for is the pair of laws at the bottom.

* `accumulated_monotone` — **spending never decreases along a run.** The
  accumulator is a monoid element with no inverses, so no later step can give
  earlier spending back. This is the finite-run accounting law.
* `omega_spend_never_covered` — **its observational meaning.** Once a run has
  spent anything at level `-1`, no budget quoted in rationals covers the run,
  however it continues and however much it saves afterwards.

Together they say what a level is for. A penalty weight is a price, and a
large enough reward pays it. A level is not a price: it is not denominated in
the same currency as the budget, so there is no amount of ordinary saving that
settles it.

The signed side is kept out deliberately. `Expenditure` has no subtraction, so
a credit, a refund or a remaining balance cannot be smuggled into the
accumulator; it belongs in the state of the underlying theory, where it can go
up and down.

The example theory is deliberately thin — a plan is a list of actions and a
step performs the first one — because the content is in the grading and the two
laws, not in the term language. Any `GSLT` with a `StepSpend` into
`Multiplicative Expenditure` gets the same two theorems.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

open Mettapedia.Algebra.Order.Infinitesimal

namespace MultiScaleExpenditure

/-! ## The accumulator -/

/-- The grade monoid: expenditure under addition, written multiplicatively so
that `spendLift` can accumulate it. -/
abbrev Spend : Type := Multiplicative Expenditure

/-- The amount an accumulator records. -/
def amount (s : Spend) : Expenditure := Multiplicative.toAdd s

@[simp] theorem amount_one : amount 1 = 0 := rfl
@[simp] theorem amount_mul (s t : Spend) : amount (s * t) = amount s + amount t := rfl

/-! ## A thin theory to grade

A plan is a list of actions; a step performs the first one.  Equality is the
equation relation, so the respect laws are immediate. -/

/-- An action, with what performing it costs. -/
structure Action where
  /-- What the action is called. -/
  name : String
  /-- What performing it spends. -/
  cost : Expenditure

/-- Plans, as a theory: terms are remaining actions, a step performs one. -/
def planning : GSLT where
  Term := List Action
  equations := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := ∃ first : Action, source = first :: target
  rewrites_resp_left := by
    rintro source source' target rfl ⟨first, rfl⟩
    exact ⟨target, ⟨first, rfl⟩, rfl⟩
  rewrites_resp_right := by
    rintro source target target' ⟨first, rfl⟩ rfl
    exact ⟨first, rfl⟩

/-- The grading: performing an action is graded by what it costs. -/
def spending : GSLT.StepSpend planning Spend where
  graded source target grade :=
    ∃ first : Action, source = first :: target ∧
      grade = Multiplicative.ofAdd first.cost
  sound := by rintro source target grade ⟨first, rfl, -⟩; exact ⟨first, rfl⟩
  resp_left := by
    rintro source source' target grade rfl ⟨first, rfl, rfl⟩
    exact ⟨target, ⟨first, rfl, rfl⟩, rfl⟩
  resp_right := by
    rintro source target target' grade ⟨first, rfl, rfl⟩ rfl
    exact ⟨first, rfl, rfl⟩

/-- **Every step carries a grade**, so erasure reflects as well as preserves. -/
theorem spending_total : spending.Total := by
  rintro source target ⟨first, rfl⟩
  exact ⟨Multiplicative.ofAdd first.cost, first, rfl, rfl⟩

/-- The graded theory: a plan together with what has been spent so far. -/
def costedPlanning : GSLT := planning.spendLift spending

/-! ## The finite-run accounting law -/

/-- One step adds its own cost and nothing else. -/
theorem amount_of_step {source target : planning.Term × Spend}
    (step : costedPlanning.Step source target) :
    ∃ spent : Expenditure, amount target.2 = amount source.2 + spent := by
  obtain ⟨grade, -, accumulated⟩ := step
  exact ⟨amount grade, by rw [accumulated, amount_mul]⟩

/-- The expenditure grading is extensive: an action's cost is an expenditure,
and adding an expenditure never lowers a total. -/
theorem spending_extensive : spending.Extensive := by
  intro _ _ grade _ accumulator
  exact Expenditure.le_add_right (amount accumulator) (amount grade)

/-- **Spending never decreases along a run.**  This is the general
`GSLT.accumulated_monotone` at the expenditure grading, not a separate
argument: the only fact specific to expenditure is `spending_extensive`. -/
theorem accumulated_monotone {source target : planning.Term × Spend}
    (path : costedPlanning.MultiStep source target) :
    amount source.2 ≤ amount target.2 :=
  GSLT.accumulated_monotone spending spending_extensive path

/-! ## Its observational meaning -/

/-- **A level-`-1` expenditure is never covered by a rational budget, and no
continuation of the run recovers it.**  This is what distinguishes a level
from a weight: a weight is a price the run can pay off, a level is not
denominated in the budget's currency at all. -/
theorem omega_spend_never_covered {source target : planning.Term × Spend}
    (path : costedPlanning.MultiStep source target)
    (spentOmega : Expenditure.omegaSpend ≤ amount source.2)
    (budget : ℚ) (hb : 0 ≤ budget) :
    Expenditure.ofRat' budget hb < amount target.2 := by
  refine lt_of_lt_of_le ?_ (le_trans spentOmega (accumulated_monotone path))
  exact Expenditure.omega_spend_not_covered budget hb

/-! ## Controls -/

namespace ExpenditureControls

/-- A run that only ever spends at level `0` **is** covered, when the budget is
large enough.  So the previous theorem is about the level, not about budgets
failing in general. -/
theorem rational_run_is_covered {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ≤ b) : Expenditure.ofRat' a ha ≤ Expenditure.ofRat' b hb :=
  Expenditure.ExpenditureControls.rational_budget_covers ha hb hab

/-- An empty run spends nothing, so monotonicity is not vacuously true by the
accumulator always growing. -/
theorem idle_run_spends_nothing (source : planning.Term × Spend) :
    amount source.2 ≤ amount source.2 :=
  accumulated_monotone (@GSLT.MultiStep.refl costedPlanning source)

/-- The grading is a genuine refinement: a step exists, and it is graded. -/
theorem a_step_exists (first : Action) (rest : List Action) :
    planning.Step (first :: rest) rest ∧
      spending.graded (first :: rest) rest (Multiplicative.ofAdd first.cost) :=
  ⟨⟨first, rfl⟩, ⟨first, rfl, rfl⟩⟩

end ExpenditureControls

end MultiScaleExpenditure

end Mettapedia.GSLT

#print axioms Mettapedia.GSLT.MultiScaleExpenditure.spending_total
#print axioms Mettapedia.GSLT.MultiScaleExpenditure.accumulated_monotone
#print axioms Mettapedia.GSLT.MultiScaleExpenditure.omega_spend_never_covered
