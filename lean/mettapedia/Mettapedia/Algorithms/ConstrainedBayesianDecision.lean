import Mettapedia.Algorithms.FiniteBayesianDecision
import Mettapedia.Algorithms.CompleteConstraintChoice

/-!
# Bayesian decisions over the complete repair space

The constraint service constructs the candidate list and checks admissibility.
The decision checker supplies the statistical and execution certificates. A
world controller that depends only on the declared assignment observations
extends the checked regret guarantee from enumerated representatives to every
solution, regardless of its binding order or extra unobserved bindings.
-/

namespace Mettapedia.Algorithms.ConstrainedBayesianDecision

open WellFoundedServices
open CompleteConstraintChoice
open FiniteBayesianDecision

variable {V D S T O U A B : Type*}
  [DecidableEq V] [DecidableEq D]
  [Fintype S] [Fintype T] [Fintype O] [Fintype U] [Fintype A] [Fintype B]
  {n : ℕ}

/-- Admissibility and coverage are computed from the actual scoped constraints. -/
def prepared (problem : Problem V D) (data : Instance S T O U A B (Assignment V D) n) :
    Instance S T O U A B (Assignment V D) n :=
  { data with candidates := solutions problem, admissible := ConstrainedChoice.checkAssignment problem }

def check (problem : Problem V D) (data : Instance S T O U A B (Assignment V D) n) : Bool :=
  (prepared problem data).check

/-- Accepted repairs satisfy the independently supplied constraint problem. -/
theorem selected_solution (problem : Problem V D)
    (data : Instance S T O U A B (Assignment V D) n)
    (accepted : check problem data = true) : problem.Solution data.selected := by
  have member := (prepared problem data).accepted_conditions accepted |>.2.2.2.2.2.1
  exact solutions_sound problem data.selected member

/-- The world-regret bound ranges over all solutions, not just a caller's proposed repairs. -/
theorem regret_all_solutions (problem : Problem V D) (wellFormed : problem.WellFormed)
    (data : Instance S T O U A B (Assignment V D) n)
    (supported : ∀ first second, Agrees problem first second →
      data.worldPolicy first = data.worldPolicy second)
    (accepted : check problem data = true)
    (alternative : Assignment V D) (solution : problem.Solution alternative) :
    problem.Solution data.selected ∧
      (data.worldScore alternative : ℝ) - (data.worldScore data.selected : ℝ) ≤
        2 * (data.uniformError : ℝ) + (data.slack : ℝ) := by
  obtain ⟨representative, member, same⟩ :=
    solutions_complete problem wellFormed alternative solution
  have bound := ((prepared problem data).regret accepted representative member).2
  have values : data.worldScore representative = data.worldScore alternative := by
    unfold Instance.worldScore
    rw [supported representative alternative same]
  refine ⟨selected_solution problem data accepted, ?_⟩
  change (data.worldScore representative : ℝ) - (data.worldScore data.selected : ℝ) ≤
    2 * (data.uniformError : ℝ) + (data.slack : ℝ) at bound
  rwa [values] at bound

end Mettapedia.Algorithms.ConstrainedBayesianDecision
