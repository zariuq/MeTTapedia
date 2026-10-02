import Mettapedia.Algorithms.WellFoundedServices.ConstraintPlanning
import Mettapedia.Algorithms.CertifiedFiniteChoice

/-!
# Checked finite choice over constraint-planning assignments

Candidate assignments are ordinary data. Domain and constraint checks use the
existing well-founded planning interface. Scores rank only candidates that
pass those checks. Selection proves admissibility and optimality over that
validated candidate family; it does not pretend an incomplete family covers
all solutions of the problem.
-/

namespace Mettapedia.Algorithms.ConstrainedChoice

open Mettapedia.Algorithms.WellFoundedServices
open Mettapedia.Algorithms.CertifiedFiniteChoice

variable {V D : Type*} [DecidableEq V] [DecidableEq D]

def checkAssignment (problem : Problem V D) (candidate : Assignment V D) : Bool :=
  problem.vars.all (fun v => match candidate.lookup v with
    | some d => problem.dom v |>.contains d
    | none => false) &&
  problem.constraints.all (fun c => match values candidate c.scope with
    | some ds => c.allows ds
    | none => false)

theorem checkAssignment_iff (problem : Problem V D) (candidate : Assignment V D) :
    checkAssignment problem candidate = true ↔ problem.Solution candidate := by
  simp only [checkAssignment, Bool.and_eq_true, List.all_eq_true, Problem.Solution]
  constructor
  · rintro ⟨domains, constraints⟩
    constructor
    · intro v member
      have found := domains v member
      cases value : candidate.lookup v with
      | none => simp [value] at found
      | some d =>
          exact ⟨d, by simpa [value] using found, rfl⟩
    · intro c member
      have checked := constraints c member
      cases found : values candidate c.scope with
      | none => simp [found] at checked
      | some ds => exact ⟨ds, found, by simpa [found] using checked⟩
  · rintro ⟨domains, constraints⟩
    constructor
    · intro v member
      obtain ⟨d, allowed, found⟩ := domains v member
      simp [found, allowed]
    · intro c member
      obtain ⟨ds, found, allowed⟩ := constraints c member
      simp [found, allowed]

def select (problem : Problem V D) (score : Assignment V D → ℚ)
    (candidates : List (Assignment V D)) : Option (Assignment V D) :=
  chooseBest score (candidates.filter (checkAssignment problem))

/-- Preferences rank admissible plans without expanding the admissible family. -/
theorem select_correct (problem : Problem V D) (score : Assignment V D → ℚ)
    (candidates : List (Assignment V D)) (selected : Assignment V D)
    (accepted : select problem score candidates = some selected) :
    selected ∈ candidates ∧ problem.Solution selected ∧
      ∀ other ∈ candidates, problem.Solution other → score other ≤ score selected := by
  obtain ⟨member, best⟩ := chooseBest_correct score _ selected accepted
  have included := List.mem_filter.mp member
  refine ⟨included.1, (checkAssignment_iff problem selected).mp included.2, ?_⟩
  intro other in_family admissible
  exact best other (List.mem_filter.mpr
    ⟨in_family, (checkAssignment_iff problem other).mpr admissible⟩)

end Mettapedia.Algorithms.ConstrainedChoice
