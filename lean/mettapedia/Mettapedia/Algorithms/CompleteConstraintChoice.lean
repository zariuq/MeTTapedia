import Mettapedia.Algorithms.ConstrainedChoice
import Mathlib.Data.List.Sections

/-!
# Complete finite repair enumeration and admissible optimization

The existing constraint problem supplies finite variable domains and scoped
constraints. Cartesian sections enumerate canonical assignments, which the
existing checker filters. Every solution is represented with the same lookup
at every declared variable. Scores must depend on those lookups to obtain
optimality over all solutions, including differently ordered assignments.
-/

namespace Mettapedia.Algorithms.CompleteConstraintChoice

open Mettapedia.Algorithms.WellFoundedServices
open Mettapedia.Algorithms.ConstrainedChoice
open Mettapedia.Algorithms.CertifiedFiniteChoice

variable {V D : Type*} [DecidableEq V] [DecidableEq D]

def assignments (problem : Problem V D) : List (Assignment V D) :=
  (problem.vars.map (fun v => (problem.dom v).map (fun d => (v, d)))).sections

def solutions (problem : Problem V D) : List (Assignment V D) :=
  (assignments problem).filter (checkAssignment problem)

def canonical (vars : List V) (assignment : Assignment V D) : Assignment V D :=
  vars.filterMap (fun v => (assignment.lookup v).map (fun d => (v, d)))

def Agrees (problem : Problem V D) (first second : Assignment V D) : Prop :=
  ∀ v ∈ problem.vars, first.lookup v = second.lookup v

omit [DecidableEq D] in
theorem canonical_lookup (vars : List V) (assignment : Assignment V D)
    (v : V) (d : D) (member : v ∈ vars) (found : assignment.lookup v = some d) :
    (canonical vars assignment).lookup v = some d := by
  induction vars with
  | nil => simp at member
  | cons w rest ih =>
      by_cases same : v = w
      · subst w
        simp [canonical, found]
      · have tail : v ∈ rest := (List.mem_cons.mp member).resolve_left same
        cases head : assignment.lookup w with
        | none => simpa [canonical, head] using ih tail
        | some e =>
            simp only [canonical, List.filterMap_cons, head, Option.map_some]
            rw [lookup_cons_ne same]
            exact ih tail

omit [DecidableEq D] in
theorem canonical_mem_assignments (vars : List V) (domain : V → List D)
    (assignment : Assignment V D)
    (assigned : ∀ v ∈ vars, ∃ d ∈ domain v, assignment.lookup v = some d) :
    canonical vars assignment ∈
      (vars.map (fun v => (domain v).map (fun d => (v, d)))).sections := by
  induction vars with
  | nil => simp [canonical]
  | cons v rest ih =>
      obtain ⟨d, allowed, found⟩ := assigned v List.mem_cons_self
      have tail := ih (fun w hw => assigned w (List.mem_cons_of_mem _ hw))
      simp only [canonical, List.filterMap_cons, found, Option.map_some, List.map_cons]
      apply List.mem_sections.mpr
      exact List.Forall₂.cons (List.mem_map.mpr ⟨d, allowed, rfl⟩)
        (List.mem_sections.mp tail)

omit [DecidableEq D] in
theorem values_congr (vars : List V) (first second : Assignment V D)
    (same : ∀ v ∈ vars, first.lookup v = second.lookup v) :
    values first vars = values second vars := by
  induction vars with
  | nil => rfl
  | cons v rest ih =>
      simp only [values, same v List.mem_cons_self,
        ih (fun w hw => same w (List.mem_cons_of_mem _ hw))]

omit [DecidableEq D] in
theorem canonical_agrees (problem : Problem V D) (assignment : Assignment V D)
    (solution : problem.Solution assignment) :
    Agrees problem (canonical problem.vars assignment) assignment := by
  intro v member
  obtain ⟨d, _, found⟩ := solution.1 v member
  rw [canonical_lookup problem.vars assignment v d member found, found]

omit [DecidableEq D] in
theorem canonical_solution (problem : Problem V D) (wellFormed : problem.WellFormed)
    (assignment : Assignment V D) (solution : problem.Solution assignment) :
    problem.Solution (canonical problem.vars assignment) := by
  have agrees := canonical_agrees problem assignment solution
  constructor
  · intro v member
    obtain ⟨d, allowed, found⟩ := solution.1 v member
    exact ⟨d, allowed, (agrees v member).trans found⟩
  · intro constraint member
    obtain ⟨ds, found, allowed⟩ := solution.2 constraint member
    refine ⟨ds, ?_, allowed⟩
    rw [values_congr constraint.scope _ assignment
      (fun v hv => agrees v (wellFormed.scopes constraint member v hv))]
    exact found

/-- All returned assignments are solutions of the actual scoped constraints. -/
theorem solutions_sound (problem : Problem V D) (assignment : Assignment V D)
    (member : assignment ∈ solutions problem) : problem.Solution assignment :=
  (checkAssignment_iff problem assignment).mp (List.mem_filter.mp member).2

/-- Every solution has an enumerated representative agreeing on all declared variables. -/
theorem solutions_complete (problem : Problem V D) (wellFormed : problem.WellFormed)
    (assignment : Assignment V D) (solution : problem.Solution assignment) :
    ∃ representative ∈ solutions problem, Agrees problem representative assignment := by
  refine ⟨canonical problem.vars assignment, List.mem_filter.mpr ⟨?_, ?_⟩,
    canonical_agrees problem assignment solution⟩
  · exact canonical_mem_assignments problem.vars problem.dom assignment solution.1
  · exact (checkAssignment_iff problem _).mpr
      (canonical_solution problem wellFormed assignment solution)

def select (problem : Problem V D) (score : Assignment V D → ℚ) :
    Option (Assignment V D) := chooseBest score (solutions problem)

/-- The selected repair is optimal over every solution for consumers of the declared variables. -/
theorem select_correct (problem : Problem V D) (wellFormed : problem.WellFormed)
    (score : Assignment V D → ℚ)
    (supported : ∀ first second, Agrees problem first second → score first = score second)
    (selected : Assignment V D) (accepted : select problem score = some selected) :
    problem.Solution selected ∧
      ∀ alternative, problem.Solution alternative → score alternative ≤ score selected := by
  obtain ⟨member, maximal⟩ := chooseBest_correct score (solutions problem) selected accepted
  refine ⟨solutions_sound problem selected member, ?_⟩
  intro alternative admissible
  obtain ⟨representative, included, same⟩ :=
    solutions_complete problem wellFormed alternative admissible
  rw [← supported representative alternative same]
  exact maximal representative included

/-- Empty complete enumeration certifies impossibility; it is not budget exhaustion. -/
theorem select_none_iff (problem : Problem V D) (wellFormed : problem.WellFormed)
    (score : Assignment V D → ℚ) :
    select problem score = none ↔ ¬ ∃ assignment, problem.Solution assignment := by
  rw [select, chooseBest_eq_none_iff]
  constructor
  · intro empty ⟨assignment, admissible⟩
    obtain ⟨representative, included, _⟩ :=
      solutions_complete problem wellFormed assignment admissible
    simp [empty] at included
  · intro impossible
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro assignment member
    exact impossible ⟨assignment, solutions_sound problem assignment member⟩

end Mettapedia.Algorithms.CompleteConstraintChoice
