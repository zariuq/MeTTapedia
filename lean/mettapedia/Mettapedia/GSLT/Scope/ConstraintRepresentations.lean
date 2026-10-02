import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.Algorithms.CompleteConstraintChoice

/-!
# Constraint states in list and functional representations

Both operational theories assign an unassigned variable from its finite domain
and refuse any fully instantiated constraint that fails. List bindings retain
their order; partial functions retain only the first-binding interpretation.
The lookup map respects equations and covers every functional assignment step.
Solution consumers therefore transfer, while comparison counts need not.
-/

namespace Mettapedia.GSLT.Scope.ConstraintRepresentations

open Mettapedia.Algorithms.WellFoundedServices
open Mettapedia.GSLT.IndexedOperational

universe u
variable {V D : Type u} [DecidableEq V]

abbrev Partial (V D : Type u) := V → Option D

def read (assignment : Assignment V D) : Partial V D := fun v => List.lookup v assignment

def functionalValues (assignment : Partial V D) : List V → Option (List D)
  | [] => some []
  | v :: rest =>
      match assignment v, functionalValues assignment rest with
      | some d, some ds => some (d :: ds)
      | _, _ => none

theorem values_read (assignment : Assignment V D) (scope : List V) :
    functionalValues (read assignment) scope = values assignment scope := by
  induction scope with
  | nil => rfl
  | cons v rest ih => rw [functionalValues, values, ih]; rfl

def put (assignment : Partial V D) (v : V) (d : D) : Partial V D :=
  fun w => if w = v then some d else assignment w

theorem read_cons (assignment : Assignment V D) (v : V) (d : D) :
    read ((v, d) :: assignment) = put (read assignment) v d := by
  funext w
  by_cases same : w = v
  · subst w
    simp [read, put]
  · simpa only [read, put, if_neg same] using lookup_cons_ne (a := assignment) (d := d) same

def functionalViolated (constraint : Constraint V D) (assignment : Partial V D) : Bool :=
  match functionalValues assignment constraint.scope with
  | some ds => !constraint.allows ds
  | none => false

def validPartial (problem : Problem V D) (assignment : Partial V D) : Prop :=
  ∀ constraint ∈ problem.constraints, functionalViolated constraint assignment = false

def listValidPartial (problem : Problem V D) (assignment : Assignment V D) : Prop :=
  ∀ constraint ∈ problem.constraints, constraint.violatedBy assignment = false

theorem valid_read (problem : Problem V D) (assignment : Assignment V D) :
    validPartial problem (read assignment) ↔ listValidPartial problem assignment := by
  simp only [validPartial, listValidPartial, functionalViolated, Constraint.violatedBy,
    values_read]
  rfl

def functionalStep (problem : Problem V D) (first second : Partial V D) : Prop :=
  ∃ v ∈ problem.vars, ∃ d ∈ problem.dom v,
    first v = none ∧ second = put first v d ∧ validPartial problem second

def listStep (problem : Problem V D) (first second : Assignment V D) : Prop :=
  ∃ v ∈ problem.vars, ∃ d ∈ problem.dom v,
    first.lookup v = none ∧
    read second = read ((v, d) :: first) ∧ listValidPartial problem second

theorem step_read (problem : Problem V D) {first second : Assignment V D}
    (step : listStep problem first second) :
    functionalStep problem (read first) (read second) := by
  obtain ⟨v, member, d, allowed, missing, same, valid⟩ := step
  exact ⟨v, member, d, allowed, missing, same.trans (read_cons first v d),
    (valid_read problem second).mpr valid⟩

/-- Every target step is implemented by the actual list insertion operation. -/
theorem lift_step (problem : Problem V D) (first : Assignment V D)
    (second : Partial V D) (step : functionalStep problem (read first) second) :
    ∃ next, listStep problem first next ∧ read next = second := by
  obtain ⟨v, member, d, allowed, missing, same, valid⟩ := step
  have result : read ((v, d) :: first) = second := (read_cons first v d).trans same.symm
  refine ⟨(v, d) :: first, ⟨v, member, d, allowed, missing, rfl, ?_⟩, result⟩
  apply (valid_read problem _).mp
  rwa [result]

def bindingSetoid : Setoid (Assignment V D) where
  r first second := read first = read second
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

def listTheory (problem : Problem V D) : GSLT where
  Term := Assignment V D
  equations := bindingSetoid
  rewrites := listStep problem
  rewrites_resp_left := by
    intro first other second equivalent step
    change read first = read other at equivalent
    obtain ⟨v, member, d, allowed, missing, same, valid⟩ := step
    refine ⟨second, ⟨v, member, d, allowed, ?_, ?_, valid⟩, rfl⟩
    · change read other v = none
      rw [← equivalent]
      exact missing
    · rw [read_cons] at same ⊢
      rwa [← equivalent]
  rewrites_resp_right := by
    intro first second other step equivalent
    change read second = read other at equivalent
    obtain ⟨v, member, d, allowed, missing, same, valid⟩ := step
    refine ⟨v, member, d, allowed, missing, equivalent.symm.trans same, ?_⟩
    apply (valid_read problem other).mp
    rw [← equivalent]
    exact (valid_read problem second).mpr valid

def functionalTheory (problem : Problem V D) : GSLT where
  Term := Partial V D
  equations := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  rewrites := functionalStep problem
  rewrites_resp_left := by
    intro first other second equivalent step
    subst other
    exact ⟨second, step, rfl⟩
  rewrites_resp_right := by
    intro first second other step equivalent
    subst other
    exact step

/-- Equational and operational translation, including local target-step coverage. -/
def lookupTranslation (problem : Problem V D) :
    CoveredTranslation (listTheory problem) (functionalTheory problem) where
  mapTerm := read
  mapEquiv := fun equivalent => equivalent
  cover := ⟨fun step => step_read problem step, fun step => lift_step problem _ _ step⟩

def functionalSolution (problem : Problem V D) (assignment : Partial V D) : Prop :=
  (∀ v ∈ problem.vars, ∃ d ∈ problem.dom v, assignment v = some d) ∧
    ∀ constraint ∈ problem.constraints,
      ∃ ds, functionalValues assignment constraint.scope = some ds ∧
        constraint.allows ds = true

/-- The independently stated functional constraints agree with the list service. -/
theorem solution_read (problem : Problem V D) (assignment : Assignment V D) :
    functionalSolution problem (read assignment) ↔ problem.Solution assignment := by
  simp only [functionalSolution, Problem.Solution, Constraint.Satisfies, values_read, read]

/-- Complete list enumeration covers the functional interpretation of every list solution. -/
theorem enumeration_covers (problem : Problem V D) [DecidableEq D]
    (wellFormed : problem.WellFormed) (assignment : Assignment V D)
    (solution : functionalSolution problem (read assignment)) :
    ∃ representative ∈ Mettapedia.Algorithms.CompleteConstraintChoice.solutions problem,
      ∀ v ∈ problem.vars, read representative v = read assignment v := by
  simpa only [Mettapedia.Algorithms.CompleteConstraintChoice.Agrees, read] using
    Mettapedia.Algorithms.CompleteConstraintChoice.solutions_complete problem wellFormed
      assignment ((solution_read problem assignment).mp solution)

def materialize (vars : List V) (assignment : Partial V D) : Assignment V D :=
  vars.filterMap (fun v => (assignment v).map (fun d => (v, d)))

theorem materialize_lookup (vars : List V) (assignment : Partial V D)
    (v : V) (d : D) (member : v ∈ vars) (found : assignment v = some d) :
    read (materialize vars assignment) v = some d := by
  induction vars with
  | nil => simp at member
  | cons w rest ih =>
      by_cases same : v = w
      · subst w
        simp [materialize, read, found]
      · have tail : v ∈ rest := (List.mem_cons.mp member).resolve_left same
        cases head : assignment w with
        | none => simpa [materialize, head] using ih tail
        | some e =>
            simp only [materialize, List.filterMap_cons, head, Option.map_some, read]
            rw [lookup_cons_ne same]
            exact ih tail

omit [DecidableEq V] in
theorem functionalValues_congr (scope : List V) (first second : Partial V D)
    (same : ∀ v ∈ scope, first v = second v) :
    functionalValues first scope = functionalValues second scope := by
  induction scope with
  | nil => rfl
  | cons v rest ih =>
      simp only [functionalValues, same v List.mem_cons_self,
        ih (fun w member => same w (List.mem_cons_of_mem _ member))]

/-- Every functional solution has a checked enumerated list representative on its declared scope. -/
theorem functional_solutions_covered (problem : Problem V D) [DecidableEq D]
    (wellFormed : problem.WellFormed) (assignment : Partial V D)
    (solution : functionalSolution problem assignment) :
    ∃ representative ∈ Mettapedia.Algorithms.CompleteConstraintChoice.solutions problem,
      ∀ v ∈ problem.vars, read representative v = assignment v := by
  let concrete := materialize problem.vars assignment
  have same : ∀ v ∈ problem.vars, read concrete v = assignment v := by
    intro v member
    obtain ⟨d, _, found⟩ := solution.1 v member
    exact (materialize_lookup problem.vars assignment v d member found).trans found.symm
  have concreteSolution : problem.Solution concrete := by
    constructor
    · intro v member
      obtain ⟨d, allowed, found⟩ := solution.1 v member
      exact ⟨d, allowed, (same v member).trans found⟩
    · intro constraint member
      obtain ⟨ds, found, allowed⟩ := solution.2 constraint member
      refine ⟨ds, ?_, allowed⟩
      rw [← values_read]
      rw [functionalValues_congr constraint.scope (read concrete) assignment
        (fun v hv => same v (wellFormed.scopes constraint member v hv))]
      exact found
  obtain ⟨representative, included, agrees⟩ :=
    Mettapedia.Algorithms.CompleteConstraintChoice.solutions_complete problem wellFormed
      concrete concreteSolution
  exact ⟨representative, included, fun v member => (agrees v member).trans (same v member)⟩

/-- Later covered representation changes compose with this actual assignment translation. -/
theorem composed_step (problem : Problem V D) (target : GSLT.{u})
    (later : CoveredTranslation (functionalTheory problem) target)
    {first second : Assignment V D} (step : (listTheory problem).Step first second) :
    target.Step (later.mapTerm (read first)) (later.mapTerm (read second)) :=
  ((lookupTranslation problem).comp later).cover.mapStep step

/-- Number of list bindings inspected by short-circuit lookup. -/
def lookupComparisons (query : V) : Assignment V D → ℕ
  | [] => 0
  | (v, _) :: rest => if query = v then 1 else 1 + lookupComparisons query rest

def twoBitProblem : Problem Bool Bool where
  vars := [false, true]
  dom _ := [false, true]
  constraints := [⟨[false, true], fun ds => decide (ds ≠ [false, false])⟩]

theorem distinct_binding_orders_agree :
    read [(false, false), (true, true)] = read [(true, true), (false, false)] := by
  funext query
  cases query <;> decide +kernel

theorem binding_orders_have_different_cost :
    lookupComparisons false [(false, false), (true, true)] ≠
      lookupComparisons false [(true, true), (false, false)] := by decide +kernel

/-- Cost does not descend through the answer-preserving representation map. -/
theorem cost_does_not_factor :
    ¬ ∃ cost : Partial Bool Bool → ℕ, ∀ assignment,
      cost (read assignment) = lookupComparisons false assignment := by
  rintro ⟨cost, factors⟩
  have same := congrArg cost distinct_binding_orders_agree
  rw [factors, factors] at same
  exact binding_orders_have_different_cost same

theorem nontrivial_assignment_step :
    listStep twoBitProblem [] [(false, true)] := by
  refine ⟨false, by decide +kernel, true, by decide +kernel, rfl, rfl, ?_⟩
  intro constraint member
  simp only [twoBitProblem, List.mem_singleton] at member
  subst constraint
  decide +kernel

theorem existing_binding_cannot_be_overwritten :
    ¬ functionalStep twoBitProblem (read [(false, true), (true, true)])
      (read [(false, false), (true, true)]) := by
  rintro ⟨v, _, _, _, missing, _⟩
  cases v <;> simp [read] at missing

theorem three_complete_repairs :
    (Mettapedia.Algorithms.CompleteConstraintChoice.solutions twoBitProblem).length = 3 := by
  decide +kernel

end Mettapedia.GSLT.Scope.ConstraintRepresentations
