import Mettapedia.Logic.BDD.FixedPointSolver
import Mettapedia.Logic.CTLFixedPoints

/-!
# Symbolic existential CTL over admitted state transducers

The BDD operators implement the independent relational predecessor and CTL
path meanings. Until uses the least fixed point; globally uses the greatest.
The state domain is explicit, and a typed source program proves that enabled
transitions stay within it. Fixed-point pages preserve the solver's own pass
count and residual, not arbitrary source evaluation schedules or counts.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.SymbolicCTL

open StatePredicates StateTransducer FixedPointSolver
open Mettapedia.Logic.CTLFixedPoints (Until Globally)

theorem pre_denote {n : Nat} (domain : Diagram n) (rules : List (Rule n)) (target : Diagram n) :
    denote (StateTransducer.pre domain rules target) =
      CTLFixedPoints.pre (Relation domain rules) (denote target) := by
  ext state
  exact pre_eval domain rules target state

def untilOp {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (holds goal : Diagram n) : Operator n where
  step current := disj (within domain goal)
    (conj (within domain holds) (StateTransducer.pre domain program.rules current))
  meaning := CTLFixedPoints.untilOperator (Relation domain program.rules)
    (denote (within domain holds)) (denote (within domain goal))
  refines current := by
    ext state
    change _ ↔ state ∈ denote (within domain goal) ∪
      (denote (within domain holds) ∩ CTLFixedPoints.pre (Relation domain program.rules) (denote current))
    simp only [denote, BDD.satSet, Set.mem_ofPred_eq, disj, conj, apply_eval, Bool.or_eq_true,
      Bool.and_eq_true_iff, Set.mem_union, Set.mem_inter_iff]
    rw [pre_eval]
    rfl

def globallyOp {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (holds : Diagram n) : Operator n where
  step current := conj (within domain holds) (StateTransducer.pre domain program.rules current)
  meaning := CTLFixedPoints.globallyOperator (Relation domain program.rules) (denote (within domain holds))
  refines current := by
    ext state
    change _ ↔ state ∈ denote (within domain holds) ∩
      CTLFixedPoints.pre (Relation domain program.rules) (denote current)
    simp only [denote, BDD.satSet, Set.mem_ofPred_eq, conj, apply_eval,
      Bool.and_eq_true_iff, Set.mem_inter_iff]
    rw [pre_eval]
    rfl

def untilRun {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (holds goal : Diagram n) (fuel : Nat) : Result n :=
  advance (untilOp program holds goal) fuel ⟨falsity n, 0⟩

def globallyRun {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (holds : Diagram n) (fuel : Nat) : Result n :=
  advance (globallyOp program holds) fuel ⟨truth n, 0⟩

theorem until_complete_iff_path {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (holds goal : Diagram n) (fuel : Nat) (final : Frame n)
    (completed : untilRun program holds goal fuel = .done final) (state : State n) :
    final.current.val.eval state = true ↔ Until (Relation domain program.rules)
      (denote (within domain holds)) (denote (within domain goal)) state := by
  have correct := completed_least (untilOp program holds goal) fuel final completed
  change state ∈ denote final.current ↔ _
  rw [correct]
  exact (CTLFixedPoints.until_iff_lfp _ _ _ state).symm

theorem globally_complete_iff_path {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (holds : Diagram n) (fuel : Nat) (final : Frame n)
    (completed : globallyRun program holds fuel = .done final) (state : State n) :
    final.current.val.eval state = true ↔ Globally (Relation domain program.rules)
      (denote (within domain holds)) state := by
  have correct := completed_greatest (globallyOp program holds) fuel final completed
  change state ∈ denote final.current ↔ _
  rw [correct]
  exact (CTLFixedPoints.globally_iff_gfp _ _ state).symm

theorem until_eventually_finishes {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (holds goal : Diagram n) : ∃ fuel, (untilRun program holds goal fuel).finished = true :=
  least_eventually_finishes (untilOp program holds goal)

theorem globally_eventually_finishes {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (holds : Diagram n) : ∃ fuel, (globallyRun program holds fuel).finished = true :=
  greatest_eventually_finishes (globallyOp program holds)

/-- A positive until approximation is already sound before completion. Its
missing states are not yet certified negative answers. -/
theorem partial_until_sound {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (holds goal : Diagram n) (fuel : Nat) (state : State n)
    (present : (untilRun program holds goal fuel).frame.current.val.eval state = true) :
    Until (Relation domain program.rules) (denote (within domain holds)) (denote (within domain goal)) state :=
  (CTLFixedPoints.until_iff_lfp _ _ _ state).mpr (bottom_result_below (untilOp program holds goal) fuel present)

/-- A state removed by a greatest-fixed-point approximation is already
refuted. A retained state may still be removed by later passes. -/
theorem partial_globally_exclusion {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (holds : Diagram n) (fuel : Nat) (state : State n)
    (absent : (globallyRun program holds fuel).frame.current.val.eval state = false) :
    ¬ Globally (Relation domain program.rules) (denote (within domain holds)) state := by
  intro path
  have member := top_result_above (globallyOp program holds) fuel
    ((CTLFixedPoints.globally_iff_gfp _ _ state).mp path)
  change (globallyRun program holds fuel).frame.current.val.eval state = true at member
  rw [absent] at member
  cases member

/-- `none` means unresolved at this page, not a false temporal proposition. -/
def observeUntil {n : Nat} (result : Result n) (state : State n) : Option Bool :=
  if result.frame.current.val.eval state then some true
  else if result.finished then some false else none

def observeGlobally {n : Nat} (result : Result n) (state : State n) : Option Bool :=
  if result.frame.current.val.eval state then
    if result.finished then some true else none
  else some false

theorem observeUntil_true {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (holds goal : Diagram n) (fuel : Nat) (state : State n)
    (answer : observeUntil (untilRun program holds goal fuel) state = some true) :
    Until (Relation domain program.rules) (denote (within domain holds)) (denote (within domain goal)) state := by
  apply partial_until_sound program holds goal fuel state
  cases value : (untilRun program holds goal fuel).frame.current.val.eval state
  · simp [observeUntil, value] at answer
  · rfl

theorem observeUntil_false {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (holds goal : Diagram n) (fuel : Nat) (state : State n)
    (answer : observeUntil (untilRun program holds goal fuel) state = some false) :
    ¬ Until (Relation domain program.rules) (denote (within domain holds)) (denote (within domain goal)) state := by
  cases run : untilRun program holds goal fuel with
  | paused frame => cases value : frame.current.val.eval state <;> simp [observeUntil, run, value, Result.frame, Result.finished] at answer
  | done frame =>
    have value : frame.current.val.eval state = false := by
      cases value : frame.current.val.eval state <;> simp_all [observeUntil, Result.frame, Result.finished]
    intro path
    have held := (until_complete_iff_path program holds goal fuel frame run state).mpr path
    simp [value] at held

theorem observeGlobally_false {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (holds : Diagram n) (fuel : Nat) (state : State n)
    (answer : observeGlobally (globallyRun program holds fuel) state = some false) :
    ¬ Globally (Relation domain program.rules) (denote (within domain holds)) state := by
  apply partial_globally_exclusion program holds fuel state
  cases value : (globallyRun program holds fuel).frame.current.val.eval state
  · rfl
  · simp [observeGlobally, value] at answer

theorem observeGlobally_true {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (holds : Diagram n) (fuel : Nat) (state : State n)
    (answer : observeGlobally (globallyRun program holds fuel) state = some true) :
    Globally (Relation domain program.rules) (denote (within domain holds)) state := by
  cases run : globallyRun program holds fuel with
  | paused frame => cases value : frame.current.val.eval state <;> simp [observeGlobally, run, value, Result.frame, Result.finished] at answer
  | done frame =>
    have value : frame.current.val.eval state = true := by
      cases value : frame.current.val.eval state <;> simp_all [observeGlobally, Result.frame, Result.finished]
    exact (globally_complete_iff_path program holds fuel frame run state).mp value

end Mettapedia.Logic.BDDCore.SymbolicCTL
