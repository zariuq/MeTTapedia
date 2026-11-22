import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.RankRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughPhases

/-!
# The tree's in-place solver, audited: level variables, cumulativity, and runs with no budget of rounds

The in-place solver (`ContextualDependentInPlace`) is a solver of the tree's driver: every progress is an update
(sound and complete for `frames S.levels`), every refutation carries the absence of solutions, and its rank is the
telescope's length, then the number of equations. Two facts its uses need are proved here.

* **Level variables are parameters, not unknowns** (`models_valuation_free`, `solvable_valuation_free`,
  `principal_valuation_free`, `initial_valuation_free`). In the tower, the frame's solutions, principal answers and
  initial solutions are the same at the settings of every two valuations of the level variables: the frame reads typed
  equality of the rules, whose universe comparison is an entailment over all valuations, and never the setting's level
  model. So a decision proved at the controls' valuation is a decision for the level variables universally quantified.
* **The base of the phases needs no budget of rounds** (`Decided.ofRank`): a decision read off the run driven by the
  solver's rank. Wherever a run with some budget decides, it decides the same (`Decided.ofRank_eq_ofRun`), and it
  decides exactly where some budget does (`Decided.ofRank_isSome_iff`). For the in-place solver this holds over every
  telescope, since its rank counts declarations and equations, not occurrence weights.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

/-! ## Level variables are parameters -/

section Valuations

variable (ν ν' : Nat → Nat)

/-- The tower's rules do not depend on the valuation of the level variables. -/
theorem rules_valuation_free : (TowerModel.setting ν).R = (TowerModel.setting ν').R := rfl

/-- Neither do its roles. -/
theorem roles_valuation_free : (TowerModel.setting ν).roles = (TowerModel.setting ν').roles := rfl

/-- **A substitution solves a store at one valuation exactly when it does at every other.** -/
theorem models_valuation_free {Γ Δ : Context (LevelTower.rules Nat)} (σ : Δ ⟶ Γ)
    (problem : EquationStore (TotalTerm Γ)) :
    (frames (TowerModel.setting ν).levels).Models σ problem ↔
      (frames (TowerModel.setting ν').levels).Models σ problem := Iff.rfl

/-- **Solvability does not depend on the valuation.** -/
theorem solvable_valuation_free {Γ : Context (LevelTower.rules Nat)} (problem : EquationStore (TotalTerm Γ)) :
    (frames (TowerModel.setting ν).levels).Solvable problem ↔
      (frames (TowerModel.setting ν').levels).Solvable problem := Iff.rfl

/-- **Principal answers do not depend on the valuation.** -/
theorem principal_valuation_free {Γ Δ : Context (LevelTower.rules Nat)} (problem : EquationStore (TotalTerm Γ))
    (σ : Δ ⟶ Γ) :
    (frames (TowerModel.setting ν).levels).Principal problem σ ↔
      (frames (TowerModel.setting ν').levels).Principal problem σ := Iff.rfl

/-- **Initial solutions do not depend on the valuation.** -/
theorem initial_valuation_free {Γ Δ : Context (LevelTower.rules Nat)} (problem : EquationStore (TotalTerm Γ))
    (σ : Δ ⟶ Γ) :
    InitialSolution (frames (TowerModel.setting ν).levels) problem σ ↔
      InitialSolution (frames (TowerModel.setting ν').levels) problem σ := Iff.rfl

end Valuations

/-! ## Decisions with no budget of rounds -/

section Decisions

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **A decision read off the run driven by the solver's rank**: a finished update or a refutation, with no budget of
rounds. -/
def Decided.ofRank (solver : ContextualDependentWorklist.Solver S.levels) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) : Option (Decided problem) :=
  match runRank solver problem with
  | .solved state finished => some (.solved state finished)
  | .refuted absent => some (.refuted absent)
  | _ => none

/-- A run with a budget that decides is finished. -/
theorem finished_of_ofRun {solver : ContextualDependentWorklist.Solver S.levels} {fuel : Nat} {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (found : (Decided.ofRun solver fuel problem).isSome = true) :
    (run solver problem fuel).Finished := by
  unfold Decided.ofRun at found
  cases h : run solver problem fuel with
  | solved state finished => trivial
  | refuted absent => trivial
  | stuck state => trivial
  | cutoff state =>
      rw [h] at found
      cases found

/-- **Wherever a run with some budget decides, the run driven by the rank decides the same.** -/
theorem Decided.ofRank_eq_ofRun {solver : ContextualDependentWorklist.Solver S.levels} {fuel : Nat}
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (found : (Decided.ofRun solver fuel problem).isSome = true) :
    Decided.ofRank solver problem = Decided.ofRun solver fuel problem := by
  unfold Decided.ofRank Decided.ofRun
  rw [← run_eq_runRank solver (finished_of_ofRun found)]
  cases run solver problem fuel <;> rfl

/-- **The run driven by the rank decides exactly where some budget decides.** -/
theorem Decided.ofRank_isSome_iff (solver : ContextualDependentWorklist.Solver S.levels) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) :
    (Decided.ofRank solver problem).isSome = true ↔ ∃ fuel, (Decided.ofRun solver fuel problem).isSome = true := by
  constructor
  · intro found
    obtain ⟨bound, same⟩ := runRank_eventually solver problem
    refine ⟨bound, ?_⟩
    unfold Decided.ofRun
    rw [same bound le_rfl]
    exact found
  · rintro ⟨fuel, found⟩
    rw [Decided.ofRank_eq_ofRun found]
    exact found

end Decisions

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
