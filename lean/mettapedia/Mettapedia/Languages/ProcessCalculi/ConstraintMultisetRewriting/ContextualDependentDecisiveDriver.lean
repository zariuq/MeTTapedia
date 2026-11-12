import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWorklist

/-!
# Decisiveness at one joint budget for a fuel-indexed solver

The executable rounds of the dependent solver take a budget for their own
normalizer, type former and conversion test. A **fuel-indexed solver family**
has one rank and one round at every budget. On a class of stores the family
**settles** when, at every nonempty store of the class, its round is eventually
the same at every larger budget, that eventual round is not stuck, and when it
progresses it stays in the class.

On a class where the family settles, the driver decides every store at one
joint budget, used both for the rounds and for the executable budget: it reaches
a principal answer or a certified refutation, and the outcome is the same at every
larger joint budget. This is a conditional decision: it holds on the classes where
a family settles. No family settles on a class holding a solvable store without a
principal answer, such as `crossStore` in the dynamic pattern fragment of the
cumulative tower (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`).
The state of a run is exact for every store
(`UnificationWithLevels.DependentFibre.outcome_exact`), and on `crossStore` every
state keeps a nonempty exact residual: the run stops postponed
(`UnificationWithLevels.DependentFibre.cross_driver_states`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDecisiveDriver

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

/-- **A fuel-indexed solver family**: one rank, and a round at every budget. -/
structure Family where
  rank : {Γ : Context rules} → EquationStore (TotalTerm Γ) → Nat × Nat
  round : Nat → {Γ : Context rules} → (problem : EquationStore (TotalTerm Γ)) → Round levels rank problem

variable {levels}

/-- The solver of a family at one budget. -/
def Family.solver (family : Family levels) (fuel : Nat) : Solver levels where
  rank := family.rank
  round := family.round fuel

/-- **A class on which a family decides**: at each nonempty store of it the round eventually settles
on one round that is not stuck, and when that round progresses it stays in the class. -/
structure Settled (family : Family levels) where
  holds : {Γ : Context rules} → EquationStore (TotalTerm Γ) → Prop
  settles : ∀ {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
    ∃ threshold, family.round threshold problem ≠ .stuck ∧
      (∀ fuel, threshold ≤ fuel → family.round fuel problem = family.round threshold problem) ∧
      ∀ {update : Update levels problem} {smaller : Below (family.rank update.remaining) (family.rank problem)},
        family.round threshold problem = .progress update smaller → holds update.remaining

namespace Settled

variable {family : Family levels} (settled : Settled family)
variable {Γ : Context rules} {original : EquationStore (TotalTerm Γ)}

omit settled in
theorem advance_empty (fuel : Nat) {state : Update levels original} (empty : state.remaining = []) :
    advance (family.solver fuel) state = .done (.solved state empty) := by
  unfold advance
  split
  · rfl
  · rename_i first rest nonempty
    rw [empty] at nonempty
    cases nonempty

omit settled in
theorem advance_progress (fuel : Nat) {state : Update levels original} (nonempty : state.remaining ≠ [])
    {update : Update levels state.remaining}
    {smaller : Below (family.rank update.remaining) (family.rank state.remaining)}
    (computed : family.round fuel state.remaining = .progress update smaller) :
    advance (family.solver fuel) state = .next (state.then update) := by
  unfold advance
  split
  · rename_i empty
    exact absurd empty nonempty
  · simp only [Family.solver]
    rw [computed]

omit settled in
theorem advance_refuted (fuel : Nat) {state : Update levels original} (nonempty : state.remaining ≠ [])
    {absent : ¬ (frames levels).Solvable state.remaining}
    (computed : family.round fuel state.remaining = .refuted absent) :
    advance (family.solver fuel) state = .done (.refuted fun solvable => absent (state.solvable_iff.mp solvable)) := by
  unfold advance
  split
  · rename_i empty
    exact absurd empty nonempty
  · simp only [Family.solver]
    rw [computed]

/-- From every state in the class, one joint threshold of budget and rounds decides the original
store, with the same outcome at every larger budget and every larger number of rounds. -/
theorem eventually (state : Update levels original) (inside : settled.holds state.remaining) :
    ∃ fuel₀ rounds₀, ∀ fuel, fuel₀ ≤ fuel → ∀ rounds, rounds₀ ≤ rounds →
      drive (family.solver fuel) rounds state = drive (family.solver fuel₀) rounds₀ state ∧
      (drive (family.solver fuel₀) rounds₀ state).Decided := by
  suffices key : ∀ rank (state : Update levels original), family.rank state.remaining = rank →
      settled.holds state.remaining →
      ∃ fuel₀ rounds₀, ∀ fuel, fuel₀ ≤ fuel → ∀ rounds, rounds₀ ≤ rounds →
        drive (family.solver fuel) rounds state = drive (family.solver fuel₀) rounds₀ state ∧
        (drive (family.solver fuel₀) rounds₀ state).Decided from key _ state rfl inside
  intro rank
  refine below_wf.induction (C := fun rank => ∀ state : Update levels original,
    family.rank state.remaining = rank → settled.holds state.remaining →
    ∃ fuel₀ rounds₀, ∀ fuel, fuel₀ ≤ fuel → ∀ rounds, rounds₀ ≤ rounds →
      drive (family.solver fuel) rounds state = drive (family.solver fuel₀) rounds₀ state ∧
      (drive (family.solver fuel₀) rounds₀ state).Decided) rank ?_
  intro rank ih state ranked inside
  by_cases empty : state.remaining = []
  · have finished : ∀ fuel rounds, drive (family.solver fuel) (rounds + 1) state = .solved state empty := by
      intro fuel rounds
      rw [drive_succ, advance_empty fuel empty]
    refine ⟨0, 1, fun fuel _ rounds enough => ?_⟩
    obtain ⟨rounds, rfl⟩ : ∃ k, rounds = k + 1 := ⟨rounds - 1, by omega⟩
    rw [finished, finished]
    exact ⟨rfl, trivial⟩
  · obtain ⟨threshold, notStuck, same, stable⟩ := settled.settles inside empty
    cases computed : family.round threshold state.remaining with
    | stuck => exact absurd computed notStuck
    | refuted absent =>
        have step : ∀ fuel', threshold ≤ fuel' → ∀ rounds',
            drive (family.solver fuel') (rounds' + 1) state =
              .refuted fun solvable => absent (state.solvable_iff.mp solvable) := by
          intro fuel' enough' rounds'
          rw [drive_succ, advance_refuted fuel' empty ((same fuel' enough').trans computed)]
        refine ⟨threshold, 1, fun fuel enough rounds more => ?_⟩
        obtain ⟨rounds, rfl⟩ : ∃ k, rounds = k + 1 := ⟨rounds - 1, by omega⟩
        rw [step fuel enough rounds, step threshold le_rfl 0]
        exact ⟨rfl, trivial⟩
    | progress update smaller =>
        have nextInside := stable computed
        have smaller' := smaller
        rw [ranked] at smaller'
        obtain ⟨fuel₁, rounds₁, later⟩ := ih _ smaller' (state.then update) rfl nextInside
        have step : ∀ fuel', threshold ≤ fuel' → ∀ rounds',
            drive (family.solver fuel') (rounds' + 1) state = drive (family.solver fuel') rounds' (state.then update) := by
          intro fuel' enough' rounds'
          rw [drive_succ, advance_progress fuel' empty ((same fuel' enough').trans computed)]
        refine ⟨max threshold fuel₁, rounds₁ + 1, fun fuel enough rounds more => ?_⟩
        obtain ⟨rounds, rfl⟩ : ∃ k, rounds = k + 1 := ⟨rounds - 1, by omega⟩
        rw [step fuel (le_of_max_le_left enough), step (max threshold fuel₁) (le_max_left _ _)]
        obtain ⟨first, decided⟩ := later fuel (le_of_max_le_right enough) rounds (by omega)
        obtain ⟨second, _⟩ := later (max threshold fuel₁) (le_max_right _ _) rounds₁ le_rfl
        exact ⟨first.trans second.symm, second ▸ decided⟩

/-- **Decisiveness at one joint budget**: on the class, the run from the original store, with the
same number for the executable budget and the rounds, reaches a principal answer or a certified
refutation, and the same outcome at every larger joint budget. -/
theorem decided (inside : settled.holds original) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (family.solver larger) original larger = run (family.solver budget) original budget ∧
      ((∃ state finished, run (family.solver larger) original larger = .solved state finished ∧
          (frames levels).Principal original state.answer) ∨
        (∃ absent, run (family.solver larger) original larger = .refuted absent)) := by
  obtain ⟨fuel₀, rounds₀, eventual⟩ := settled.eventually (Update.pending levels original) inside
  refine ⟨max fuel₀ rounds₀, fun larger enough => ?_⟩
  obtain ⟨atLarger, decidedAt⟩ := eventual larger (le_of_max_le_left enough) larger (le_of_max_le_right enough)
  obtain ⟨atBudget, _⟩ := eventual (max fuel₀ rounds₀) (le_max_left _ _) (max fuel₀ rounds₀) (le_max_right _ _)
  unfold run
  refine ⟨atLarger.trans atBudget.symm, ?_⟩
  rw [atLarger]
  cases outcome : drive (family.solver fuel₀) rounds₀ (Update.pending levels original) with
  | solved state finished => exact .inl ⟨state, finished, rfl, state.completed finished⟩
  | refuted absent => exact .inr ⟨absent, rfl⟩
  | stuck _ => rw [outcome] at decidedAt; exact False.elim decidedAt
  | cutoff _ => rw [outcome] at decidedAt; exact False.elim decidedAt

end Settled

end ContextualDependentDecisiveDriver
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
