import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.ExactTransitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesCumulativePrincipal

/-!
# The true theorem on the dependent fibre of the tree

The dependent fibre already in the tree (`ContextualDependentEta.frames`: typed contexts, typed
terms up to typed equality, context morphisms) is an instance of the frames, so the theorems of
`ExactTransitions` apply to it unchanged.

* The worklist driver's states (`ContextualDependentUpdate.Update`: an answer and a residual, sound
  and complete) are **exactly exact transitions** (`update_exact`, `exact_iff_update`). So every
  outcome of that driver that carries a state is exact (`outcome_exact`): its stuck outcome is the
  postponed outcome of the true theorem.
* On `crossStore`, solvable and without principal answer (`fragment_without_principal_answer`),
  **every exact solver that stops, stops postponed** (`cross_postponed`), and every state of the
  driver on it has a nonempty exact residual (`cross_driver_states`). This is the true form of
  what `acceptance_conclusion_false` refutes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace DependentFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- **A state of the driver is an exact transition.** -/
theorem update_exact {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}
    (u : Update levels problem) : Exact (frames levels) problem u.answer u.remaining := by
  intro Δ f
  constructor
  · intro solved
    obtain ⟨residual, solvedR, agree⟩ := u.complete Δ f solved
    exact ⟨residual, agree, solvedR⟩
  · rintro ⟨g, fg, solvedG⟩
    exact (models_of_agree fg problem).mpr (u.sound Δ g solvedG)

/-- **And every exact transition is a state of the driver.** -/
theorem exact_iff_update {Γ m : Context rules} {problem : EquationStore (TotalTerm Γ)}
    (answer : m ⟶ Γ) (remaining : EquationStore (TotalTerm m)) :
    Exact (frames levels) problem answer remaining ↔
      ∃ u : Update levels problem, ∃ same : u.target = m,
        same ▸ u.answer = answer ∧ same ▸ u.remaining = remaining := by
  constructor
  · intro exact
    refine ⟨⟨m, answer, remaining, fun Δ residual solved => ?_, fun Δ solution solved => ?_⟩,
      rfl, rfl, rfl⟩
    · exact (exact Δ _).mpr ⟨residual, Agree.refl _, solved⟩
    · obtain ⟨g, fg, solvedG⟩ := (exact Δ solution).mp solved
      exact ⟨g, solvedG, fg⟩
  · rintro ⟨u, rfl, rfl, rfl⟩
    exact update_exact u

/-- **Every outcome of the driver that carries a state is exact.** -/
theorem outcome_exact {Γ : Context rules} {original : EquationStore (TotalTerm Γ)}
    (outcome : Outcome levels original) :
    ∀ state ∈ outcome.state?, Exact (frames levels) original state.answer state.remaining :=
  fun state _ => update_exact state

open ContextualDependentSweep.Witnesses in
/-- **On the cross store, every exact solver that stops, stops postponed.** -/
theorem cross_postponed (P : Solver (frames ContextualDependentPatternFiring.Controls.setting.levels))
    {m : Context ContextualDependentPatternFiring.Controls.setting.R} {σ : m ⟶ ctxCross}
    {R : EquationStore (TotalTerm m)} (run : P.Reaches crossStore m σ R) :
    R ≠ [] ∧ (∀ r : Reason, ¬ P.Refutes R r) ∧
      Exact (frames ContextualDependentPatternFiring.Controls.setting.levels) crossStore σ R :=
  postponed_of_solvable_no_principal fragment_without_principal_answer.2.1
    (fun _ answer => fragment_without_principal_answer.2.2 answer) run

open ContextualDependentSweep.Witnesses in
/-- **Every state of the driver on the cross store has a nonempty exact residual.** -/
theorem cross_driver_states
    (solver : ContextualDependentWorklist.Solver ContextualDependentPatternFiring.Controls.setting.levels)
    (fuel : Nat) :
    ∀ state ∈ (run solver crossStore fuel).state?, state.remaining ≠ [] ∧
      Exact (frames ContextualDependentPatternFiring.Controls.setting.levels) crossStore
        state.answer state.remaining := by
  intro state _
  have exact := update_exact state
  refine ⟨fun empty => ?_, exact⟩
  rw [empty] at exact
  exact fragment_without_principal_answer.2.2 state.answer (exact_nil_iff_principal.mp exact)

end DependentFibre

#print axioms DependentFibre.update_exact
#print axioms DependentFibre.exact_iff_update
#print axioms DependentFibre.cross_postponed
#print axioms DependentFibre.cross_driver_states

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
