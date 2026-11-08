import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantPruning
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerChoices

/-!
# A principal constant-function pruning rule for the cumulative tower

Every solution of the actual scoped equation F x = F y factors through
F := lambda x.H. The outer context is retained and H has the original result
type. Checked scope closing supplies the ordinary equation-store interface;
an unavailable universe join leaves the rule unfinished.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstantPruningTower

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentScope
open ContextualDependentConstantShape ContextualDependentConstantConstraint

variable {L : Type} [UniverseLevel.LevelOrder L] (valuation : Nat → L)
variable {Γ : Context (LevelTower.rules L)}

theorem factors (shape : Shape Γ) {Δ : Context (LevelTower.rules L)}
    (solution : Δ ⟶ shape.source) (solved : shape.problem.Holds solution) :
    ∃ residual : Δ ⟶ shape.target, ∀ term : TotalTerm shape.source,
      (frames (TowerModel.setting valuation).levels).E
        (term.reindex solution) (term.reindex (residual ≫ shape.answer)) := by
  let base := solution ≫ projectionHom Γ shape.whole
  let reindexed := shape.reindex base
  have independent : Independent reindexed (pulledNewest solution) := (shape.problem_holds_iff solution).mp solved
  have sameFresh := (independent_iff_fresh (S := TowerModel.setting valuation) reindexed (pulledNewest solution)).mp independent
  obtain ⟨fuel, succeeds⟩ := ContextualDependentUnaryConstancy.eventually_recovers valuation Δ reindexed.domain reindexed.codomain
    (reindexed.fresh (pulledNewest solution)) sameFresh
  obtain ⟨recovered, _⟩ := Option.isSome_iff_exists.mp (succeeds fuel le_rfl)
  have same := reindexed.constant_of_recovery (TowerModel.setting valuation).levels (pulledNewest solution) recovered
  rw [reindexed.constantHere_code] at same
  have substitution := shape.factors_of_constant solution recovered.body same
  exact ⟨pair base recovered.body, fun term => act_equal_of_substEq (TowerModel.setting valuation).levels substitution term⟩

def solve (choices : ExecutableChecking.HeadChoices (LevelTower.rules L)) (shape : Shape Γ) :
    Option (ContextualDependentScopedDispatch.Result (TowerModel.setting valuation).levels [shape.problem]) :=
  match computed : shape.problem.closeWith (TowerModel.setting valuation).levels choices with
  | none => none
  | some closed => some <| by
      have correspondence : ∀ {Δ : Context (LevelTower.rules L)} (solution : Δ ⟶ shape.source),
          (frames (TowerModel.setting valuation).levels).Models solution [closed.equation] ↔ shape.problem.Holds solution :=
        fun solution => (Active.holds_iff_models (TowerModel.setting valuation).levels closed solution).symm.trans
          (Scoped.closeWith_holds_iff (TowerModel.setting valuation).levels choices shape.problem computed solution)
      refine ⟨⟨[closed.equation], fun solution => ?_⟩, ?_⟩
      · constructor
        · intro modeled constraint member
          obtain rfl := List.mem_singleton.mp member
          exact (correspondence solution).mp modeled
        · intro held
          exact (correspondence solution).mpr (held _ (List.mem_singleton_self _))
      · refine ⟨shape.target, shape.answer, [], ?_, ?_⟩
        · intro Δ residual _
          exact (correspondence (residual ≫ shape.answer)).mpr
            (Scoped.holds_comp (TowerModel.setting valuation).levels shape.problem shape.answer residual shape.answer_sound)
        · intro Δ solution solved
          obtain ⟨residual, factor⟩ := factors valuation shape solution ((correspondence solution).mp solved)
          exact ⟨residual, Frames.models_nil _, factor⟩

theorem solve_success_iff (choices : ExecutableChecking.HeadChoices (LevelTower.rules L)) (shape : Shape Γ) :
    (solve valuation choices shape).isSome = true ↔
      (shape.problem.closeWith (TowerModel.setting valuation).levels choices).isSome = true := by
  unfold solve
  split <;> simp_all

theorem solve_finished (choices : ExecutableChecking.HeadChoices (LevelTower.rules L)) (shape : Shape Γ)
    (result : ContextualDependentScopedDispatch.Result (TowerModel.setting valuation).levels [shape.problem])
    (computed : solve valuation choices shape = some result) : result.update.remaining = [] := by
  unfold solve at computed
  split at computed
  · cases computed
  · cases Option.some.inj computed
    rfl

theorem solve_answer (choices : ExecutableChecking.HeadChoices (LevelTower.rules L)) (shape : Shape Γ)
    (result : ContextualDependentScopedDispatch.Result (TowerModel.setting valuation).levels [shape.problem])
    (computed : solve valuation choices shape = some result) :
    ∃ same : result.update.target = shape.target,
      result.update.answer = eqToHom same ≫ shape.answer := by
  unfold solve at computed
  split at computed
  · cases computed
  · cases Option.some.inj computed
    exact ⟨rfl, (Category.id_comp _).symm⟩

theorem solve_total (shape : Shape Γ) :
    (solve valuation ExecutableTowerChoices.choices shape).isSome = true := by
  apply (solve_success_iff valuation ExecutableTowerChoices.choices shape).mpr
  apply Option.isSome_iff_exists.mpr
  apply Scoped.closeWith_exists
  intro first second firstUniverse secondUniverse
  cases firstUniverse
  cases secondUniverse
  exact ⟨_, rfl⟩

def prune (shape : Shape Γ) :
    ContextualDependentScopedDispatch.Result (TowerModel.setting valuation).levels [shape.problem] :=
  (solve valuation ExecutableTowerChoices.choices shape).get (solve_total valuation shape)

theorem prune_finished (shape : Shape Γ) : (prune valuation shape).update.remaining = [] :=
  solve_finished valuation ExecutableTowerChoices.choices shape (prune valuation shape) (Option.some_get _).symm

theorem prune_principal (shape : Shape Γ) :
    ContextualDependentScopedDispatch.Holds [shape.problem] (prune valuation shape).update.answer ∧
      ∀ (Δ : Context (LevelTower.rules L)) (solution : Δ ⟶ shape.source),
        ContextualDependentScopedDispatch.Holds [shape.problem] solution →
          ∃ residual : Δ ⟶ (prune valuation shape).update.target,
            ∀ term : TotalTerm shape.source,
              (frames (TowerModel.setting valuation).levels).E
                (term.reindex solution) (term.reindex (residual ≫ (prune valuation shape).update.answer)) :=
  (prune valuation shape).completed (prune_finished valuation shape)

end ContextualDependentConstantPruningTower
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
