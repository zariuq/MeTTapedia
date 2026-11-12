import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MeetControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruneControls

/-!
# Pruning and intersection: the tree's forcing-backed updates, as exact rules

The tree already builds pruning and intersection as updates of its driver, with the loss of no solution proved from
the actual equations, through the normal forms and their supports:

* **intersection** (`ContextualDependentIntersection.intersectRule`): `λ x̄. G ȳ ≐ λ x̄. G z̄` for the newest
  unknown, pruned to the binders where `ȳ` and `z̄` agree (`forced_intersection`);
* **flex-flex pruning** (`ContextualDependentPrune.pruneFlexFlex`): `G ȳ ≐ f x̄`, with `G` pruned to a restriction
  covering the intersection of the two argument lists (`forced_flexFlex`).

Here they are rules of the exact-transition reading: every progress of the intersection rule is exact
(`intersectRule_exact`), and every flex-flex pruning is exact (`pruneFlexFlex_exact`), both through
`exact_iff_update`.

Controls, in the tower:

* intersection fires on `λ x y. F x y ≐ λ x y. F y x`, its update is exact (`intersection_found_exact`), and the store
  has a principal answer (`intersection_principal`);
* the rule's firing condition is not the boundary of principality (`twice_principal`): the same equation stated twice
  has a principal answer, and the intersection solver is stuck on it (the tree's `twice_stuck`), because the rule
  asks that no other equation mention the unknown;
* pruning `G y z ≐ F x y` to the intersection `{y}` is exact (`pruned_exact`); a restriction that drops the first
  binder of `G` does not cover the intersection (the tree's `first_binder_forced`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

/-! ## Intersection -/

section Intersection

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- **Every progress of the tree's intersection rule is exact.** -/
theorem intersectRule_exact (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {found : ContextualDependentIntersection.Progress facts roots heads algebra rigid complete problem}
    (_ : ContextualDependentIntersection.intersectRule facts roots heads algebra rigid complete declared choices
      reducer root normalizes headTypingUnique fuel problem = some found) :
    Exact (frames S.levels) problem found.val.answer found.val.remaining :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr ⟨found.val, rfl, rfl, rfl⟩

end Intersection

/-! ## Flex-flex pruning -/

section Pruning

open ContextualDependentPiSpine ContextualDependentScope ContextualDependentGeneralPattern ContextualDependentPrune

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (facts : FormFacts S.R S.roles) (algebra : CumulativeAlgebra S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (declared : DeclaredTypesFormed S.R)

variable {Γ : Context S.R} {type : TypeOver Γ} {spine : Spine type}
  {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType}

/-- **Every flex-flex pruning is exact.** -/
theorem pruneFlexFlex_exact (pattern : Pattern spine scope) (app : Application scope)
    (sameType : app.spine.result.reindex app.map.hom = (lifted spine).result.reindex pattern.map.hom)
    {keptType : TypeOver Γ} {kept : Spine keptType} (restriction : Restriction spine kept)
    (covers : ∀ position : spine.Local, (∃ other, app.args other = pattern.args position) →
      ∃ chosen, restriction.keep chosen = position)
    (problem : EquationStore (TotalTerm (extend Γ type)))
    (contains : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type), (frames S.levels).Models solution problem →
      (pattern.constraint ((app.term).cast sameType)).Holds solution) :
    Exact (frames S.levels) problem
      (pruneFlexFlex rigid complete normalizes facts algebra headTypingUnique roots heads declared pattern app
        sameType restriction covers problem contains).answer
      (pruneFlexFlex rigid complete normalizes facts algebra headTypingUnique roots heads declared pattern app
        sameType restriction covers problem contains).remaining :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr ⟨_, rfl, rfl, rfl⟩

end Pruning

/-! ## Controls -/

namespace Controls

open ContextualDependentPatternFiring.Controls ContextualDependentFlexReorder.Controls
open ContextualDependentIntersection.Controls

/-- The intersection rule's update on `λ x y. F x y ≐ λ x y. F y x`, at budget 16. -/
noncomputable def intersectionFound :=
  (ContextualDependentIntersection.intersectRule (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentNormalCheckingTower.head_typing_unique 16 intersectionStore).get intersection_rule_fires

/-- **The intersection found on the store is exact.** -/
theorem intersection_found_exact :
    Exact (frames setting.levels) intersectionStore intersectionFound.val.answer intersectionFound.val.remaining :=
  intersectRule_exact (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentNormalCheckingTower.head_typing_unique 16 (Option.some_get _).symm

/-- A run that commits ends with a principal answer. -/
theorem principal_of_commit {Γ : Context setting.R} {original : EquationStore (TotalTerm Γ)}
    {solver : ContextualDependentWorklist.Solver setting.levels} {fuel : Nat}
    (committed : (run solver original fuel).readout = .commit) :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Γ), (frames setting.levels).Principal original answer := by
  cases outcome : run solver original fuel with
  | solved state finished => exact ⟨_, _, state.completed finished⟩
  | stuck _ => rw [outcome] at committed; cases committed
  | refuted _ => rw [outcome] at committed; cases committed
  | cutoff _ => rw [outcome] at committed; cases committed

/-- **The intersection store has a principal answer.** -/
theorem intersection_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ withBinary), (frames setting.levels).Principal intersectionStore answer :=
  principal_of_commit intersection_committed

/-- **The same equation stated twice has a principal answer**, although the intersection solver is stuck on it
(`twice_stuck`): the firing condition of the rule is not the boundary of principality. -/
theorem twice_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ withBinary), (frames setting.levels).Principal twiceStore answer := by
  obtain ⟨Δ, answer, principal⟩ := intersection_principal
  have same : ∀ {Δ' : Context setting.R} (σ : Δ' ⟶ withBinary),
      (frames setting.levels).Models σ twiceStore ↔ (frames setting.levels).Models σ intersectionStore := by
    intro Δ' σ
    rw [intersectionStore_eq]
    constructor
    · intro solved e member
      exact solved e (by rw [List.mem_singleton.mp member]; exact List.mem_cons_self)
    · intro solved e member
      have one : e = intersectionEquation := by
        rcases List.mem_cons.mp member with same | later
        · exact same
        · exact List.mem_singleton.mp later
      rw [one]
      exact solved _ (List.mem_singleton_self _)
  exact ⟨Δ, answer, ⟨(same answer).mpr principal.sound,
    fun Δ' f solved => principal.factors Δ' f ((same f).mp solved)⟩⟩

/-- **The flex-flex pruning of `G y z ≐ F x y` to `{y}` is exact.** -/
theorem pruned_exact :
    Exact (frames setting.levels) ContextualDependentPrune.Controls.store ContextualDependentPrune.Controls.pruned.answer
      ContextualDependentPrune.Controls.pruned.remaining :=
  (DependentFibre.exact_iff_update (levels := setting.levels) _ _).mpr ⟨_, rfl, rfl, rfl⟩

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
