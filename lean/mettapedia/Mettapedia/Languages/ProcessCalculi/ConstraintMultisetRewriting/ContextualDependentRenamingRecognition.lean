import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRenamingTower
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternSolver

/-!
# Recognition compares universe levels that renaming commutation makes equal

`recognize` accepts a pattern `F x̄ ≐ t` only if the annotation of the equation and the renamed result
type of `F` agree **syntactically**, in code and in universe level. Both levels are computed by the
executable type former during spine discovery, at the same budget: the equation's from its own
annotation over the local telescope, `F`'s from its declared type over its own telescope.

When the two codes agree, they are related by the pattern's renaming composed with the weakening
past `F`, and that composite embeds `F`'s telescope into the equation's. Type formation commutes
with embeddings, so the two discovered levels agree as well: **the level comparison never rejects
a pattern whose code comparison succeeds.**
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRenaming

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ExecutableChecking ContextualDependentPiSpine ContextualDependentGeneralPattern
open TypedContextual.QuotientComprehensionSyntax

/-! ## Reindexing a spine along an embedding -/

section Reindex

variable {Head : Type} {rules : Rules Head}

theorem Embedding.comp {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k} {ρ : Ren n m}
    {τ : Ren m k} (first : Embedding Γ Δ ρ) (second : Embedding Δ Θ τ) : Embedding Γ Θ (fun i => τ (ρ i)) :=
  ⟨second.injective.comp first.injective, CtxRen.comp first.lookup second.lookup⟩

/-- **A spine reindexed along a renaming morphism** is reindexed by a renaming of its telescope,
which embeds the telescope when the base renaming embeds the base. -/
theorem reindex_embedding {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ : Context rules} (base : Δ ⟶ Γ) (ρ : Ren Γ.arity Δ.arity), base.substitution = renSub ρ →
      Embedding Γ.raw Δ.raw ρ →
      ∃ ρ' : Ren spine.target.arity (spine.reindex base).target.arity,
        (spine.map base).substitution = renSub ρ' ∧ Embedding spine.target.raw (spine.reindex base).target.raw ρ' := by
  induction spine with
  | stop type =>
      intro Δ base ρ substRen embedding
      exact ⟨ρ, substRen, embedding⟩
  | @bind Γ' shape rest ih =>
      intro Δ base ρ substRen embedding
      have lifted : (rawLift base shape.domain).substitution = renSub (liftRen ρ) := by
        change liftSub base.substitution = _
        rw [substRen, liftSub_renSub]
      have extended : Embedding (extend Γ' shape.domain).raw (extend Δ (shape.domain.reindex base)).raw (liftRen ρ) := by
        have snoc := embedding.snoc shape.domain.code
        change Embedding (.snoc Γ'.raw shape.domain.code) (.snoc Δ.raw (subst base.substitution shape.domain.code))
          (liftRen ρ)
        rw [substRen, subst_renSub]
        exact snoc
      exact ih (rawLift base shape.domain) (liftRen ρ) lifted extended

/-- The level of a reindexed result type is the level of the result type. -/
theorem lifted_result_level {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ((lifted spine).result).level = spine.result.level := by
  rw [← Spine.result_reindex]
  rfl

end Reindex

/-! ## Discovery forms its result type -/

section Discovery

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : HeadChoices S.R) (reducer : Reducer S.R)

set_option backward.isDefEq.respectTransparency false in
/-- **A discovered result type is the type former's output** on its code, in the discovered
telescope, at the discovery budget. -/
theorem discover_result_formed (fuel : Nat) :
    ∀ (count : Nat) {Γ : Context S.R} (whole : TypeOver Γ) (spine : Spine whole),
      ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel (count + 1)
          whole = some spine →
        (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel spine.target
            spine.result.code).map (fun formed => formed.val.level) = some spine.result.level := by
  intro count
  induction count with
  | zero =>
      intro Γ whole spine computed
      unfold ContextualDependentPiSpineDiscovery.discover at computed
      split at computed
      · obtain ⟨first, firstRun, afterOne⟩ := Option.bind_eq_some_iff.mp computed
        obtain ⟨second, secondRun, afterTwo⟩ := Option.bind_eq_some_iff.mp afterOne
        obtain ⟨rest, restRun, returned⟩ := Option.bind_eq_some_iff.mp afterTwo
        cases Option.some.inj returned
        simp only [ContextualDependentPiSpineDiscovery.discover, Option.some.injEq] at restRun
        subst restRun
        obtain ⟨formed, sameCode⟩ := second
        change (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
          (extend Γ first.val) formed.code).map (fun formed => formed.val.level) = some formed.level
        subst sameCode
        rw [secondRun]
        rfl
      · cases computed
  | succ count ih =>
      intro Γ whole spine computed
      unfold ContextualDependentPiSpineDiscovery.discover at computed
      split at computed
      · obtain ⟨first, firstRun, afterOne⟩ := Option.bind_eq_some_iff.mp computed
        obtain ⟨second, secondRun, afterTwo⟩ := Option.bind_eq_some_iff.mp afterOne
        obtain ⟨rest, restRun, returned⟩ := Option.bind_eq_some_iff.mp afterTwo
        cases Option.some.inj returned
        exact ih second.val rest restRun
      · cases computed

variable {reducer} (renames : Renames reducer)
include renames

/-- **The level comparison of recognition follows from its code comparison.** For a spine of the
newest metavariable's type and a telescope of the equation's annotation, both discovered at one
budget with at least one binder, a pattern whose annotation code agrees with the renamed result
type of the metavariable agrees in universe level as well. -/
theorem recognized_levels (fuel : Nat) {Γ : Context S.R} {type : TypeOver Γ} {count : Nat} {spine : Spine type}
    (discovered : ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel
      (count + 1) type = some spine)
    {scopeType : TypeOver (extend Γ type)} {count' : Nat} {scope : Spine scopeType}
    (scopeFound : ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel
      (count' + 1) scopeType = some scope)
    (pattern : Pattern spine scope)
    (sameCode : scope.result.code = ((lifted spine).result.reindex pattern.map.hom).code) :
    scope.result.level = ((lifted spine).result.reindex pattern.map.hom).level := by
  obtain ⟨ρ, mapRenaming, liftEmbedding⟩ := reindex_embedding spine (projectionHom Γ type) wk rfl
    ⟨Fin.succ_injective _, CtxRen.wk Γ.raw type.code⟩
  have argEmbedding : Embedding (lifted spine).target.raw scope.target.raw pattern.map.forward :=
    ⟨pattern.map.injective, pattern.compatible⟩
  have composite := liftEmbedding.comp argEmbedding
  have renamedCode : scope.result.code = rename (fun i => pattern.map.forward (ρ i)) spine.result.code := by
    rw [sameCode]
    change subst (renSub pattern.map.forward) (lifted spine).result.code = _
    rw [← Spine.result_reindex]
    change subst (renSub pattern.map.forward) (subst (spine.map (projectionHom Γ type)).substitution
      spine.result.code) = _
    rw [mapRenaming, subst_renSub, subst_renSub, rename_comp]
  have spineLevel := discover_result_formed facts roots heads algebra declared choices reducer fuel count type spine
    discovered
  have scopeLevel := discover_result_formed facts roots heads algebra declared choices reducer fuel count' scopeType
    scope scopeFound
  have commutes : Corr (fun formed => formed.val.level) (fun formed => formed.val.level)
      (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel scope.target
        (rename (fun i => pattern.map.forward (ρ i)) spine.result.code))
      (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel spine.target
        spine.result.code) :=
    formType_rename facts roots heads algebra declared choices renames fuel composite spine.result.code
  rw [← renamedCode] at commutes
  have levels : some scope.result.level = some spine.result.level := by
    rw [← scopeLevel, ← spineLevel]
    exact commutes
  rw [Option.some.injEq] at levels
  rw [levels]
  change spine.result.level = (lifted spine).result.level
  rw [lifted_result_level]

end Discovery

end ContextualDependentRenaming
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
