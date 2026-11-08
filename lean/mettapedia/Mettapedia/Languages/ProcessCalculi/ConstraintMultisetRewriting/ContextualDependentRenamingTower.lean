import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRenamingChecking
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalizingCertify
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentExecutableChecking

/-!
# Renaming commutation of the solver's executables, and their eventual results

The executable type former reads the universe level of a type from synthesis followed by universe
recognition, so along an embedding it computes syntactically the same level for the renamed code,
at every budget. A result an executable reaches and keeps at every larger budget is reached and
kept, renamed, on renamed inputs.

In the cumulative tower the actual normalizer is root-free and commutes with renaming, so every
statement holds there with the actual normalizer and the constructed universe choices.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRenaming

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ExecutableConversion ExecutableChecking

/-! ## Eventual results -/

section Eventual

variable {Head : Type} {R : Rules Head} [DecidableEq Head] [DecidableRel R.headEq]
  [∀ head, Decidable (R.isUniverse head)] [DecidableRel R.cumulative]
variable (heads : HeadChoices R) {reducer : Reducer R} (renames : Renames reducer)
include renames

/-- **An eventual synthesized type commutes with embeddings.** -/
theorem synth_eventually_rename {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m} (e : Embedding Γ Δ ρ)
    {term type : Tm Head n} {fuel : Nat}
    (kept : ∀ larger, fuel ≤ larger → (synth R heads reducer larger Γ term).map Sigma.fst = some type) :
    ∀ larger, fuel ≤ larger →
      (synth R heads reducer larger Δ (rename ρ term)).map Sigma.fst = some (rename ρ type) := by
  intro larger enough
  have commutes : (synth R heads reducer larger Δ (rename ρ term)).map Sigma.fst =
      ((synth R heads reducer larger Γ term).map Sigma.fst).map (rename ρ) := by
    rw [Option.map_map]
    exact synth_rename heads renames larger e term
  rw [commutes, kept larger enough]
  rfl

/-- **Eventual success of checking commutes with embeddings.** -/
theorem check_eventually_rename {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m} (e : Embedding Γ Δ ρ)
    {term type : Tm Head n} {fuel : Nat}
    (kept : ∀ larger, fuel ≤ larger → (check R heads reducer larger Γ term type).isSome) :
    ∀ larger, fuel ≤ larger → (check R heads reducer larger Δ (rename ρ term) (rename ρ type)).isSome := by
  intro larger enough
  rw [check_rename heads renames larger e term type]
  exact kept larger enough

omit [DecidableEq Head] [DecidableRel R.headEq] [DecidableRel R.cumulative] in
/-- **An eventual universe head commutes with renaming.** -/
theorem asUniverse_eventually_rename {n m : Nat} (ρ : Ren n m) {type : Tm Head n} {fuel : Nat} {level : Head}
    (kept : ∀ larger, fuel ≤ larger → (asUniverse R reducer larger type).map Subtype.val = some level) :
    ∀ larger, fuel ≤ larger → (asUniverse R reducer larger (rename ρ type)).map Subtype.val = some level := by
  intro larger enough
  rw [show _ = _ from asUniverse_rename renames larger ρ type]
  exact kept larger enough

end Eventual

/-! ## The level computed by the type former -/

section Formation

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : HeadChoices S.R) {reducer : Reducer S.R} (renames : Renames reducer)
include renames

/-- **Type formation commutes with embeddings**: the renamed code is formed exactly when the code
is, and at syntactically the same universe level. -/
theorem formType_rename (fuel : Nat) {Γ Δ : Context S.R} {ρ : Ren Γ.arity Δ.arity} (e : Embedding Γ.raw Δ.raw ρ)
    (code : Tm Head Γ.arity) :
    Corr (fun formed => formed.val.level) (fun formed => formed.val.level)
      (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Δ (rename ρ code))
      (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ code) := by
  unfold ContextualDependentPruning.formType
  simp only [Option.bind_eq_bind]
  refine Corr.bind (synth_rename choices renames fuel e code) fun a b same => ?_
  obtain ⟨T, c⟩ := a
  obtain ⟨T', c'⟩ := b
  dsimp only at same
  subst same
  exact Corr.bind (asUniverse_rename renames fuel ρ T') fun _ _ sameLevel => Corr.some_some sameLevel

/-- Formed types along an embedding have the same level. -/
theorem formType_level_rename (fuel : Nat) {Γ Δ : Context S.R} {ρ : Ren Γ.arity Δ.arity}
    (e : Embedding Γ.raw Δ.raw ρ) {code : Tm Head Γ.arity}
    {formed : {type : TypeOver Γ // type.code = code}}
    (computed : ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ code =
      some formed) :
    ∃ renamed, ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Δ
        (rename ρ code) = some renamed ∧ renamed.val.level = formed.val.level := by
  rcases (formType_rename facts roots heads algebra declared choices renames fuel e code).cases with
    ⟨_, missing⟩ | ⟨renamed, original, h₁, h₂, same⟩
  · rw [computed] at missing
    cases missing
  · rw [computed] at h₂
    cases h₂
    exact ⟨renamed, h₁, same⟩

end Formation

/-! ## The cumulative tower -/

section Tower

variable {L : Type} [UniverseLevel.LevelOrder L]

/-- **The tower's normalizer commutes with renaming.** -/
theorem red_renames : Renames (ContextualDependentExecutableConversion.red (L := L)) :=
  rootFree_normalize_renames

variable [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative]

/-- Tower synthesis along an embedding, with the actual normalizer and universe choices. -/
theorem tower_synth_rename (fuel : Nat) {n m : Nat} {Γ : Ctx (LevelTower.Head L) n} {Δ : Ctx (LevelTower.Head L) m}
    {ρ : Ren n m} (e : Embedding Γ Δ ρ) (term : Tm (LevelTower.Head L) n) :
    Corr Sigma.fst (fun result => rename ρ result.1)
      (synth (LevelTower.rules L) ContextualDependentExecutableChecking.tc ContextualDependentExecutableConversion.red
        fuel Δ (rename ρ term))
      (synth (LevelTower.rules L) ContextualDependentExecutableChecking.tc ContextualDependentExecutableConversion.red
        fuel Γ term) :=
  synth_rename _ red_renames fuel e term

/-- Tower checking along an embedding. -/
theorem tower_check_rename (fuel : Nat) {n m : Nat} {Γ : Ctx (LevelTower.Head L) n} {Δ : Ctx (LevelTower.Head L) m}
    {ρ : Ren n m} (e : Embedding Γ Δ ρ) (term type : Tm (LevelTower.Head L) n) :
    (check (LevelTower.rules L) ContextualDependentExecutableChecking.tc ContextualDependentExecutableConversion.red
        fuel Δ (rename ρ term) (rename ρ type)).isSome =
      (check (LevelTower.rules L) ContextualDependentExecutableChecking.tc ContextualDependentExecutableConversion.red
        fuel Γ term type).isSome :=
  check_rename _ red_renames fuel e term type

omit [DecidableRel (LevelTower.rules L).cumulative] in
/-- Tower conversion along an embedding. -/
theorem tower_compare_rename (fuel : Nat) {n m : Nat} {Γ : Ctx (LevelTower.Head L) n} {Δ : Ctx (LevelTower.Head L) m}
    {ρ : Ren n m} (e : Embedding Γ Δ ρ) (left right type : Tm (LevelTower.Head L) n) :
    (compare (LevelTower.rules L) ContextualDependentExecutableConversion.red fuel Δ
        (rename ρ left) (rename ρ right) (rename ρ type)).isSome =
      (compare (LevelTower.rules L) ContextualDependentExecutableConversion.red fuel Γ left right type).isSome :=
  (conversion_commutes red_renames fuel).1 e left right type

/-- **Eventual typing of normal terms commutes with embeddings in the tower**: a normal term of a
formed context is eventually synthesized at a type equal to the kernel's, and its renaming is
eventually synthesized at the renamed type. -/
theorem tower_synth_eventually_rename {n m : Nat} {Γ : Ctx (LevelTower.Head L) n} {Δ : Ctx (LevelTower.Head L) m}
    {ρ : Ren n m} (e : Embedding Γ Δ ρ) (formed : CtxFormed (LevelTower.rules L) Γ)
    {t T₀ : Tm (LevelTower.Head L) n} (normal : ContextualDependentExecutableJoin.Normal (LevelTower.rules L) t)
    (synthesized : Synth (LevelTower.rules L) (TowerModel.roles (L := L)) Γ t T₀) :
    ∃ fuel T, TypeEq (LevelTower.rules L) Γ T₀ T ∧ ∀ larger, fuel ≤ larger →
      (synth (LevelTower.rules L) ContextualDependentExecutableChecking.tc ContextualDependentExecutableConversion.red
        larger Δ (rename ρ t)).map Sigma.fst = some (rename ρ T) := by
  obtain ⟨fuel, T, r, computed, equal⟩ := (ContextualDependentExecutableChecking.realized t formed normal).1 synthesized
  refine ⟨fuel, T, equal, synth_eventually_rename _ red_renames e fun larger enough => ?_⟩
  rw [ContextualDependentExecutableChecking.synth_mono computed enough]
  rfl

end Tower

end ContextualDependentRenaming
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
