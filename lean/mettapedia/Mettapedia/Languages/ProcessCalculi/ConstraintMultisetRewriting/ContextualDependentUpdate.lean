import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaElimination
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaConversion

/-!
# Solution-preserving dependent solver updates

An update retains its typed answer substitution and residual equations.
Soundness reconstructs original solutions; completeness factors every
original solution through the answer, up to typed equality on all annotated
terms. Composition and transport of surrounding equations preserve both
directions. Actual definition elimination and bounded eta conversion produce
updates of this form. A completed update yields a principal answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentUpdate

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

structure Update {Γ : Context rules} (problem : EquationStore (TotalTerm Γ)) where
  target : Context rules
  answer : target ⟶ Γ
  remaining : EquationStore (TotalTerm target)
  sound : ∀ (Δ : Context rules) (residual : Δ ⟶ target),
    (frames levels).Models residual remaining → (frames levels).Models (residual ≫ answer) problem
  complete : ∀ (Δ : Context rules) (solution : Δ ⟶ Γ), (frames levels).Models solution problem →
    ∃ residual : Δ ⟶ target,
      (frames levels).Models residual remaining ∧
      ∀ term : TotalTerm Γ,
        (frames levels).E (term.reindex solution) (term.reindex (residual ≫ answer))

namespace Update

def pending {Γ : Context rules} (problem : EquationStore (TotalTerm Γ)) : Update levels problem where
  target := Γ
  answer := 𝟙 Γ
  remaining := problem
  sound := by
    intro Δ residual solved
    simpa only [Category.comp_id] using solved
  complete := by
    intro Δ solution solved
    refine ⟨solution, solved, fun term => ?_⟩
    rw [Category.comp_id]
    exact ((frames levels).equivalence Δ).refl _

variable {levels}

def rephrase {Γ : Context rules} {source target : EquationStore (TotalTerm Γ)}
    (update : Update levels target) (same : (frames levels).Equivalent source target) : Update levels source where
  target := update.target
  answer := update.answer
  remaining := update.remaining
  sound := fun Δ residual solved => (same Δ _).mpr (update.sound Δ residual solved)
  complete := fun Δ solution solved => update.complete Δ solution ((same Δ solution).mp solved)

def «then» {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}
    (first : Update levels problem) (second : Update levels first.remaining) : Update levels problem where
  target := second.target
  answer := second.answer ≫ first.answer
  remaining := second.remaining
  sound := by
    intro Δ residual solved
    simpa only [Category.assoc] using first.sound Δ (residual ≫ second.answer) (second.sound Δ residual solved)
  complete := by
    intro Δ solution solved
    obtain ⟨middle, middleModels, firstFactor⟩ := first.complete Δ solution solved
    obtain ⟨residual, remainingModels, secondFactor⟩ := second.complete Δ middle middleModels
    refine ⟨residual, remainingModels, fun term => ?_⟩
    have carried := secondFactor (term.reindex first.answer)
    rw [← reindex_comp, ← reindex_comp, Category.assoc] at carried
    exact ((frames levels).equivalence Δ).trans (firstFactor term) carried

/-- Equations outside the selected subproblem are instantiated, not
forgotten or checked only at one chosen answer. -/
def keepLeft {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}
    (update : Update levels problem) (extra : EquationStore (TotalTerm Γ)) :
    Update levels (extra ++ problem) where
  target := update.target
  answer := update.answer
  remaining := (frames levels).applyStore update.answer extra ++ update.remaining
  sound := by
    intro Δ residual solved
    obtain ⟨earlier, later⟩ := (Frames.models_append (X := frames levels) residual _ _).mp solved
    exact (Frames.models_append (X := frames levels) _ _ _).mpr
      ⟨(Frames.models_applyStore (X := frames levels) update.answer residual extra).mp earlier,
        update.sound Δ residual later⟩
  complete := by
    intro Δ solution solved
    obtain ⟨earlier, later⟩ := (Frames.models_append (X := frames levels) solution _ _).mp solved
    obtain ⟨residual, remaining, factor⟩ := update.complete Δ solution later
    refine ⟨residual, (Frames.models_append (X := frames levels) _ _ _).mpr ⟨?_, remaining⟩, factor⟩
    apply (Frames.models_applyStore (X := frames levels) update.answer residual extra).mpr
    exact (Elimination.models_pointwise levels factor extra).mp earlier

/-- The same later context is retained in both directions. In particular,
specializing it to the empty telescope preserves closed solutions separately
from the unrestricted symbolic notion. -/
theorem fixed_point_solutions_iff {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}
    (update : Update levels problem) (point : Context rules) :
    (∃ solution : point ⟶ Γ, (frames levels).Models solution problem) ↔
      ∃ residual : point ⟶ update.target, (frames levels).Models residual update.remaining := by
  constructor
  · rintro ⟨solution, solved⟩
    obtain ⟨residual, remaining, _⟩ := update.complete point solution solved
    exact ⟨residual, remaining⟩
  · rintro ⟨residual, remaining⟩
    exact ⟨residual ≫ update.answer, update.sound point residual remaining⟩

theorem solvable_iff {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}
    (update : Update levels problem) :
    (frames levels).Solvable problem ↔ (frames levels).Solvable update.remaining := by
  constructor
  · rintro ⟨Δ, solution, solved⟩
    obtain ⟨residual, remaining, _⟩ := update.complete Δ solution solved
    exact ⟨Δ, residual, remaining⟩
  · rintro ⟨Δ, residual, remaining⟩
    exact ⟨Δ, residual ≫ update.answer, update.sound Δ residual remaining⟩

/-- Finishing the actual residual queue earns principality. It is not
assumed for an update whose constraints remain open. -/
theorem completed {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}
    (update : Update levels problem) (finished : update.remaining = []) :
    (frames levels).Principal problem update.answer where
  sound := by
    have empty : (frames levels).Models (𝟙 update.target) update.remaining := by
      rw [finished]
      exact Frames.models_nil _
    simpa only [Category.id_comp] using update.sound update.target (𝟙 _) empty
  factors := by
    intro Δ solution solved
    obtain ⟨residual, _, factor⟩ := update.complete Δ solution solved
    exact ⟨residual, factor⟩

theorem entails_iff {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}
    (update : Update levels problem) (observation : (Δ : Context rules) → (Δ ⟶ Γ) → Prop)
    (respects : ∀ (Δ : Context rules) (first second : Δ ⟶ Γ),
      (∀ term : TotalTerm Γ, (frames levels).E (term.reindex first) (term.reindex second)) →
        (observation Δ first ↔ observation Δ second)) :
    (frames levels).Entails problem observation ↔
      (frames levels).Entails update.remaining (fun Δ residual => observation Δ (residual ≫ update.answer)) := by
  constructor
  · intro asked Δ residual solved
    exact asked Δ _ (update.sound Δ residual solved)
  · intro asked Δ solution solved
    obtain ⟨residual, remaining, factor⟩ := update.complete Δ solution solved
    exact (respects Δ solution _ factor).mpr (asked Δ residual remaining)

end Update

def definition {Γ : Context rules} {type : TypeOver Γ} (value : Term Γ type)
    (problem : EquationStore (TotalTerm (extend Γ type))) :
    Update levels (Elimination.definition Γ value :: problem) where
  target := Γ
  answer := Elimination.instantiate Γ value
  remaining := (frames levels).applyStore (Elimination.instantiate Γ value) problem
  sound := by
    intro Δ residual solved
    exact (Elimination.definition_models_iff levels value problem _).mpr
      ⟨residual, solved, fun term => ((frames levels).equivalence Δ).refl _⟩
  complete := fun Δ solution solved =>
    (Elimination.definition_models_iff levels value problem solution).mp solved

variable {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
variable (reducer : ExecutableReduction.Reducer S.R)

def conversion (fuel : Nat) {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) :
    Update S.levels problem where
  target := Γ
  answer := 𝟙 Γ
  remaining := Conversion.scan facts roots heads algebra reducer fuel problem
  sound := by
    intro Δ residual solved
    simpa only [Category.comp_id] using
      (Conversion.scan_models facts roots heads algebra reducer fuel residual problem).mp solved
  complete := by
    intro Δ solution solved
    refine ⟨solution, (Conversion.scan_models facts roots heads algebra reducer fuel solution problem).mpr solved,
      fun term => ?_⟩
    rw [Category.comp_id]
    exact ((frames S.levels).equivalence Δ).refl _

def defineThenConvert (fuel : Nat) {Γ : Context S.R} {type : TypeOver Γ}
    (value : Term Γ type) (problem : EquationStore (TotalTerm (extend Γ type))) :
    Update S.levels (Elimination.definition Γ value :: problem) :=
  (definition S.levels value problem).then
    (conversion facts roots heads algebra reducer fuel ((frames S.levels).applyStore (Elimination.instantiate Γ value) problem))

end ContextualDependentUpdate
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
