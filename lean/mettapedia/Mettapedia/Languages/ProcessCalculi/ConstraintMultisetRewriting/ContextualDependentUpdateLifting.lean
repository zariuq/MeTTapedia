import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUpdate

/-!
# Solver updates beneath later dependent declarations

A solver update of Gamma lifts to Gamma.A by reindexing A along the computed
answer and using the existing typed comprehension lift. Every original
solution factors through the lifted answer. Its newest component is retained
and retyped by the equality of the prefix substitutions; no independence of
A, closed inhabitant, or equality of raw solution codes is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax

namespace ContextualDependentEta

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

/-- Equality on all judged terms includes the typed variables. -/
theorem substEq_of_act_equal {Γ Δ : Context rules} {first second : Δ ⟶ Γ}
    (same : ∀ term : TotalTerm Γ, (frames levels).E (term.reindex first) (term.reindex second)) :
    homTypedEquality rules first second := by
  refine ⟨first.typed, fun index => ?_⟩
  obtain ⟨levelHead, universeWitness, formed⟩ := Γ.formed.lookup index
  exact (same ⟨⟨Ctx.lookup Γ.raw index, levelHead, universeWitness, formed⟩,
    ⟨.var index, .var index⟩⟩).2

theorem types_equal_of_act_equal {Γ Δ : Context rules} {first second : Δ ⟶ Γ}
    (same : ∀ term : TotalTerm Γ, (frames levels).E (term.reindex first) (term.reindex second))
    (type : TypeOver Γ) : TypeEq rules Δ.raw (type.reindex first).code (type.reindex second).code :=
  ⟨type.level, type.universeWitness, type.formed.functional (substEq_of_act_equal levels same)⟩

end ContextualDependentEta

namespace ContextualDependentUpdate

open ContextualDependentEta

variable {Head : Type} {rules : Rules Head}

theorem lift_projection {Γ Δ : Context rules} (answer : Δ ⟶ Γ) (type : TypeOver Γ) :
    rawLift answer type ≫ projectionHom Γ type =
      projectionHom Δ (type.reindex answer) ≫ answer := by
  apply Hom.ext
  funext index
  change rename wk (answer.substitution index) = subst projection (answer.substitution index)
  exact (subst_projection _).symm

variable {L : Type} [UniverseLevel.LevelOrder L] {levels : LevelModel rules L}

namespace Update

/-- The actual extended answer rewrites the later declaration's type and
retains its value slot. The solution factors carry the necessary retyping. -/
def lift {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}
    (update : Update levels problem) (type : TypeOver Γ) :
    Update levels ((frames levels).applyStore (projectionHom Γ type) problem) where
  target := extend update.target (type.reindex update.answer)
  answer := rawLift update.answer type
  remaining := (frames levels).applyStore (projectionHom update.target (type.reindex update.answer)) update.remaining
  sound := by
    intro Δ solution solved
    apply (Frames.models_applyStore (X := frames levels) (projectionHom Γ type)
      (solution ≫ rawLift update.answer type) problem).mpr
    have restricted := (Frames.models_applyStore (X := frames levels)
      (projectionHom update.target (type.reindex update.answer)) solution update.remaining).mp solved
    have original := update.sound Δ
      (solution ≫ projectionHom update.target (type.reindex update.answer)) restricted
    change (frames levels).Models ((solution ≫ rawLift update.answer type) ≫ projectionHom Γ type) problem
    rw [Category.assoc, lift_projection, ← Category.assoc]
    exact original
  complete := by
    intro Δ solution solved
    let restrictedMap := solution ≫ projectionHom Γ type
    have prefixModels : (frames levels).Models restrictedMap problem :=
      (Frames.models_applyStore (X := frames levels) (projectionHom Γ type) solution problem).mp solved
    obtain ⟨residual, residualModels, prefixFactor⟩ := update.complete Δ restrictedMap prefixModels
    have prefixEqual := substEq_of_act_equal levels prefixFactor
    have annotations : TypeEq rules Δ.raw (type.reindex restrictedMap).code
        ((type.reindex update.answer).reindex residual).code := by
      have same := types_equal_of_act_equal levels prefixFactor type
      rw [type.reindex_comp residual update.answer] at same
      exact same
    let component := (pulledNewest solution).convertType
      ((type.reindex update.answer).reindex residual) annotations
    let extended := pair residual component
    have componentCode : component.code = solution.substitution 0 := by
      simp only [component, Term.convertType_code, pulledNewest_code]
    refine ⟨extended, ?_, ?_⟩
    · apply (Frames.models_applyStore (X := frames levels)
        (projectionHom update.target (type.reindex update.answer)) extended update.remaining).mpr
      change (frames levels).Models (pair residual component ≫
        projectionHom update.target (type.reindex update.answer)) update.remaining
      rw [pair_projection]
      exact residualModels
    · apply act_equal_of_substEq levels
      refine ⟨solution.typed, fun index => ?_⟩
      refine Fin.cases ?_ (fun index => ?_) index
      · change Equal rules Δ.raw (solution.substitution 0) component.code
          (subst solution.substitution (Ctx.lookup (extend Γ type).raw 0))
        rw [componentCode]
        exact .refl (solution.typed 0)
      · have earlier := prefixEqual.2 index
        change Equal rules Δ.raw (solution.substitution index.succ)
          (subst residual.substitution (update.answer.substitution index))
          (subst (subComp solution.substitution projection) (Ctx.lookup Γ.raw index)) at earlier
        rw [← subst_subComp, subst_projection] at earlier
        change Equal rules Δ.raw (solution.substitution index.succ)
          (subst (consSub component.code residual.substitution) (rename wk (update.answer.substitution index)))
          (subst solution.substitution (rename wk (Ctx.lookup Γ.raw index)))
        rw [subst_consSub_rename_wk]
        exact earlier

theorem lift_target_type {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}
    (update : Update levels problem) (type : TypeOver Γ) :
    (update.lift type).target.raw = .snoc update.target.raw (subst update.answer.substitution type.code) := rfl

theorem lift_answer_newest {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}
    (update : Update levels problem) (type : TypeOver Γ) :
    (update.lift type).answer.substitution 0 = .var (0 : Fin (update.target.arity + 1)) := rfl

theorem lift_completed {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}
    (update : Update levels problem) (type : TypeOver Γ) (finished : update.remaining = []) :
    (frames levels).Principal ((frames levels).applyStore (projectionHom Γ type) problem)
      (update.lift type).answer := by
  apply (update.lift type).completed
  simp only [lift, finished, Frames.applyStore, List.map_nil]

end Update
end ContextualDependentUpdate
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
