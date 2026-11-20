import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationQueryTransport

/-!
# Exact solver information under invertible change of source frame

Only the problem's frame changes. An exact residual update keeps the same
target frame and the same residual equations, with its answer composed with
the inverse comparison. No residual refinement is asserted to be invertible,
and a pending update is not turned into a principal solution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SolverTransport

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {Γ Δ : Context rules}
  {problem : EquationStore (TotalTerm Γ)}

def residual (comparison : Δ ≅ Γ) (update : ContextualDependentUpdate.Update levels problem) :
    ContextualDependentUpdate.Update levels ((frames levels).applyStore comparison.hom problem) where
  target := update.target
  answer := update.answer ≫ comparison.inv
  remaining := update.remaining
  sound := by
    intro observer further solved
    apply (Frames.models_applyStore (X := frames levels) comparison.hom (further ≫ (update.answer ≫ comparison.inv)) problem).mpr
    change (frames levels).Models ((further ≫ (update.answer ≫ comparison.inv)) ≫ comparison.hom) problem
    simpa only [Category.assoc, comparison.inv_hom_id, Category.comp_id] using update.sound observer further solved
  complete := by
    intro observer solution solved
    obtain ⟨further, remains, agree⟩ := update.complete observer (solution ≫ comparison.hom)
      ((Frames.models_applyStore (X := frames levels) comparison.hom solution problem).mp solved)
    refine ⟨further, remains, fun term => ?_⟩
    have carried := agree (term.reindex comparison.inv)
    simpa only [← ContextualDependentEta.reindex_comp, Category.assoc,
      comparison.hom_inv_id, Category.comp_id] using carried

theorem residual_equations (comparison : Δ ≅ Γ)
    (update : ContextualDependentUpdate.Update levels problem) :
    (residual comparison update).remaining = update.remaining := rfl

theorem residual_answer_square (comparison : Δ ≅ Γ)
    (update : ContextualDependentUpdate.Update levels problem) :
    (residual comparison update).answer ≫ comparison.hom = update.answer := by
  simp only [residual, Category.assoc, comparison.inv_hom_id, Category.comp_id]

theorem principal (comparison : Δ ≅ Γ) {target : Context rules} {answer : target ⟶ Γ}
    (certificate : (frames levels).Principal problem answer) :
    (frames levels).Principal ((frames levels).applyStore comparison.hom problem) (answer ≫ comparison.inv) where
  sound := by
    apply (Frames.models_applyStore (X := frames levels) comparison.hom (answer ≫ comparison.inv) problem).mpr
    change (frames levels).Models ((answer ≫ comparison.inv) ≫ comparison.hom) problem
    simpa only [Category.assoc, comparison.inv_hom_id, Category.comp_id] using certificate.sound
  factors := by
    intro observer solution solved
    obtain ⟨further, agree⟩ := certificate.factors observer (solution ≫ comparison.hom)
      ((Frames.models_applyStore (X := frames levels) comparison.hom solution problem).mp solved)
    refine ⟨further, fun term => ?_⟩
    have carried := agree (term.reindex comparison.inv)
    change (frames levels).E
      ((term.reindex comparison.inv).reindex (solution ≫ comparison.hom))
      ((term.reindex comparison.inv).reindex (further ≫ answer)) at carried
    change (frames levels).E (term.reindex solution) (term.reindex (further ≫ (answer ≫ comparison.inv)))
    simpa only [← ContextualDependentEta.reindex_comp, Category.assoc,
      comparison.hom_inv_id, Category.comp_id] using carried

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SolverTransport

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SolverTransport.residual
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SolverTransport.principal
