import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverCases
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverMeasure

/-!
# Located reflexivity strictly lowers structural queue weight

Dropping an identical equation retains both queue portions unchanged. The
candidate remains its own residual model; its active image and parameter
costs cannot increase, and the removed pair has positive tree weight.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverReflexiveProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualSolverCases
open ContextualActiveSupport
open ContextualEquationWeight
open ContextualSolverMeasure

variable {S : Signature} {V Next : Type} [DecidableEq V] {source : V → MetaArity S}
  {next : Next → MetaArity S}

def choice {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort) (before after : Problem source) :
    Choice (before ++ (observe term, observe term) :: after) :=
  ⟨before, _, RootCase.reflexive term, after, rfl⟩

theorem same_remaining {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort)
    (before after : Problem source) : (choice term before after).perform.remaining = before ++ after := by
  dsimp only [choice, Choice.perform, RootCase.perform, ContextualReflexive.discharge,
    ContextualFrameUpdate.Update.keep_left, ContextualFrameUpdate.Update.keep_right, List.nil_append, id]
  exact congrArg₂ (fun first second : Problem source => first ++ second)
    (ContextualReflexiveProgress.map_identity before) (ContextualReflexiveProgress.map_identity after)

theorem active_subset {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort)
    (before after : Problem source) : active (before ++ after) ⊆ active (before ++ (observe term, observe term) :: after) := by
  intro identity member
  obtain ⟨equation, selected, inside⟩ := (mem_active identity _).mp member
  apply (mem_active identity _).mpr
  refine ⟨equation, ?_, inside⟩
  rcases List.mem_append.mp selected with first | second
  · exact List.mem_append_left _ first
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ second)

theorem model_progress {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort)
    (before after : Problem source) (candidate : Assignment source next)
    (solved : Models candidate (before ++ (observe term, observe term) :: after)) :
    Models candidate (choice term before after).perform.remaining ∧
      (∀ identity, candidate identity = instantiate candidate ((choice term before after).perform.answer identity)) ∧
      Smaller (measure candidate (choice term before after).perform.remaining)
        (measure candidate (before ++ (observe term, observe term) :: after)) := by
  have included := active_subset term before after
  refine ⟨?_, fun identity => (instantiate_generator candidate identity).symm, ?_⟩
  · rw [same_remaining]
    obtain ⟨first, second⟩ := (models_append _ _ _).mp solved
    exact (models_append _ _ _).mpr ⟨first, fun equation member => second equation (List.mem_cons_of_mem _ member)⟩
  · apply of_equation_lt
    · dsimp only [ContextualSolverMeasure.measure]
      rw [same_remaining]
      exact potential_monotone candidate included
    · dsimp only [ContextualSolverMeasure.measure]
      rw [same_remaining]
      exact ContextualInterfacePotential.monotone source included
    · dsimp only [ContextualSolverMeasure.measure]
      rw [same_remaining, weight_append, weight_append, weight_cons]
      change weight before + weight after < weight before + (termSize term + termSize term + weight after)
      have positive := termSize_pos term
      omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverReflexiveProgress
