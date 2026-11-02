import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverCases
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedSelfProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemMapping
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemPermutation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverMeasure

/-!
# Located same-hole pruning preserves the actual tail and lowers its measure

The chosen equation is discharged. Prefix and suffix are mapped by the same
computed fresh-frame assignment, so the named pruning progress law applies
to the actual queue retained by the executable choice.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverSelfProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualSolverCases
open ContextualSolverMeasure

variable {S : Signature} {V Next : Type} [DecidableEq V] {source : V → MetaArity S}
  {next : Next → MetaArity S}

def choice (identity : V) {Γ : Ctx S} (left right : Ren S (source identity).1 Γ) (different : left ≠ right)
    (before after : Problem source) : Choice (before ++
      (observe (rename (S := signature S source) left (generator source identity)),
        observe (rename (S := signature S source) right (generator source identity))) :: after) :=
  ⟨before, _, RootCase.selfPair (S := S) (source := source) identity left right different, after, rfl⟩

theorem same_remaining (identity : V) {Γ : Ctx S} (left right : Ren S (source identity).1 Γ)
    (different : left ≠ right) (before after : Problem source) :
    (choice identity left right different before after).perform.remaining =
      (ContextualNamedSelfPair.apply source identity left right (before ++ after)).remaining := by
  dsimp only [choice, Choice.perform, RootCase.perform, ContextualNamedSelfPair.apply,
    ContextualFrameUpdate.Update.keep_left, ContextualFrameUpdate.Update.keep_right, id]
  simp only [ContextualProblemMapping.composition]
  simp only [mapProblem, List.map_nil, List.nil_append, List.map_append]

theorem model_progress (identity : V) {Γ : Ctx S} (left right : Ren S (source identity).1 Γ)
    (different : left ≠ right) (before after : Problem source) (candidate : Assignment source next)
    (solved : Models candidate (before ++
      (observe (rename (S := signature S source) left (generator source identity)),
        observe (rename (S := signature S source) right (generator source identity))) :: after)) :
    let update := (choice identity left right different before after).perform
    letI := update.equality
    ∃ remaining : Assignment update.declaration next, Models remaining update.remaining ∧
      (∀ name, candidate name = instantiate remaining (update.answer name)) ∧
      Smaller (measure remaining update.remaining)
        (measure candidate (before ++ (observe (rename (S := signature S source) left (generator source identity)),
          observe (rename (S := signature S source) right (generator source identity))) :: after)) := by
  let equation := (observe (rename (S := signature S source) left (generator source identity)),
    observe (rename (S := signature S source) right (generator source identity)))
  have moved := ContextualProblemPermutation.selected_to_head equation before after
  have solvedHead := (ContextualProblemPermutation.models_permutation candidate moved).mp solved
  let named := ContextualNamedSelfPair.apply source identity left right (before ++ after)
  let _ := named.equality
  obtain ⟨remaining, models, components, images, parameters⟩ := ContextualNamedSelfProgress.model_progress
    identity left right different (before ++ after) candidate solvedHead
  have tail := same_remaining identity left right different before after
  have sameImages := ContextualProblemPermutation.potential_permutation candidate moved
  have sameParameters := ContextualProblemPermutation.interface_permutation moved
  refine ⟨remaining, ?_, components, ?_⟩
  · rw [tail]
    exact models
  · apply of_interface_lt
    · dsimp only [ContextualSolverMeasure.measure]
      rw [tail]
      exact images.trans_eq sameImages.symm
    · dsimp only [ContextualSolverMeasure.measure]
      rw [tail]
      exact parameters.trans_eq sameParameters.symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverSelfProgress
