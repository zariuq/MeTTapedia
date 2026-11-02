import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverCases
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedFlexProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemMapping
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemPermutation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverMeasure

/-!
# Located flexible-pair solving retains the computed common interface

Prefix and suffix remain under the same fresh-helper assignment. The named
pair's result-sort witness and component factorization are retained by the
actual located operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverFlexProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualSolverCases
open ContextualSolverMeasure

variable {S : Signature} {V Next : Type} [DecidableEq V] {source : V → MetaArity S}
  {next : Next → MetaArity S}

def choice (first second : V) (different : first ≠ second) (sorts : (source first).2 = (source second).2)
    {Γ : Ctx S} (left : Ren S (source first).1 Γ) (right : Ren S (source second).1 Γ)
    (before after : Problem source) : Choice (before ++
      (observe (rename (S := signature S source) left (generator source first)),
        observe (rename (S := signature S source) right (generator source second))) :: after) :=
  ⟨before, _, RootCase.flexPair (S := S) (source := source) first second different sorts left right, after, rfl⟩

theorem same_remaining (first second : V) (different : first ≠ second) (sorts : (source first).2 = (source second).2)
    {Γ : Ctx S} (left : Ren S (source first).1 Γ) (right : Ren S (source second).1 Γ)
    (before after : Problem source) :
    (choice first second different sorts left right before after).perform.remaining =
      (ContextualNamedFlexPair.apply source first second different sorts left right (before ++ after)).remaining := by
  dsimp only [choice, Choice.perform, RootCase.perform, ContextualNamedFlexPair.apply,
    ContextualHeterogeneousFlexPair.apply,
    ContextualFrameUpdate.Update.keep_left, ContextualFrameUpdate.Update.keep_right, id]
  simp only [ContextualProblemMapping.composition]
  simp only [mapProblem, List.map_nil, List.nil_append, List.map_append]

theorem model_progress (first second : V) (different : first ≠ second) (sorts : (source first).2 = (source second).2)
    {Γ : Ctx S} (left : Ren S (source first).1 Γ) (right : Ren S (source second).1 Γ)
    (before after : Problem source) (candidate : Assignment source next)
    (solved : Models candidate (before ++
      (observe (rename (S := signature S source) left (generator source first)),
        observe (rename (S := signature S source) right (generator source second))) :: after)) :
    let update := (choice first second different sorts left right before after).perform
    letI := update.equality
    ∃ remaining : Assignment update.declaration next, Models remaining update.remaining ∧
      (∀ name, candidate name = instantiate remaining (update.answer name)) ∧
      Smaller (measure remaining update.remaining)
        (measure candidate (before ++ (observe (rename (S := signature S source) left (generator source first)),
          observe (rename (S := signature S source) right (generator source second))) :: after)) := by
  let equation := (observe (rename (S := signature S source) left (generator source first)),
    observe (rename (S := signature S source) right (generator source second)))
  have moved := ContextualProblemPermutation.selected_to_head equation before after
  have solvedHead := (ContextualProblemPermutation.models_permutation candidate moved).mp solved
  let named := ContextualNamedFlexPair.apply source first second different sorts left right (before ++ after)
  let _ := named.equality
  obtain ⟨remaining, models, components, decrease⟩ := ContextualNamedFlexProgress.model_progress
    first second different sorts left right (before ++ after) candidate solvedHead
  have tail := same_remaining first second different sorts left right before after
  have sameSource := ContextualProblemPermutation.potential_permutation candidate moved
  refine ⟨remaining, ?_, components, ?_⟩
  · rw [tail]
    exact models
  · apply of_image_lt
    dsimp only [ContextualSolverMeasure.measure]
    rw [tail]
    exact decrease.trans_eq sameSource.symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverFlexProgress
