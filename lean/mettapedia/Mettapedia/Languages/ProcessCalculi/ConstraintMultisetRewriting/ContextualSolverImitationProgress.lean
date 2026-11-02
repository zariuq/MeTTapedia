import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverCases
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedImitationProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemMapping
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemPermutation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverMeasure

/-!
# Located imitation uses the same residual frame and strict model decrease

The actual queue order retained by the executable choice is compared with
the distinguished-head progress law through an explicit permutation.
Contextual queue mapping composes on both existing observations. Models,
component factorization and the strict primary decrease therefore hold for
the same located operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverImitationProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualSolverCases
open ContextualSolverMeasure

variable {S : Signature} {V Next : Type} [DecidableEq V] {source : V → MetaArity S}
  {next : Next → MetaArity S}

def choice (identity : V) {Γ : Ctx S} (rho : Ren S (source identity).1 Γ)
    (operator : S.Op (source identity).2) (fields : Args (signature S source) (S.arity operator) Γ)
    (before after : Problem source) :
    Choice (before ++ (observe (rename (S := signature S source) rho (generator source identity)),
      observe (Term.op (.inl operator) fields)) :: after) :=
  ⟨before, _, RootCase.imitation (S := S) (source := source) identity rho operator fields, after, rfl⟩

theorem queue_permutation (identity : V) {Γ : Ctx S} (rho : Ren S (source identity).1 Γ)
    (operator : S.Op (source identity).2) (fields : Args (signature S source) (S.arity operator) Γ)
    (before after : Problem source) :
    (choice identity rho operator fields before after).perform.remaining.Perm
      (ContextualNamedImitation.apply source identity rho operator fields (before ++ after)).remaining := by
  dsimp only [choice, Choice.perform, RootCase.perform, ContextualNamedImitation.apply,
    ContextualFrameUpdate.Update.keep_left, ContextualFrameUpdate.Update.keep_right, id]
  simp only [ContextualProblemMapping.composition]
  simp only [mapProblem, List.map_cons, List.map_nil, List.map_append, List.cons_append, List.nil_append]
  exact ContextualProblemPermutation.selected_to_head _ _ _

theorem model_progress (identity : V) {Γ : Ctx S} (rho : Ren S (source identity).1 Γ)
    (operator : S.Op (source identity).2) (fields : Args (signature S source) (S.arity operator) Γ)
    (before after : Problem source) (candidate : Assignment source next)
    (solved : Models candidate (before ++
      (observe (rename (S := signature S source) rho (generator source identity)),
        observe (Term.op (.inl operator) fields)) :: after)) :
    let update := (choice identity rho operator fields before after).perform
    letI := update.equality
    ∃ remaining : Assignment update.declaration next, Models remaining update.remaining ∧
      (∀ name, candidate name = instantiate remaining (update.answer name)) ∧
      Smaller (measure remaining update.remaining)
        (measure candidate (before ++ (observe (rename (S := signature S source) rho (generator source identity)),
          observe (Term.op (.inl operator) fields)) :: after)) := by
  let equation := (observe (rename (S := signature S source) rho (generator source identity)),
    observe (Term.op (.inl operator) fields))
  have moved := ContextualProblemPermutation.selected_to_head equation before after
  have solvedHead := (ContextualProblemPermutation.models_permutation candidate moved).mp solved
  let named := ContextualNamedImitation.apply source identity rho operator fields (before ++ after)
  let _ := named.equality
  obtain ⟨remaining, models, components, decrease⟩ := ContextualNamedImitationProgress.model_progress
    identity rho operator fields (before ++ after) candidate solvedHead
  have tails := queue_permutation identity rho operator fields before after
  have samePotential := ContextualProblemPermutation.potential_permutation remaining tails
  have sameSource := ContextualProblemPermutation.potential_permutation candidate moved
  refine ⟨remaining, (ContextualProblemPermutation.models_permutation remaining tails).mpr models, components, ?_⟩
  apply of_image_lt
  exact lt_of_eq_of_lt samePotential (decrease.trans_eq sameSource.symm)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverImitationProgress
