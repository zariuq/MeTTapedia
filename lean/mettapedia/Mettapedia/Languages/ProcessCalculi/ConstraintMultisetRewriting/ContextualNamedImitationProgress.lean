import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedImitation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitationActive
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveReindex

/-!
# Progress of the named fresh-helper update used by the worklist

The actual selected identity is reindexed to the constructor-imitation port.
Its model and finite active potential move along that same equivalence. The
computed frame update then preserves the model with strictly smaller active
image potential, including all retained equations and binding-field helpers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedImitationProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport

variable {S : Signature} {V Next : Type} [DecidableEq V] {source : V → MetaArity S}
  {next : Next → MetaArity S}

theorem model_progress (identity : V) {Γ : Ctx S} (rho : Ren S (source identity).1 Γ)
    (operator : S.Op (source identity).2) (fields : Args (signature S source) (S.arity operator) Γ)
    (rest : Problem source) (candidate : Assignment source next)
    (solved : Models candidate
      ((observe (rename (S := signature S source) rho (generator source identity)),
        observe (Term.op (.inl operator) fields)) :: rest)) :
    let update := ContextualNamedImitation.apply source identity rho operator fields rest
    letI := update.equality
    ∃ remaining : Assignment update.declaration next, Models remaining update.remaining ∧
      (∀ name, candidate name = instantiate remaining (update.answer name)) ∧
      potential remaining (active update.remaining) < potential candidate
        (active ((observe (rename (S := signature S source) rho (generator source identity)),
          observe (Term.op (.inl operator) fields)) :: rest)) := by
  let problem := (observe (rename (S := signature S source) rho (generator source identity)),
    observe (Term.op (.inl operator) fields)) :: rest
  let others : ContextualFrameSelection.Remaining identity → MetaArity S := fun other => source other.val
  let selected := ContextualSelectedOccurrences.selected source identity
  let backward := reindex (ContextualFrameSelection.split identity).symm
    (ContextualFrameSelection.backward_preserves source identity)
  let moved := Assignment.compose candidate backward
  have movedSolved : Models moved (mapProblem selected problem) :=
    (ContextualActiveReindex.models_reindex_back (ContextualFrameSelection.split identity)
      (ContextualFrameSelection.forward_preserves source identity)
      (ContextualFrameSelection.backward_preserves source identity) problem candidate).mpr solved
  have chosen :
      (observe (rename (S := signature S (ContextualFrameSelection.declarations source identity)) rho
        (generator (ContextualFrameSelection.declarations source identity) (.inl ()))),
       observe (Term.op (.inl operator) (instantiateArgs selected fields))) ∈ mapProblem selected problem := by
    dsimp only [problem, selected]
    rw [ContextualSelectedOccurrences.selected_rigid_problem]
    exact List.mem_cons_self
  obtain ⟨remaining, models, components, decrease⟩ := ContextualImitationActive.model_progress
    (source identity).1 operator others rho (instantiateArgs selected fields) (mapProblem selected problem)
    chosen moved movedSolved
  have back : Assignment.compose moved selected = candidate := by
    have inverse : Assignment.compose backward selected = generator source :=
      reindex_left_inverse (S := S) (source := source)
        (target := ContextualFrameSelection.declarations source identity)
        (ContextualFrameSelection.split identity) (ContextualFrameSelection.split identity).symm
        (ContextualFrameSelection.forward_preserves source identity)
        (ContextualFrameSelection.backward_preserves source identity) (ContextualFrameSelection.split identity).left_inv
    dsimp only [moved]
    rw [← Assignment.compose_associative, inverse, Assignment.compose_identity_right]
  have factors : moved = Assignment.compose remaining (ContextualImitation.answer (source identity).1 operator others) :=
    funext components
  have original : candidate = Assignment.compose remaining
      (Assignment.compose (ContextualImitation.answer (source identity).1 operator others) selected) := by
    rw [← back, factors, ← Assignment.compose_associative]
  have start := ContextualActiveReindex.potential_reindex_exact (ContextualFrameSelection.split identity)
    (ContextualFrameSelection.forward_preserves source identity)
    (ContextualFrameSelection.backward_preserves source identity) problem candidate
  refine ⟨remaining, models, fun name => congrFun original name, ?_⟩
  exact decrease.trans_eq start

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedImitationProgress
