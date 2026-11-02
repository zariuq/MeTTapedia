import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedSelfPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPairActive

/-!
# Secondary progress of the named same-hole frame update

Reindexing carries both image size and parameter cost to the distinguished
port. Pruning different maps cannot increase the actual residual image
potential, and strictly decreases its active parameter cost. The selected
equation is discharged; every other instantiated equation remains.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedSelfProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport

variable {S : Signature} {V Next : Type} [DecidableEq V] {source : V → MetaArity S}
  {next : Next → MetaArity S}

theorem model_progress (identity : V) {Γ : Ctx S}
    (left right : Ren S (source identity).1 Γ) (different : left ≠ right)
    (rest : Problem source) (candidate : Assignment source next)
    (solved : Models candidate
      ((observe (rename (S := signature S source) left (generator source identity)),
        observe (rename (S := signature S source) right (generator source identity))) :: rest)) :
    let update := ContextualNamedSelfPair.apply source identity left right rest
    letI := update.equality
    ∃ remaining : Assignment update.declaration next, Models remaining update.remaining ∧
      (∀ name, candidate name = instantiate remaining (update.answer name)) ∧
      potential remaining (active update.remaining) ≤ potential candidate
        (active ((observe (rename (S := signature S source) left (generator source identity)),
          observe (rename (S := signature S source) right (generator source identity))) :: rest)) ∧
      ContextualInterfacePotential.cost update.declaration (active update.remaining) <
        ContextualInterfacePotential.cost source
          (active ((observe (rename (S := signature S source) left (generator source identity)),
            observe (rename (S := signature S source) right (generator source identity))) :: rest)) := by
  let problem := (observe (rename (S := signature S source) left (generator source identity)),
    observe (rename (S := signature S source) right (generator source identity))) :: rest
  let others : ContextualFrameSelection.Remaining identity → MetaArity S := fun other => source other.val
  let selected := ContextualSelectedOccurrences.selected source identity
  let backward := reindex (ContextualFrameSelection.split identity).symm
    (ContextualFrameSelection.backward_preserves source identity)
  let moved := Assignment.compose candidate backward
  let equalizer := ScopeEqualizer.Finite.build left right
  let answer := ContextualSelfPair.answer equalizer (source identity).2 others
  have movedSolved : Models moved (mapProblem selected problem) :=
    (ContextualActiveReindex.models_reindex_back (ContextualFrameSelection.split identity)
      (ContextualFrameSelection.forward_preserves source identity)
      (ContextualFrameSelection.backward_preserves source identity) problem candidate).mpr solved
  have chosen :
      (observe (rename (S := signature S (ContextualFrameSelection.declarations source identity)) left
        (generator (ContextualFrameSelection.declarations source identity) (.inl ()))),
       observe (rename (S := signature S (ContextualFrameSelection.declarations source identity)) right
        (generator (ContextualFrameSelection.declarations source identity) (.inl ())))) ∈ mapProblem selected problem := by
    dsimp only [problem, selected]
    rw [ContextualSelectedOccurrences.selected_problem]
    exact List.mem_cons_self
  obtain ⟨remaining, models, components, images, parameters⟩ := ContextualSelfPairActive.model_progress
    different (source identity).2 others (mapProblem selected problem) chosen moved movedSolved
  have back : Assignment.compose moved selected = candidate := by
    have inverse : Assignment.compose backward selected = generator source :=
      reindex_left_inverse (S := S) (source := source)
        (target := ContextualFrameSelection.declarations source identity)
        (ContextualFrameSelection.split identity) (ContextualFrameSelection.split identity).symm
        (ContextualFrameSelection.forward_preserves source identity)
        (ContextualFrameSelection.backward_preserves source identity) (ContextualFrameSelection.split identity).left_inv
    dsimp only [moved]
    rw [← Assignment.compose_associative, inverse, Assignment.compose_identity_right]
  have factors : moved = Assignment.compose remaining answer := funext components
  have original : candidate = Assignment.compose remaining (Assignment.compose answer selected) := by
    rw [← back, factors, ← Assignment.compose_associative]
  have startImages := ContextualActiveReindex.potential_reindex_exact (ContextualFrameSelection.split identity)
    (ContextualFrameSelection.forward_preserves source identity)
    (ContextualFrameSelection.backward_preserves source identity) problem candidate
  have startParameters := ContextualInterfacePotential.reindex_exact source
    (ContextualFrameSelection.declarations source identity) (ContextualFrameSelection.split identity)
    (ContextualFrameSelection.forward_preserves source identity)
    (ContextualFrameSelection.backward_preserves source identity) problem
  have retained : active (mapProblem answer (mapProblem selected rest)) ⊆
      active (mapProblem answer (mapProblem selected problem)) := active_tail_subset _ _
  refine ⟨remaining, ?_, fun name => congrFun original name, ?_, ?_⟩
  · exact fun equation member => models equation (List.mem_cons_of_mem _ member)
  · exact ((potential_monotone remaining retained).trans images).trans_eq startImages
  · exact (lt_of_le_of_lt (ContextualInterfacePotential.monotone _ retained) parameters).trans_eq startParameters

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedSelfProgress
