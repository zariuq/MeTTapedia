import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedFlexPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualHeterogeneousFlexProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveReindex

/-!
# Progress of the named flexible-pair frame update

The two selected identities retain their independent arities and result-sort
witness. Reindexing preserves the actual active-model potential; their
computed common helper then strictly decreases it. The proof concerns the
same frame update that the executable worklist selects.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedFlexProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport

variable {S : Signature} {V Next : Type} [DecidableEq V] {source : V → MetaArity S}
  {next : Next → MetaArity S}

theorem model_progress (first second : V) (different : first ≠ second)
    (sorts : (source first).2 = (source second).2) {Γ : Ctx S}
    (left : Ren S (source first).1 Γ) (right : Ren S (source second).1 Γ)
    (rest : Problem source) (candidate : Assignment source next)
    (solved : Models candidate
      ((observe (rename (S := signature S source) left (generator source first)),
        observe (rename (S := signature S source) right (generator source second))) :: rest)) :
    let update := ContextualNamedFlexPair.apply source first second different sorts left right rest
    letI := update.equality
    ∃ remaining : Assignment update.declaration next, Models remaining update.remaining ∧
      (∀ identity, candidate identity = instantiate remaining (update.answer identity)) ∧
      potential remaining (active update.remaining) < potential candidate
        (active ((observe (rename (S := signature S source) left (generator source first)),
          observe (rename (S := signature S source) right (generator source second))) :: rest)) := by
  let problem := (observe (rename (S := signature S source) left (generator source first)),
    observe (rename (S := signature S source) right (generator source second))) :: rest
  let others : ContextualPairSelection.Remaining first second → MetaArity S := fun other => source other.val
  let selected := ContextualSelectedPairs.selected source first second different
  let backward := reindex (ContextualPairSelection.split first second different).symm
    (ContextualPairSelection.backward_preserves source first second different)
  let moved := Assignment.compose candidate backward
  have movedSolved : Models moved (mapProblem selected problem) :=
    (ContextualActiveReindex.models_reindex_back (ContextualPairSelection.split first second different)
      (ContextualPairSelection.forward_preserves source first second different)
      (ContextualPairSelection.backward_preserves source first second different) problem candidate).mpr solved
  dsimp only [problem, selected] at movedSolved
  rw [ContextualSelectedPairs.selected_problem] at movedSolved
  let final := ContextualHeterogeneousFlexPair.apply (S := S) (source first).1 (source second).1
    (source first).2 (source second).2 sorts others left right (mapProblem selected rest)
  let _ := final.equality
  obtain ⟨remaining, models, components, decrease⟩ := ContextualHeterogeneousFlexProgress.model_progress
    (source first).1 (source second).1 (source first).2 (source second).2 sorts others left right
    (mapProblem selected rest) moved movedSolved
  have back : Assignment.compose moved selected = candidate := by
    have inverse : Assignment.compose backward selected = generator source :=
      reindex_left_inverse (S := S) (source := source)
        (target := ContextualPairSelection.declarations source first second)
        (ContextualPairSelection.split first second different) (ContextualPairSelection.split first second different).symm
        (ContextualPairSelection.forward_preserves source first second different)
        (ContextualPairSelection.backward_preserves source first second different)
        (ContextualPairSelection.split first second different).left_inv
    dsimp only [moved]
    rw [← Assignment.compose_associative, inverse, Assignment.compose_identity_right]
  have factors : moved = Assignment.compose remaining final.answer := funext components
  have original : candidate = Assignment.compose remaining (Assignment.compose final.answer selected) := by
    rw [← back, factors, ← Assignment.compose_associative]
  have start := ContextualActiveReindex.potential_reindex_exact (ContextualPairSelection.split first second different)
    (ContextualPairSelection.forward_preserves source first second different)
    (ContextualPairSelection.backward_preserves source first second different) problem candidate
  dsimp only [problem, selected, ContextualSelectedPairs.selected] at start
  rw [ContextualSelectedPairs.selected_problem] at start
  exact ⟨remaining, models, fun identity => congrFun original identity, decrease.trans_eq start⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedFlexProgress
