import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedOccurrences
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameUpdate
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnifierProfiles

/-!
# A computed fresh-helper update for an arbitrary named same-hole equation

The finite equalizer computes the parameters on which both applications
agree. Selecting the old hole, introducing its helper and retaining every
other declaration are actual substitutions. The selected equation leaves
the queue, including when the two maps are equal; remaining equations use
the new frame. No globally fresh numeric name is required.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedSelfPair

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

variable {S : Signature} {V : Type} [DecidableEq V]

def apply (source : V → MetaArity S) (identity : V) {Γ : Ctx S}
    (left right : Ren S (source identity).1 Γ) (rest : Problem source) :
    ContextualFrameUpdate.Update
      ((observe (rename (S := signature S source) left (generator source identity)),
        observe (rename (S := signature S source) right (generator source identity))) :: rest) := by
  let others : ContextualFrameSelection.Remaining identity → MetaArity S := fun other => source other.val
  let equalizer := ScopeEqualizer.Finite.build (S := S) left right
  let answer := ContextualSelfPair.answer equalizer (source identity).2 others
  let first := ContextualFrameSelection.reduction source identity
    ((observe (rename (S := signature S source) left (generator source identity)),
      observe (rename (S := signature S source) right (generator source identity))) :: rest)
  change Reduction _ (ContextualSelectedOccurrences.selected source identity) _ at first
  rw [ContextualSelectedOccurrences.selected_problem source identity left right rest] at first
  have second := of_principal_prefix
    (ContextualUnifierProfiles.same_hole equalizer (source identity).2 others)
    (mapProblem (ContextualSelectedOccurrences.selected source identity) rest)
  refine ⟨Unit ⊕ ContextualFrameSelection.Remaining identity, inferInstance,
    ContextualSelfPair.declarations equalizer.context (source identity).2 others,
    Assignment.compose answer (ContextualSelectedOccurrences.selected source identity),
    mapProblem answer (mapProblem (ContextualSelectedOccurrences.selected source identity) rest), ?_⟩
  exact first.compose second

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedSelfPair
