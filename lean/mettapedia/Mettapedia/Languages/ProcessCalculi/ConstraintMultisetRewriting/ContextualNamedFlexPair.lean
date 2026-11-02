import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedPairs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualHeterogeneousFlexPair

/-!
# Two arbitrary named holes share a computed fresh parameter interface

Both original identities are selected without changing either arity. The
explicit sort equality then supplies the common pullback solver. Its actual
fresh helper and mapped residuals compose back to the original named frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedFlexPair

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

variable {S : Signature} {V : Type} [DecidableEq V]

def apply (source : V → MetaArity S) (first second : V) (different : first ≠ second)
    (sorts : (source first).2 = (source second).2) {Γ : Ctx S}
    (left : Ren S (source first).1 Γ) (right : Ren S (source second).1 Γ)
    (rest : Problem source) :
    ContextualFrameUpdate.Update
      ((observe (rename (S := signature S source) left (generator source first)),
        observe (rename (S := signature S source) right (generator source second))) :: rest) := by
  let others : ContextualPairSelection.Remaining first second → MetaArity S := fun other => source other.val
  let selected := ContextualSelectedPairs.selected source first second different
  let initial := ContextualPairSelection.reduction source first second different
    ((observe (rename (S := signature S source) left (generator source first)),
      observe (rename (S := signature S source) right (generator source second))) :: rest)
  change Reduction _ selected _ at initial
  rw [ContextualSelectedPairs.selected_problem source first second different left right rest] at initial
  let final := ContextualHeterogeneousFlexPair.apply (S := S) (source first).1 (source second).1
    (source first).2 (source second).2 sorts others left right (mapProblem selected rest)
  exact ⟨final.Variables, final.equality, final.declaration,
    Assignment.compose final.answer selected, final.remaining, initial.compose final.valid⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedFlexPair
