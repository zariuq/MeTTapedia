import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedOccurrences
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameUpdate
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitation
import Mettapedia.OSLF.Syntax.BindingArgumentSlotPositions

/-!
# Named constructor imitation as an actual frame update

The selected old hole is replaced by its rigid head and one fresh helper per
typed field. Binder prefixes belong to those helpers' own contexts. The
original selected equation and every other queued constraint are mapped,
so later rigid decomposition still has to solve the actual field equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedImitation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

variable {S : Signature} {V : Type} [DecidableEq V]

def apply (source : V → MetaArity S) (identity : V) {Γ : Ctx S}
    (rho : Ren S (source identity).1 Γ) (operator : S.Op (source identity).2)
    (arguments : Args (signature S source) (S.arity operator) Γ) (rest : Problem source) :
    ContextualFrameUpdate.Update
      ((observe (rename (S := signature S source) rho (generator source identity)),
        observe (Term.op (.inl operator) arguments)) :: rest) := by
  let others : ContextualFrameSelection.Remaining identity → MetaArity S := fun other => source other.val
  let selected := ContextualSelectedOccurrences.selected source identity
  let answer := ContextualImitation.answer (S := S) (source identity).1 operator others
  let problem := (observe (rename (S := signature S source) rho (generator source identity)),
    observe (Term.op (.inl operator) arguments)) :: rest
  let first := ContextualFrameSelection.reduction source identity problem
  change Reduction problem selected (mapProblem selected problem) at first
  have chosen :
      (observe (rename (S := signature S (ContextualFrameSelection.declarations source identity)) rho
          (generator (ContextualFrameSelection.declarations source identity) (.inl ()))),
       observe (Term.op (.inl operator) (instantiateArgs selected arguments))) ∈ mapProblem selected problem := by
    dsimp only [problem, selected]
    rw [ContextualSelectedOccurrences.selected_rigid_problem source identity rho operator arguments rest]
    exact List.mem_cons_self
  let second := ContextualImitation.reduction (S := S) (source identity).1 operator others rho
    (instantiateArgs selected arguments) (mapProblem selected problem) chosen
  exact ⟨ArgumentSlots.Slot (S.arity operator) ⊕ ContextualFrameSelection.Remaining identity,
    inferInstance, ContextualImitation.targetDeclarations (source identity).1 operator others,
    Assignment.compose answer selected, mapProblem answer (mapProblem selected problem), first.compose second⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedImitation
