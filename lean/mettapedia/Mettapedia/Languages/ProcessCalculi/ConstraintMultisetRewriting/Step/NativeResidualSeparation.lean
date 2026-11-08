import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeResidual
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LawfulTransport

/-!
# The native residual's frame is not separated

`Transport.Coherent` (`Step/LawfulTransport`) asks that a residual's frame be the amalgamation of the
firing's frame and the other's result: every pair of agreeing solutions comes from one solution
(`amalgamate`), and a solution is determined by its two restrictions (`separated`). The content theorem
`Transport.Lawful.independent_iff` rests on the second.

The native residual of a live firing (`LiveFiring.residualAt`) has two restrictions, along `carry` to
the firing's information frame and along the capture of the published frame. Its frame keeps names
neither reaches: the opened private locals below the relocation `shift G`, and every scoped copy of a
solver helper. So:

* **The relocation is at least one scope** (`one_le_shift`): an execution reserves its own scopes.
* **Separation fails** (`residual_not_separated`): for every execution and every private local, there
  are two solutions of the residual's frame with the same two restrictions that are not equal on
  observations.

The square and the information law of `Coherent` hold for the native residual (`carry_captured`,
`information_residualAt`), and joint solutions amalgamate into the first-order frame
(`models_amalgam`). It is the dead names that break uniqueness, as they break the isomorphism of the
two composite states of a diamond (`Step/NativeClosing`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open NativeResidual

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace NativeResidualSeparation

variable {s : NativeState S O Γ sort} (G : ContextualConditionalExecution.Firing s.locals s.state)

/-- **An execution relocates later activations by at least one scope.** -/
theorem one_le_shift : 1 ≤ shift G := by
  have member : ContextualActivationScopes.start s.state.occupied ∈ G.target.occupied := by
    apply ContextualFreshFrameScopeLedger.old_scopes_retained
    apply Finset.mem_union_right
    simp [ContextualActivationScopes.reserved, ContextualActivationScopes.count]
  have bound : ContextualActivationScopes.start s.state.occupied ≤ G.target.occupied.sup id :=
    Finset.le_sup (f := id) member
  unfold shift
  unfold ContextualActivationScopes.start at bound ⊢
  omega

/-- The residual's frame with one more name per private local. -/
def wider : Frames.Frame S :=
  ⟨(ScopedVar (s.Local ⊕ G.update.Variables) ⊕ G.target.Names) ⊕ s.Local, Sum.elim (laterTarget G) s.locals⟩

/-- The residual's frame inside the wider frame. -/
def straight : Assignment (laterTarget G) (wider G).arity :=
  fun name => generator (wider G).arity (.inl name)

/-- The same, except that the opened private locals below the relocation go to the extra names. -/
def bent : Assignment (laterTarget G) (wider G).arity
  | .inl ⟨scope, .inl name⟩ =>
      if scope < shift G then generator (wider G).arity (.inr name)
      else generator (wider G).arity (.inl (.inl ⟨scope, .inl name⟩))
  | name => generator (wider G).arity (.inl name)

theorem bent_carry : Assignment.compose (bent G) (carry G) = Assignment.compose (straight G) (carry G) := by
  funext name
  cases name with
  | inl name =>
      have notBelow : ¬ name.scope + shift G < shift G := by omega
      exact (instantiate_generator (bent G) (.inl (ScopedVar.at (name.scope + shift G) (.inl name.name)))).trans
        ((if_neg notBelow).trans
          (instantiate_generator (straight G) (.inl (ScopedVar.at (name.scope + shift G) (.inl name.name)))).symm)
  | inr name =>
      exact (instantiate_generator (bent G) (.inr (.inl (.inr name)))).trans
        (instantiate_generator (straight G) (.inr (.inl (.inr name)))).symm

theorem bent_captured :
    Assignment.compose (bent G) (laterCaptured G) = Assignment.compose (straight G) (laterCaptured G) := by
  funext name
  exact (instantiate_generator (bent G) (.inr name)).trans (instantiate_generator (straight G) (.inr name)).symm

/-- **The native residual's frame is not separated by its two restrictions**: two solutions with the
same restriction to the firing's information frame and to the published frame differ on an
observation. -/
theorem residual_not_separated (name : s.Local) :
    ∃ (b : Frames.Frame S) (ρ ρ' : Assignment (laterTarget G) b.arity),
      Assignment.compose ρ (carry G) = Assignment.compose ρ' (carry G) ∧
        Assignment.compose ρ (laterCaptured G) = Assignment.compose ρ' (laterCaptured G) ∧
        ¬ (Frames.contextual S).Agree (a := ⟨_, laterTarget G⟩) (b := b) ρ ρ' := by
  refine ⟨wider G, bent G, straight G, bent_carry G, bent_captured G, fun agree => ?_⟩
  have below : 0 < shift G := one_le_shift G
  have same := agree (observe (generator (laterTarget G) (.inl ⟨0, .inl name⟩)))
  change observe (instantiate (bent G) (generator (laterTarget G) (.inl ⟨0, .inl name⟩))) =
    observe (instantiate (straight G) (generator (laterTarget G) (.inl ⟨0, .inl name⟩))) at same
  have terms := observe_injective same
  rw [instantiate_generator, instantiate_generator] at terms
  have images : generator (wider G).arity (.inr name) =
      generator (wider G).arity (.inl (.inl ⟨0, .inl name⟩)) :=
    (if_pos below).symm.trans terms
  unfold generator at images
  cases images

end NativeResidualSeparation

#print axioms NativeResidualSeparation.one_le_shift
#print axioms NativeResidualSeparation.bent_carry
#print axioms NativeResidualSeparation.bent_captured
#print axioms NativeResidualSeparation.residual_not_separated

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
