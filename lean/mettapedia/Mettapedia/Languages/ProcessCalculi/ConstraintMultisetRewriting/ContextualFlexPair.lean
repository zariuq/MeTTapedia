import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFamilies
import Mettapedia.OSLF.Syntax.BindingScopePullback
import Mettapedia.OSLF.Syntax.ContextualFamilyDeclarations

/-!
# A flexible pair factors through its shared parameter interface

Two distinguished holes are replaced by one fresh hole over the pullback of
their parameter maps. All other declaration identities are retained. Every
solution into any further declaration family factors through this answer.

This is a frame-changing solver case on the existing binding terms. It does
not claim a complete solver or erase the current frame when choosing a fresh
helper. Endomorphic execution uses an explicit retained interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPair

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {Other Next : Type} {L R Γ : Ctx S}
  {left : Ren S L Γ} {right : Ren S R Γ}

abbrev sourceDeclarations (L R : Ctx S) (result : S.Srt) (others : Other → MetaArity S) :
    Bool ⊕ Other → MetaArity S := pairDeclarations (L, result) (R, result) others

abbrev targetDeclarations (common : Ctx S) (result : S.Srt) (others : Other → MetaArity S) :
    Unit ⊕ Other → MetaArity S
  | .inl _ => (common, result)
  | .inr identity => others identity

/-- Scope structure depends only on positional variables and sorts, so
adjoining metavariable operators preserves the same variable pullback. -/
def inFamily (pullback : Mettapedia.OSLF.Binding.ScopePullback left right)
    {V : Type} (declaration : V → MetaArity S) :
    Mettapedia.OSLF.Binding.ScopePullback (S := signature S declaration) left right where
  context := pullback.context
  toLeft := pullback.toLeft
  toRight := pullback.toRight
  commutes := pullback.commutes
  recover := pullback.recover
  recover_left := pullback.recover_left
  recover_right := pullback.recover_right
  recover_pair := pullback.recover_pair

def answer (pullback : Mettapedia.OSLF.Binding.ScopePullback left right)
    (result : S.Srt) (others : Other → MetaArity S) :
    Assignment (sourceDeclarations L R result others) (targetDeclarations pullback.context result others)
  | .inl false => rename (S := signature S (targetDeclarations pullback.context result others))
      pullback.toLeft (generator (targetDeclarations pullback.context result others) (.inl ()))
  | .inl true => rename (S := signature S (targetDeclarations pullback.context result others))
      pullback.toRight (generator (targetDeclarations pullback.context result others) (.inl ()))
  | .inr identity => generator (targetDeclarations pullback.context result others) (.inr identity)

theorem sound (pullback : Mettapedia.OSLF.Binding.ScopePullback left right)
    (result : S.Srt) (others : Other → MetaArity S) :
    instantiate (answer pullback result others)
        (rename (S := signature S (sourceDeclarations L R result others)) left
          (generator (sourceDeclarations L R result others) (.inl false))) =
      instantiate (answer pullback result others)
        (rename (S := signature S (sourceDeclarations L R result others)) right
          (generator (sourceDeclarations L R result others) (.inl true))) := by
  rw [ContextualFamily.instantiate_rename, ContextualFamily.instantiate_rename,
    instantiate_generator, instantiate_generator]
  simp only [answer, rename_comp]
  have maps : (fun sort position => left sort (pullback.toLeft sort position)) =
      (fun sort position => right sort (pullback.toRight sort position)) := by
    funext sort position
    exact pullback.commutes sort position
  rw [maps]

/-- Factorization compares the original declarations. The fresh helper
belongs to the answer frame, so no unrelated old value is prescribed for it. -/
theorem factors (pullback : Mettapedia.OSLF.Binding.ScopePullback left right)
    (result : S.Srt) (others : Other → MetaArity S)
    (next : Next → MetaArity S)
    (candidate : Assignment (sourceDeclarations L R result others) next)
    (solved :
      instantiate candidate
          (rename (S := signature S (sourceDeclarations L R result others)) left
            (generator (sourceDeclarations L R result others) (.inl false))) =
        instantiate candidate
          (rename (S := signature S (sourceDeclarations L R result others)) right
            (generator (sourceDeclarations L R result others) (.inl true)))) :
    ∃ residual : Assignment (targetDeclarations pullback.context result others) next,
      ∀ identity, candidate identity = instantiate residual (answer pullback result others identity) := by
  rw [ContextualFamily.instantiate_rename, ContextualFamily.instantiate_rename,
    instantiate_generator, instantiate_generator] at solved
  obtain ⟨common, firstCommon, secondCommon⟩ :=
    (inFamily pullback next).factor_terms (candidate (.inl false)) (candidate (.inl true)) solved
  let residual : Assignment (targetDeclarations pullback.context result others) next
    | .inl _ => common
    | .inr identity => candidate (.inr identity)
  refine ⟨residual, ?_⟩
  intro identity
  cases identity with
  | inl choice =>
      cases choice with
      | false =>
          change candidate (.inl false) = instantiate residual
            (rename (S := signature S (targetDeclarations pullback.context result others)) pullback.toLeft
              (generator (targetDeclarations pullback.context result others) (.inl ())))
          rw [ContextualFamily.instantiate_rename, instantiate_generator]
          exact firstCommon.symm
      | true =>
          change candidate (.inl true) = instantiate residual
            (rename (S := signature S (targetDeclarations pullback.context result others)) pullback.toRight
              (generator (targetDeclarations pullback.context result others) (.inl ())))
          rw [ContextualFamily.instantiate_rename, instantiate_generator]
          exact secondCommon.symm
  | inr identity =>
      exact (instantiate_generator residual (.inr identity)).symm

/-- Component factorization carries every old term, at every object
context and sort, through the same residual assignment. -/
theorem factors_all_terms (pullback : Mettapedia.OSLF.Binding.ScopePullback left right)
    (result : S.Srt) (others : Other → MetaArity S)
    (next : Next → MetaArity S)
    (candidate : Assignment (sourceDeclarations L R result others) next)
    (solved :
      instantiate candidate
          (rename (S := signature S (sourceDeclarations L R result others)) left
            (generator (sourceDeclarations L R result others) (.inl false))) =
        instantiate candidate
          (rename (S := signature S (sourceDeclarations L R result others)) right
            (generator (sourceDeclarations L R result others) (.inl true)))) :
    ∃ residual : Assignment (targetDeclarations pullback.context result others) next,
      ∀ {context : Ctx S} {sort : S.Srt}
        (term : Term (signature S (sourceDeclarations L R result others)) context sort),
        instantiate candidate term = instantiate residual (instantiate (answer pullback result others) term) := by
  obtain ⟨residual, components⟩ := factors pullback result others next candidate solved
  refine ⟨residual, ?_⟩
  intro context sort term
  rw [instantiate_comp]
  exact congrArg (fun assignment => instantiate assignment term) (funext components)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPair
