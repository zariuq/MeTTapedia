import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameUnifier
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalInterface
import Mettapedia.OSLF.Syntax.ContextualFamilyDeclarations

/-!
# Lifting a proved frame answer into the ordinary equation action

Selected old declarations and fresh helper declarations occupy disjoint
parts of the active family. A proved frame unifier that preserves the other
declarations induces an ordinary substitution, principal on the retained old
interface. This construction applies to different solver cases without
assuming that arbitrary equations have principal answers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshFrame

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {Selected Fresh Other : Type}

variable (selected : Selected → MetaArity S) (fresh : Fresh → MetaArity S) (others : Other → MetaArity S)

abbrev old := sumDeclarations selected others
abbrev target := sumDeclarations fresh others
abbrev active := sumDeclarations selected (target fresh others)

def includeOld : Assignment (old selected others) (active selected fresh others)
  | .inl identity => generator (active selected fresh others) (.inl identity)
  | .inr identity => generator (active selected fresh others) (.inr (.inr identity))

def includeTarget : Assignment (target fresh others) (active selected fresh others) :=
  fun identity => generator (active selected fresh others) (.inr identity)

def answer (frameAnswer : Assignment (old selected others) (target fresh others)) :
    Assignment (active selected fresh others) (active selected fresh others)
  | .inl identity => instantiate (includeTarget selected fresh others) (frameAnswer (.inl identity))
  | .inr identity => generator (active selected fresh others) (.inr identity)

theorem answer_includeOld
    (frameAnswer : Assignment (old selected others) (target fresh others))
    (preservesOthers : ∀ identity, frameAnswer (.inr identity) = generator (target fresh others) (.inr identity)) :
    Assignment.compose (answer selected fresh others frameAnswer) (includeOld selected fresh others) =
      Assignment.compose (includeTarget selected fresh others) frameAnswer := by
  funext identity
  cases identity with
  | inl identity =>
      change instantiate (answer selected fresh others frameAnswer)
        (generator (active selected fresh others) (.inl identity)) = _
      rw [instantiate_generator]
      rfl
  | inr identity =>
      change instantiate (answer selected fresh others frameAnswer)
          (generator (active selected fresh others) (.inr (.inr identity))) =
        instantiate (includeTarget selected fresh others) (frameAnswer (.inr identity))
      rw [instantiate_generator, preservesOthers, instantiate_generator]
      rfl

theorem answer_on_old_term
    (frameAnswer : Assignment (old selected others) (target fresh others))
    (preservesOthers : ∀ identity, frameAnswer (.inr identity) = generator (target fresh others) (.inr identity))
    {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S (old selected others)) Γ sort) :
    instantiate (answer selected fresh others frameAnswer) (instantiate (includeOld selected fresh others) term) =
      instantiate (includeTarget selected fresh others) (instantiate frameAnswer term) := by
  rw [instantiate_comp]
  change instantiate
      (Assignment.compose (answer selected fresh others frameAnswer) (includeOld selected fresh others)) term = _
  rw [answer_includeOld selected fresh others frameAnswer preservesOthers, Assignment.instantiate_compose]

def extendResidual
    (candidate : Assignment (active selected fresh others) (active selected fresh others))
    (through : Assignment (target fresh others) (active selected fresh others)) :
    Assignment (active selected fresh others) (active selected fresh others)
  | .inl identity => candidate (.inl identity)
  | .inr identity => through identity

theorem extendResidual_includeTarget
    (candidate : Assignment (active selected fresh others) (active selected fresh others))
    (through : Assignment (target fresh others) (active selected fresh others)) :
    Assignment.compose (extendResidual selected fresh others candidate through) (includeTarget selected fresh others) =
      through := by
  funext identity
  change instantiate (extendResidual selected fresh others candidate through)
    (generator (active selected fresh others) (.inr identity)) = through identity
  rw [instantiate_generator]
  rfl

/-- The old problem and its observation interface are both embedded into
the active frame. The proof uses the supplied unifier's soundness and
universal factorization, not an acceptance tag or concrete success alone. -/
theorem principal_on
    {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S (old selected others)) Γ sort))
    (frameAnswer : Assignment (old selected others) (target fresh others))
    (unifier : ContextualFrameUnifier.Principal problem frameAnswer)
    (preservesOthers : ∀ identity, frameAnswer (.inr identity) = generator (target fresh others) (.inr identity))
    (observed : List (Term (signature S (old selected others)) Γ sort)) :
    (ContextualFamilies.action (active selected fresh others) Γ sort).PrincipalOn
      (ContextualFrameUnifier.mapProblem (includeOld selected fresh others) problem)
      (answer selected fresh others frameAnswer)
      (observed.map (instantiate (includeOld selected fresh others))) := by
  constructor
  · change ContextualFrameUnifier.Models (answer selected fresh others frameAnswer)
      (ContextualFrameUnifier.mapProblem (includeOld selected fresh others) problem)
    rw [ContextualFrameUnifier.models_mapProblem,
      answer_includeOld selected fresh others frameAnswer preservesOthers]
    exact ContextualFrameUnifier.models_compose unifier.sound (includeTarget selected fresh others)
  · intro candidate solved
    change ContextualFrameUnifier.Models candidate
      (ContextualFrameUnifier.mapProblem (includeOld selected fresh others) problem) at solved
    have compatible := (ContextualFrameUnifier.models_mapProblem
      (includeOld selected fresh others) candidate problem).mp solved
    obtain ⟨through, components⟩ := unifier.factors (active selected fresh others)
      (Assignment.compose candidate (includeOld selected fresh others)) compatible
    let residual := extendResidual selected fresh others candidate through
    refine ⟨residual, ?_⟩
    intro term member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    change instantiate candidate (instantiate (includeOld selected fresh others) original) =
      instantiate (Assignment.compose residual (answer selected fresh others frameAnswer))
        (instantiate (includeOld selected fresh others) original)
    rw [Assignment.instantiate_compose]
    calc
      instantiate candidate (instantiate (includeOld selected fresh others) original) =
          instantiate (Assignment.compose candidate (includeOld selected fresh others)) original :=
        instantiate_comp _ _ original
      _ = instantiate through (instantiate frameAnswer original) :=
        ContextualFrameUnifier.factor_terms _ _ _ components original
      _ = instantiate (Assignment.compose residual (includeTarget selected fresh others))
          (instantiate frameAnswer original) := by
        rw [extendResidual_includeTarget]
      _ = instantiate residual (instantiate (includeTarget selected fresh others) (instantiate frameAnswer original)) :=
        Assignment.instantiate_compose _ _ _
      _ = instantiate residual (instantiate (answer selected fresh others frameAnswer)
          (instantiate (includeOld selected fresh others) original)) := by
        rw [answer_on_old_term selected fresh others frameAnswer preservesOthers]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshFrame
