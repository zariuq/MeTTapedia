import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalInterface
import Mettapedia.OSLF.Syntax.ContextualFamilyComposition

/-!
# A fresh-helper answer in the ordinary shared equation-store action

The active declaration family contains two selected holes, one fresh helper
and all other holes. The old interface embeds the selected and other holes,
so an existing observed name cannot silently be reused as the helper.

The frame-changing flexible-pair answer induces an ordinary endomorphic
substitution. It is principal on every represented old observation interface.
Guard transport still requires the explicit coverage laws of `PrincipalChecks`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshAnswer

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {Other : Type} {L R Γ : Ctx S}
  {left : Ren S L Γ} {right : Ren S R Γ}

abbrev oldDeclarations (L R : Ctx S) (result : S.Srt) (others : Other → MetaArity S) :=
  ContextualFlexPair.sourceDeclarations L R result others

abbrev answerDeclarations (common : Ctx S) (result : S.Srt) (others : Other → MetaArity S) :=
  ContextualFlexPair.targetDeclarations common result others

abbrev activeDeclarations (L R common : Ctx S) (result : S.Srt) (others : Other → MetaArity S) :=
  ContextualFlexPair.sourceDeclarations L R result (answerDeclarations common result others)

def includeOld (common : Ctx S) (result : S.Srt) (others : Other → MetaArity S) :
    Assignment (oldDeclarations L R result others) (activeDeclarations L R common result others)
  | .inl false => generator (activeDeclarations L R common result others) (.inl false)
  | .inl true => generator (activeDeclarations L R common result others) (.inl true)
  | .inr identity => generator (activeDeclarations L R common result others) (.inr (.inr identity))

def includeAnswer (result : S.Srt) (others : Other → MetaArity S) (common : Ctx S) :
    Assignment (answerDeclarations common result others) (activeDeclarations L R common result others) :=
  fun identity => generator (activeDeclarations L R common result others) (.inr identity)

def answer (pullback : Mettapedia.OSLF.Binding.ScopePullback left right)
    (result : S.Srt) (others : Other → MetaArity S) :
    Assignment (activeDeclarations L R pullback.context result others)
      (activeDeclarations L R pullback.context result others)
  | .inl false => instantiate (includeAnswer result others pullback.context)
      (ContextualFlexPair.answer pullback result others (.inl false))
  | .inl true => instantiate (includeAnswer result others pullback.context)
      (ContextualFlexPair.answer pullback result others (.inl true))
  | .inr identity => generator (activeDeclarations L R pullback.context result others) (.inr identity)

theorem answer_includeOld (pullback : Mettapedia.OSLF.Binding.ScopePullback left right)
    (result : S.Srt) (others : Other → MetaArity S) :
    Assignment.compose (answer pullback result others) (includeOld pullback.context result others) =
      Assignment.compose (includeAnswer result others pullback.context)
        (ContextualFlexPair.answer pullback result others) := by
  funext identity
  cases identity with
  | inl choice =>
      cases choice <;>
        simp only [Assignment.compose, includeOld, instantiate_generator, answer]
  | inr identity =>
      change instantiate (answer pullback result others)
          (generator (activeDeclarations L R pullback.context result others) (.inr (.inr identity))) =
        instantiate (includeAnswer result others pullback.context)
          (generator (answerDeclarations pullback.context result others) (.inr identity))
      rw [instantiate_generator, instantiate_generator]
      rfl

def extendResidual (common : Ctx S) (result : S.Srt) (others : Other → MetaArity S)
    (candidate : Assignment (activeDeclarations L R common result others)
      (activeDeclarations L R common result others))
    (through : Assignment (answerDeclarations common result others)
      (activeDeclarations L R common result others)) :
    Assignment (activeDeclarations L R common result others) (activeDeclarations L R common result others)
  | .inl choice => candidate (.inl choice)
  | .inr identity => through identity

theorem extendResidual_includeAnswer (common : Ctx S) (result : S.Srt) (others : Other → MetaArity S)
    (candidate : Assignment (activeDeclarations L R common result others)
      (activeDeclarations L R common result others))
    (through : Assignment (answerDeclarations common result others)
      (activeDeclarations L R common result others)) :
    Assignment.compose (extendResidual common result others candidate through)
      (includeAnswer result others common) = through := by
  funext identity
  change instantiate (extendResidual common result others candidate through)
    (generator (activeDeclarations L R common result others) (.inr identity)) = through identity
  rw [instantiate_generator]
  rfl

abbrev originalLeft (result : S.Srt) (others : Other → MetaArity S) :
    Term (signature S (oldDeclarations L R result others)) Γ result :=
  rename (S := signature S (oldDeclarations L R result others)) left
    (generator (oldDeclarations L R result others) (.inl false))

abbrev originalRight (result : S.Srt) (others : Other → MetaArity S) :
    Term (signature S (oldDeclarations L R result others)) Γ result :=
  rename (S := signature S (oldDeclarations L R result others)) right
    (generator (oldDeclarations L R result others) (.inl true))

abbrev problem (common : Ctx S) (result : S.Srt) (others : Other → MetaArity S) :
    EquationStore (Term (signature S (activeDeclarations L R common result others)) Γ result) :=
  [(instantiate (includeOld common result others) (originalLeft (left := left) result others),
    instantiate (includeOld common result others) (originalRight (right := right) result others))]

theorem sound (pullback : Mettapedia.OSLF.Binding.ScopePullback left right)
    (result : S.Srt) (others : Other → MetaArity S) :
    (ContextualFamilies.action (activeDeclarations L R pullback.context result others) Γ result).Models
      (answer pullback result others) (problem (left := left) (right := right) pullback.context result others) := by
  intro equation member
  have same := List.mem_singleton.mp member
  subst equation
  change instantiate (answer pullback result others)
      (instantiate (includeOld pullback.context result others) (originalLeft (left := left) result others)) =
    instantiate (answer pullback result others)
      (instantiate (includeOld pullback.context result others) (originalRight (right := right) result others))
  rw [instantiate_comp, instantiate_comp]
  change instantiate (Assignment.compose (answer pullback result others) (includeOld pullback.context result others)) _ =
    instantiate (Assignment.compose (answer pullback result others) (includeOld pullback.context result others)) _
  rw [answer_includeOld, Assignment.instantiate_compose, Assignment.instantiate_compose]
  exact congrArg (instantiate (includeAnswer result others pullback.context))
    (ContextualFlexPair.sound pullback result others)

theorem factors_original_terms (pullback : Mettapedia.OSLF.Binding.ScopePullback left right)
    (result : S.Srt) (others : Other → MetaArity S)
    (candidate : Assignment (activeDeclarations L R pullback.context result others)
      (activeDeclarations L R pullback.context result others))
    (solved : (ContextualFamilies.action (activeDeclarations L R pullback.context result others) Γ result).Models
      candidate (problem (left := left) (right := right) pullback.context result others)) :
    ∃ residual : Assignment (activeDeclarations L R pullback.context result others)
        (activeDeclarations L R pullback.context result others),
      ∀ {context : Ctx S} {sort : S.Srt}
        (term : Term (signature S (oldDeclarations L R result others)) context sort),
        instantiate candidate (instantiate (includeOld pullback.context result others) term) =
          instantiate residual (instantiate (answer pullback result others)
            (instantiate (includeOld pullback.context result others) term)) := by
  have compatible := solved _ (List.mem_singleton_self _)
  change instantiate candidate (instantiate (includeOld pullback.context result others)
      (originalLeft (left := left) result others)) =
    instantiate candidate (instantiate (includeOld pullback.context result others)
      (originalRight (right := right) result others)) at compatible
  rw [instantiate_comp, instantiate_comp] at compatible
  obtain ⟨through, factored⟩ := ContextualFlexPair.factors_all_terms pullback result others
    (activeDeclarations L R pullback.context result others)
    (Assignment.compose candidate (includeOld pullback.context result others)) compatible
  let residual := extendResidual pullback.context result others candidate through
  refine ⟨residual, ?_⟩
  intro context sort term
  calc
    instantiate candidate (instantiate (includeOld pullback.context result others) term) =
        instantiate (Assignment.compose candidate (includeOld pullback.context result others)) term :=
      instantiate_comp _ _ term
    _ = instantiate through (instantiate (ContextualFlexPair.answer pullback result others) term) := factored term
    _ = instantiate (Assignment.compose residual (includeAnswer result others pullback.context))
        (instantiate (ContextualFlexPair.answer pullback result others) term) := by
      rw [extendResidual_includeAnswer]
    _ = instantiate residual (instantiate
        (Assignment.compose (includeAnswer result others pullback.context)
          (ContextualFlexPair.answer pullback result others)) term) := by
      rw [Assignment.instantiate_compose, Assignment.instantiate_compose]
    _ = instantiate residual (instantiate
        (Assignment.compose (answer pullback result others) (includeOld pullback.context result others)) term) := by
      rw [answer_includeOld]
    _ = instantiate residual (instantiate (answer pullback result others)
        (instantiate (includeOld pullback.context result others) term)) := by
      rw [Assignment.instantiate_compose]

/-- The ordinary equation action has a principal answer on every retained
old-frame interface. No value of the newly introduced helper is prescribed. -/
theorem principal_on (pullback : Mettapedia.OSLF.Binding.ScopePullback left right)
    (result : S.Srt) (others : Other → MetaArity S)
    (observed : List (Term (signature S (oldDeclarations L R result others)) Γ result)) :
    (ContextualFamilies.action (activeDeclarations L R pullback.context result others) Γ result).PrincipalOn
      (problem (left := left) (right := right) pullback.context result others) (answer pullback result others)
      (observed.map (instantiate (includeOld pullback.context result others))) := by
  refine ⟨sound pullback result others, ?_⟩
  intro candidate solved
  obtain ⟨residual, factored⟩ := factors_original_terms pullback result others candidate solved
  refine ⟨residual, ?_⟩
  intro term member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  change instantiate candidate (instantiate (includeOld pullback.context result others) original) =
    instantiate (Assignment.compose residual (answer pullback result others))
      (instantiate (includeOld pullback.context result others) original)
  rw [Assignment.instantiate_compose]
  exact factored original

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshAnswer
