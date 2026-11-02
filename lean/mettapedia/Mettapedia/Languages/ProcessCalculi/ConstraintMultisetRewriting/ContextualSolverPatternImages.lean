import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternPreservation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualVariableBinding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBinding
import Mettapedia.OSLF.Syntax.BindingScopeInterfaceInjectivity

/-!
# The actual contextual solver answers preserve the pattern fragment

Variable binding, rigid imitation, same-hole pruning, and distinct-hole
factoring supply pattern images. Pullback factoring needs the injective
occurrence maps of this fragment. The general factoring operation itself
remains available for arbitrary maps; these preservation laws add no language
restriction. Fresh helper images use the same declared binding fields and
the same existing terms as ordinary application.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatternImages

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPatternFragment

variable {S : Signature} {V Other : Type} {declaration : V → MetaArity S}

theorem renamed_generator_check (identity : V) {Γ : Ctx S}
    (rho : Ren S (declaration identity).1 Γ) :
    check (S := S) (declaration := declaration)
      (rename (S := signature S declaration) rho (generator declaration identity)) =
      RenamingSlots.check (S := signature S declaration) rho := by
  rw [generator, rename, check]
  rw [VariableSpines.complete (S := signature S declaration) _ _ rho (by
    intro sort position
    rw [argsToSub_renameArgs, argsToSub_selfArgs]
    rfl)]

theorem renamed_generator_pattern_iff (identity : V) {Γ : Ctx S}
    (rho : Ren S (declaration identity).1 Γ) :
    Pattern S declaration (rename (S := signature S declaration) rho (generator declaration identity)) ↔
      ∀ sort, Function.Injective (rho sort) := by
  rw [← check_iff, renamed_generator_check, RenamingSlots.check_iff]

theorem tabulate_patterns {Γ : Ctx S} : ∀ (arities : List (MetaArity S))
    (values : (field : MetaArity S) → Var arities field → Term (signature S declaration) (field.1 ++ Γ) field.2),
    (∀ field position, Pattern S declaration (values field position)) →
      PatternArgs S declaration (ArgumentSlots.tabulate (S := signature S declaration) arities values)
  | [], _, _ => .nil
  | field :: rest, values, checked =>
      .cons _ _ (checked field .zero)
        (tabulate_patterns rest (fun other position => values other (.succ position))
          (fun other position => checked other (.succ position)))

theorem variable_binding_images (parameters : Ctx S) {result : S.Srt} (others : Other → MetaArity S)
    (position : Var parameters result) :
    ∀ identity, Pattern S others (ContextualVariableBinding.answer parameters others position identity)
  | .inl () => .object position
  | .inr identity => generator_pattern (S := S) (declaration := others) identity

theorem ordinary_binding_images [DecidableEq V] (identity : V)
    (body : Term (signature S declaration) (declaration identity).1 (declaration identity).2)
    (checked : Pattern S declaration body) :
    ∀ other, Pattern S declaration (ContextualBinding.answer identity body other) := by
  intro other
  by_cases same : other = identity
  · subst other
    rw [ContextualBinding.answer_same]
    exact checked
  · rw [ContextualBinding.answer_other identity other same]
    exact generator_pattern other

theorem imitation_fields (parameters : Ctx S) {result : S.Srt} (operator : S.Op result)
    (others : Other → MetaArity S) :
    PatternArgs S (ContextualImitation.targetDeclarations parameters operator others)
      (ContextualImitation.freshFields parameters operator others) := by
  apply tabulate_patterns
  intro field position
  exact generator_pattern (S := S)
    (declaration := ContextualImitation.targetDeclarations parameters operator others) (.inl ⟨field, position⟩)

theorem imitation_images (parameters : Ctx S) {result : S.Srt} (operator : S.Op result)
    (others : Other → MetaArity S) :
    ∀ identity, Pattern S (ContextualImitation.targetDeclarations parameters operator others)
      (ContextualImitation.answer parameters operator others identity)
  | .inl () => .rigid operator _ (imitation_fields parameters operator others)
  | .inr identity => generator_pattern (S := S)
      (declaration := ContextualImitation.targetDeclarations parameters operator others) (.inr identity)

theorem same_hole_images {parameters context : Ctx S} {left right : Ren S parameters context}
    (equalizer : ScopeEqualizer left right) (result : S.Srt) (others : Other → MetaArity S) :
    ∀ identity, Pattern S (ContextualSelfPair.declarations equalizer.context result others)
      (ContextualSelfPair.answer equalizer result others identity)
  | .inl () => rename_preserves _
      (generator_pattern (S := S) (declaration := ContextualSelfPair.declarations equalizer.context result others) (.inl ()))
      equalizer.inclusion equalizer.inclusion_injective
  | .inr identity => generator_pattern (S := S)
      (declaration := ContextualSelfPair.declarations equalizer.context result others) (.inr identity)

theorem different_hole_images {L R context : Ctx S} {left : Ren S L context} {right : Ren S R context}
    (pullback : ScopePullback left right) (result : S.Srt) (others : Other → MetaArity S)
    (leftInjective : ∀ sort, Function.Injective (left sort))
    (rightInjective : ∀ sort, Function.Injective (right sort)) :
    ∀ identity, Pattern S (ContextualFlexPair.targetDeclarations pullback.context result others)
      (ContextualFlexPair.answer pullback result others identity)
  | .inl false => rename_preserves _
      (generator_pattern (S := S) (declaration := ContextualFlexPair.targetDeclarations pullback.context result others) (.inl ())) pullback.toLeft
      (pullback.toLeft_injective rightInjective)
  | .inl true => rename_preserves _
      (generator_pattern (S := S) (declaration := ContextualFlexPair.targetDeclarations pullback.context result others) (.inl ())) pullback.toRight
      (pullback.toRight_injective leftInjective)
  | .inr identity => generator_pattern (S := S)
      (declaration := ContextualFlexPair.targetDeclarations pullback.context result others) (.inr identity)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatternImages
