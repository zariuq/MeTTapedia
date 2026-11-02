import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameUnifier

/-!
# Adding unused contextual declarations conservatively extends prefix models

The extension adds fresh operators for unused declarations, not equations
from their future events. A source model lifts by the existing capture
transport; inclusion reflects equality without an inverse for off-image
operators or an inhabitant at every sort.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixModels

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {Extra V W : Type}
  (unused : Extra → MetaArity S) (declaration : V → MetaArity S)

abbrev extended := ContextualSelectionViews.source unused declaration

def inclusion : Assignment declaration (extended unused declaration) :=
  ContextualSelectionViews.capturedSource unused declaration

theorem inclusion_meta {Γ : Ctx S} (identity : V)
    (arguments : Args (signature S declaration)
      ((declaration identity).1.map fun sort => ([], sort)) Γ) :
    instantiate (inclusion unused declaration)
        (.op (S := signature S declaration) (.inr (.mk identity)) arguments) =
      .op (S := signature S (extended unused declaration)) (.inr (.mk (Sum.inr identity)))
        (instantiateArgs (inclusion unused declaration) arguments) := by
  simp only [inclusion, ContextualSelectionViews.capturedSource, instantiate, generator,
    Mettapedia.OSLF.Binding.bind]
  exact congrArg
    (Term.op (S := signature S (extended unused declaration)) (.inr (.mk (Sum.inr identity))))
    (bindArgs_selfArgs (T := signature S (extended unused declaration)) (declaration identity).1
      (instantiateArgs (ContextualSelectionViews.capturedSource unused declaration) arguments))

def metaOperator : {sort : S.Srt} → Operator declaration sort → Operator (extended unused declaration) sort
  | _, .mk name => Operator.mk (declaration := extended unused declaration) (Sum.inr name)

theorem metaOperator_key {sort : S.Srt} (operator : Operator declaration sort) :
    (metaOperator unused declaration operator).key = Sum.inr operator.key := by
  cases operator
  rfl

theorem metaOperator_injective {sort : S.Srt} :
    Function.Injective (metaOperator unused declaration (sort := sort)) := by
  intro first second same
  apply Operator.key_injective
  have names := congrArg Operator.key same
  rw [metaOperator_key, metaOperator_key] at names
  exact Sum.inr.inj names

def operator : {sort : S.Srt} → (signature S declaration).Op sort →
    (signature S (extended unused declaration)).Op sort
  | _, .inl original => .inl original
  | _, .inr localName => .inr (metaOperator unused declaration localName)

theorem operator_injective {sort : S.Srt} :
    Function.Injective (operator unused declaration (sort := sort)) := by
  intro first second same
  cases first with
  | inl first =>
      cases second with
      | inl second => exact congrArg Sum.inl (Sum.inl.inj same)
      | inr second => cases same
  | inr first =>
      cases second with
      | inl second => cases same
      | inr second => exact congrArg Sum.inr (metaOperator_injective unused declaration (Sum.inr.inj same))

theorem operator_arity {sort : S.Srt} (head : (signature S declaration).Op sort) :
    (signature S (extended unused declaration)).arity (operator unused declaration head) =
      (signature S declaration).arity head := by
  cases head with
  | inl original => rfl
  | inr localName => cases localName; rfl

theorem inclusion_op {Γ : Ctx S} {sort : S.Srt} (head : (signature S declaration).Op sort)
    (arguments : Args (signature S declaration) ((signature S declaration).arity head) Γ) :
    instantiate (inclusion unused declaration) (.op head arguments) =
      .op (operator unused declaration head)
        (castArgsArity (T := signature S (extended unused declaration)) (operator_arity unused declaration head).symm
          (instantiateArgs (inclusion unused declaration) arguments)) := by
  cases head with
  | inl original => rfl
  | inr localName => cases localName; exact inclusion_meta unused declaration _ _

private theorem castArgs_injective {T : Signature} {first second : List (List T.Srt × T.Srt)}
    (same : first = second) {Γ : Ctx T} :
    Function.Injective (castArgsArity (T := T) (Γ := Γ) same) := by
  cases same
  exact Function.injective_id

mutual
theorem inclusion_injective : ∀ {Γ : Ctx S} {sort : S.Srt}
    (first second : Term (signature S declaration) Γ sort),
    instantiate (inclusion unused declaration) first = instantiate (inclusion unused declaration) second →
      first = second
  | _, _, .var first, .var second, same =>
      congrArg (Term.var (S := signature S declaration))
        (Term.var.inj (S := signature S (extended unused declaration)) same)
  | _, _, .var _, .op _ _, same => by rw [inclusion_op] at same; cases same
  | _, _, .op _ _, .var _, same => by rw [inclusion_op] at same; cases same
  | _, _, .op head arguments, .op other others, same => by
      rw [inclusion_op, inclusion_op] at same
      have names := operator_injective unused declaration (Term.op.inj same).1
      subst other
      exact congrArg (Term.op (S := signature S declaration) head)
        (inclusionArgs_injective arguments others
          (castArgs_injective (T := signature S (extended unused declaration))
            (operator_arity unused declaration head).symm (eq_of_heq (Term.op.inj same).2)))

theorem inclusionArgs_injective : ∀ {Γ : Ctx S} {arities : List (List S.Srt × S.Srt)}
    (first second : Args (signature S declaration) arities Γ),
    instantiateArgs (inclusion unused declaration) first =
      instantiateArgs (inclusion unused declaration) second → first = second
  | _, _, .nil, .nil, _ => rfl
  | _, _, .cons first rest, .cons second tail, same => by
      have components := Args.cons.inj same
      exact congrArg₂ Args.cons
        (inclusion_injective first second components.1)
        (inclusionArgs_injective rest tail components.2)
end

variable {declaration} {next : W → MetaArity S}

theorem models_after_inclusion_iff (candidate : Assignment declaration next)
    {Γ : Ctx S} {sort : S.Srt} (prefixProblem : EquationStore (Term (signature S declaration) Γ sort)) :
    ContextualFrameUnifier.Models (Assignment.compose (inclusion unused next) candidate) prefixProblem ↔
      ContextualFrameUnifier.Models candidate prefixProblem := by
  constructor
  · intro solved equation member
    apply inclusion_injective unused next
    simpa only [Assignment.instantiate_compose] using solved equation member
  · intro solved
    exact ContextualFrameUnifier.models_compose solved (inclusion unused next)

theorem lifted_capture_assignment (candidate : Assignment declaration next) :
    Assignment.compose (ContextualStoredRows.liftCaptures unused candidate) (inclusion unused declaration) =
      Assignment.compose (inclusion unused next) candidate := by
  funext name
  exact instantiate_generator (ContextualStoredRows.liftCaptures unused candidate) (Sum.inr name)

theorem lifted_prefix_models_iff (candidate : Assignment declaration next)
    {Γ : Ctx S} {sort : S.Srt} (prefixProblem : EquationStore (Term (signature S declaration) Γ sort)) :
    ContextualFrameUnifier.Models (ContextualStoredRows.liftCaptures unused candidate)
        (ContextualFrameUnifier.mapProblem (inclusion unused declaration) prefixProblem) ↔
      ContextualFrameUnifier.Models candidate prefixProblem := by
  rw [ContextualFrameUnifier.models_mapProblem, lifted_capture_assignment]
  exact models_after_inclusion_iff unused candidate prefixProblem

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixModels
