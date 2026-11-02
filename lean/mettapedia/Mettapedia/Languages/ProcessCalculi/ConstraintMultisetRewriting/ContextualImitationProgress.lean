import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitation
import Mettapedia.OSLF.Syntax.BindingArgumentSizes

/-!
# Constructor imitation strictly decreases a finite model potential

The selected image is a constructor with its field images. Imitation replaces
that image by the fields, removing precisely one tree node. Other active
declarations are unchanged; their carrier need not be finite. The model of an
actual selected equation supplies both the residual solution and this strict
decrease. This is a solver progress law, not an assumed global termination
or completeness theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitationProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualImitation
open scoped BigOperators

variable {S : Signature} {Other Variables : Type} {next : Variables → MetaArity S}

def sourcePotential (parameters : Ctx S) (result : S.Srt) (others : Other → MetaArity S)
    (candidate : Assignment (sourceDeclarations parameters result others) next) (active : Finset Other) : Nat :=
  termSize (candidate (.inl ())) + ∑ identity ∈ active, termSize (candidate (.inr identity))

def targetPotential (parameters : Ctx S) {result : S.Srt} (operator : S.Op result) (others : Other → MetaArity S)
    (candidate : Assignment (targetDeclarations parameters operator others) next) (active : Finset Other) : Nat :=
  (∑ slot : ArgumentSlots.Slot (S.arity operator), termSize (candidate (.inl slot))) +
    ∑ identity ∈ active, termSize (candidate (.inr identity))

theorem residual_field_sizes (parameters : Ctx S) {result : S.Srt} (operator : S.Op result)
    (others : Other → MetaArity S) (candidate : Assignment (sourceDeclarations parameters result others) next)
    (fields : Args (signature S next) (S.arity operator) parameters) :
    (∑ slot : ArgumentSlots.Slot (S.arity operator),
      termSize (ContextualImitation.residual parameters operator others candidate fields (.inl slot))) = argsSize fields := by
  change (∑ slot : ArgumentSlots.Slot (S.arity operator),
    termSize (ArgumentSlots.get fields slot.1 slot.2)) = argsSize fields
  convert ArgumentSlots.sum_get fields using 1
  apply Finset.sum_congr
  · ext slot
    simp only [Finset.mem_univ]
  · intro slot _
    rfl

theorem removes_one_model_node (parameters : Ctx S) {result : S.Srt} (operator : S.Op result)
    (others : Other → MetaArity S) (candidate : Assignment (sourceDeclarations parameters result others) next)
    (fields : Args (signature S next) (S.arity operator) parameters)
    (head : candidate (.inl ()) = Term.op (S := signature S next) (.inl operator) fields)
    (active : Finset Other) :
    targetPotential parameters operator others (ContextualImitation.residual parameters operator others candidate fields) active + 1 =
      sourcePotential parameters result others candidate active := by
  unfold targetPotential sourcePotential
  rw [residual_field_sizes, head]
  simp only [ContextualImitation.residual, termSize]
  omega

theorem model_progress (parameters : Ctx S) {result : S.Srt} (operator : S.Op result)
    (others : Other → MetaArity S) {Γ : Ctx S} (rho : Ren S parameters Γ)
    (right : Args (signature S (sourceDeclarations parameters result others)) (S.arity operator) Γ)
    (problem : ContextualResidual.Problem (sourceDeclarations parameters result others))
    (selected :
      (observe (rename (S := signature S (sourceDeclarations parameters result others)) rho
        (generator (sourceDeclarations parameters result others) (.inl ()))),
       observe (Term.op (.inl operator) right)) ∈ problem)
    (candidate : Assignment (sourceDeclarations parameters result others) next)
    (solved : ContextualResidual.Models candidate problem) (active : Finset Other) :
    ∃ remaining : Assignment (targetDeclarations parameters operator others) next,
      ContextualResidual.Models remaining (ContextualResidual.mapProblem (answer parameters operator others) problem) ∧
      (∀ identity, candidate identity = instantiate remaining (answer parameters operator others identity)) ∧
      targetPotential parameters operator others remaining active < sourcePotential parameters result others candidate active := by
  have same := observe_injective (solved _ selected)
  rw [ContextualFamily.instantiate_rename, instantiate_generator] at same
  change rename (S := signature S next) rho (candidate (.inl ())) =
    Term.op (S := signature S next) (.inl operator) (instantiateArgs candidate right) at same
  obtain ⟨fields, head, _⟩ := ArgumentSlots.rename_eq_operator (S := signature S next) rho (candidate (.inl ()))
    (.inl operator) (instantiateArgs candidate right) same
  let remaining := ContextualImitation.residual parameters operator others candidate fields
  have factors := factors_of_head parameters operator others candidate fields head
  refine ⟨remaining,
    (ContextualResidual.models_of_components candidate _ remaining factors problem).mp solved, factors, ?_⟩
  have decrease := removes_one_model_node parameters operator others candidate fields head active
  change targetPotential parameters operator others remaining active + 1 =
    sourcePotential parameters result others candidate active at decrease
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitationProgress
