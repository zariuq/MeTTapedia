import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualObservationAction

/-!
# Rigid decomposition retains every typed child equation

The equation carrier keeps each child's binder-extended context and result
sort. Decomposing a common rigid operator preserves exactly the solution set,
including in an existing equation store. Distinct rigid heads are inconsistent
in this structural-equality profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDecomposition

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V : Type} {declaration : V → MetaArity S}

def argumentEquations : {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    Args (signature S declaration) arities Γ → Args (signature S declaration) arities Γ →
      EquationStore (Observation S declaration)
  | _, _, .nil, .nil => []
  | _, _, .cons first rest, .cons second remaining =>
      (observe first, observe second) :: argumentEquations rest remaining

theorem models_arguments (assignment : Assignment declaration declaration) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (first second : Args (signature S declaration) arities Γ),
      (ContextualObservationAction.action declaration).Models assignment (argumentEquations first second) ↔
        instantiateArgs assignment first = instantiateArgs assignment second
  | _, _, .nil, .nil => by simp [argumentEquations, instantiateArgs]
  | _, _, .cons first rest, .cons second remaining => by
      constructor
      · intro solved
        have head := solved (observe first, observe second) List.mem_cons_self
        have heads := (ContextualObservationAction.solves_observed_iff declaration assignment first second).mp head
        have tails := (models_arguments assignment rest remaining).mp
          (fun equation member => solved equation (List.mem_cons_of_mem _ member))
        exact congrArg₂ Args.cons heads tails
      · intro same equation member
        have fields := Args.cons.inj same
        rcases List.mem_cons.mp member with rfl | member
        · exact (ContextualObservationAction.solves_observed_iff declaration assignment first second).mpr fields.1
        · exact (models_arguments assignment rest remaining).mpr fields.2 equation member

theorem rigid_node_iff (assignment : Assignment declaration declaration)
    {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    (first second : Args (signature S declaration) (S.arity operator) Γ) :
    (ContextualObservationAction.action declaration).Models assignment
        [(observe (Term.op (.inl operator) first), observe (Term.op (.inl operator) second))] ↔
      (ContextualObservationAction.action declaration).Models assignment (argumentEquations first second) := by
  constructor
  · intro solved
    have parent := solved _ (List.mem_singleton_self _)
    have nodes := (ContextualObservationAction.solves_observed_iff declaration assignment _ _).mp parent
    apply (models_arguments assignment first second).mpr
    exact eq_of_heq (Term.op.inj nodes).2
  · intro solved equation member
    have same := List.mem_singleton.mp member
    subst equation
    apply (ContextualObservationAction.solves_observed_iff declaration assignment _ _).mpr
    exact congrArg (Term.op (S := signature S declaration) (.inl operator))
      ((models_arguments assignment first second).mp solved)

/-- Existing equations are retained; the transformation preserves all
models, rather than only the existence of one successful answer. -/
theorem rigid_node_store_equivalent
    {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    (first second : Args (signature S declaration) (S.arity operator) Γ)
    (before : EquationStore (Observation S declaration)) :
    (ContextualObservationAction.action declaration).Equivalent
      (before ++ [(observe (Term.op (.inl operator) first), observe (Term.op (.inl operator) second))])
      (before ++ argumentEquations first second) := by
  intro assignment
  rw [SubstitutionAction.models_append, SubstitutionAction.models_append,
    rigid_node_iff assignment operator first second]

theorem rigid_clash {Γ : Ctx S} {sort : S.Srt} (first second : S.Op sort)
    (different : first ≠ second)
    (leftArgs : Args (signature S declaration) (S.arity first) Γ)
    (rightArgs : Args (signature S declaration) (S.arity second) Γ) :
    ¬ (ContextualObservationAction.action declaration).Consistent
      [(observe (Term.op (.inl first) leftArgs), observe (Term.op (.inl second) rightArgs))] := by
  rintro ⟨assignment, solved⟩
  have parent := solved _ (List.mem_singleton_self _)
  have nodes := (ContextualObservationAction.solves_observed_iff declaration assignment _ _).mp parent
  exact different (Sum.inl.inj (Term.op.inj nodes).1)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDecomposition
