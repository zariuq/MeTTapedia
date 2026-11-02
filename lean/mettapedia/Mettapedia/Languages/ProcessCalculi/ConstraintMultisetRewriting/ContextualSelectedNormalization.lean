import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklist
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScopeSupport
import Mettapedia.OSLF.Syntax.ContextualRigidTerms

/-!
# Actual normalization of rigid reflexive selected-row equations

Terms from the original binding signature have no contextual holes, although
they may contain object binders. Their repeated equations are retained in
the semantic store and discharged by the actual rigid worklist at fuel one.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedNormalization

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W : Type} (declaration : V → MetaArity S)

mutual
theorem included_support : ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort),
    support (Rigid.includeTerm declaration term) = []
  | _, _, .var _ => rfl
  | _, _, .op _ arguments => included_args_support arguments

theorem included_args_support : ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (arguments : Args S arities Γ), supportArgs (Rigid.includeArgs declaration arguments) = []
  | _, _, .nil => rfl
  | _, _, .cons head rest => by
      simp only [Rigid.includeArgs, supportArgs, included_support head, included_args_support rest, List.nil_append]
end

theorem included_covered (scopes : V → Finset Nat) (occupied : Finset Nat)
    {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) :
    ContextualScopeSupport.Covered scopes occupied (Rigid.includeTerm declaration term) := by
  unfold ContextualScopeSupport.Covered ContextualScopeSupport.term
  rw [included_support]
  exact Finset.empty_subset _

variable [∀ result, DecidableEq (S.Op result)]

mutual
theorem rigid_reflexive : ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort),
    ContextualRigidSolver.terms (Rigid.includeTerm declaration term) (Rigid.includeTerm declaration term) = some []
  | _, _, .var _ => by simp [Rigid.includeTerm, ContextualRigidSolver.terms]
  | _, _, .op _ arguments => by
      simp only [Rigid.includeTerm, ContextualRigidSolver.terms, dite_true]
      exact rigid_args_reflexive arguments

theorem rigid_args_reflexive : ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (arguments : Args S arities Γ),
    ContextualRigidSolver.arguments (Rigid.includeArgs declaration arguments) (Rigid.includeArgs declaration arguments) = some []
  | _, _, .nil => by simp only [Rigid.includeArgs, ContextualRigidSolver.arguments]
  | _, _, .cons head rest => by
      simp only [Rigid.includeArgs, ContextualRigidSolver.arguments, rigid_reflexive head,
        rigid_args_reflexive rest]
      rfl
end

variable {Γ : Ctx S} {sort : S.Srt}

def diagonals (terms : List (Term S Γ sort)) : EquationStore (Term (signature S declaration) Γ sort) :=
  terms.map fun term => (Rigid.includeTerm declaration term, Rigid.includeTerm declaration term)

omit [∀ result, DecidableEq (S.Op result)] in
theorem models_diagonals {next : W → MetaArity S} (candidate : Assignment declaration next)
    (terms : List (Term S Γ sort)) : ContextualFrameUnifier.Models candidate (diagonals declaration terms) := by
  intro equation member
  obtain ⟨term, _present, rfl⟩ := List.mem_map.mp member
  rfl

omit [∀ result, DecidableEq (S.Op result)] in
theorem map_diagonals {next : W → MetaArity S} (candidate : Assignment declaration next)
    (terms : List (Term S Γ sort)) :
    ContextualFrameUnifier.mapProblem candidate (diagonals declaration terms) = diagonals next terms := by
  simp only [ContextualFrameUnifier.mapProblem, diagonals, List.map_map]
  apply List.map_congr_left
  intro term _member
  exact congrArg₂ Prod.mk (Rigid.instantiate_include candidate term) (Rigid.instantiate_include candidate term)

variable [DecidableEq S.Srt]

theorem normalize_diagonals (terms : List (Term S Γ sort)) :
    ContextualRigidSolver.normalize (ContextualResidual.observeProblem (diagonals declaration terms)) = some [] := by
  induction terms with
  | nil => rfl
  | cons term rest earlier =>
      change ContextualRigidSolver.merge
        (ContextualRigidSolver.equation (observe (Rigid.includeTerm declaration term), observe (Rigid.includeTerm declaration term)))
        (ContextualRigidSolver.normalize (ContextualResidual.observeProblem (diagonals declaration rest))) = _
      have equation : ContextualRigidSolver.equation
          (observe (Rigid.includeTerm declaration term), observe (Rigid.includeTerm declaration term)) = some [] := by
        simpa only [ContextualRigidSolver.equation, observe, dif_pos] using rigid_reflexive declaration term
      rw [equation, earlier]
      rfl

variable [DecidableEq V]

theorem actual_one_fuel_return (terms : List (Term S Γ sort)) :
    ContextualFrameWorklist.run 1 declaration
        (ContextualResidual.observeProblem (diagonals declaration terms)) =
      .residual (ContextualFrameWorklist.normalizationUpdate (normalize_diagonals declaration terms)) := by
  have model := (ContextualResidual.models_observeProblem _ _).mpr
    (models_diagonals declaration (generator declaration) terms)
  rw [ContextualFrameWorklist.run_eq_local_on_model 1 _ declaration (generator declaration) model]
  rw [ContextualFrameWorklist.runWithRefuter_normalized _ 0 _ [] (normalize_diagonals declaration terms) (by rfl)]
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedNormalization
