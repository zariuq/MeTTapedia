import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationStore
import Mettapedia.Logic.LP.TotalUnification

/-!
# The existing first-order unifier as an equation-store solver

This is a profile over the existing LP term type, not a term language for the
calculus. Its total occurs-checked solver is sound, complete and principal.
Other term theories may have several principal branches or residual problems;
the equation-store interface does not impose this profile on them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder

open Mettapedia.Logic.LP

variable (signature : LPSignature)

def action : SubstitutionAction (Term signature) (Subst signature) where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply := Subst.applyTerm
  identity := Subst.id signature
  compose := Subst.comp
  apply_identity := Subst.applyTerm_id
  apply_compose := Subst.applyTerm_comp
  preserves := fun σ {_ _} same => congrArg σ.applyTerm same

variable {signature}

theorem models_iff (σ : Subst signature) (store : EquationStore (Term signature)) :
    (action signature).Models σ store ↔ Unifies σ store := Iff.rfl

/-- Every finite ground target is fixed by substitution. -/
theorem ground_fixed (σ : Subst signature) (term : Term signature)
    (ground : term.isGround) : σ.applyTerm term = term := by
  induction term with
  | var _ => exact ground.elim
  | const _ => rfl
  | app _ children ih =>
    simp only [Subst.applyTerm]
    congr 1
    funext i
    exact ih i (ground i)

theorem factors_on_terms {answer candidate : Subst signature}
    (general : answer.moreGeneral candidate) :
    ∃ residual : Subst signature, ∀ term,
      candidate.applyTerm term = (residual.comp answer).applyTerm term := by
  obtain ⟨residual, factors⟩ := general
  have same : candidate = residual.comp answer := funext factors
  exact ⟨residual, fun term => congrArg (fun σ : Subst signature => σ.applyTerm term) same⟩

variable [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols]

theorem accepted_principal (store : EquationStore (Term signature))
    (answer : Subst signature) (accepted : unifyTotal store = some answer) :
    (action signature).Principal store answer := by
  refine ⟨unifyTotal_sound store answer accepted, ?_⟩
  intro candidate solves
  exact factors_on_terms (unifyTotal_mgu store answer accepted candidate solves)

theorem accepted_iff_consistent (store : EquationStore (Term signature)) :
    (∃ answer, unifyTotal store = some answer) ↔ (action signature).Consistent store := by
  constructor
  · rintro ⟨answer, accepted⟩
    exact ⟨answer, unifyTotal_sound store answer accepted⟩
  · exact unifyTotal_complete

theorem refused_iff_inconsistent (store : EquationStore (Term signature)) :
    unifyTotal store = none ↔ ¬ (action signature).Consistent store :=
  unifyTotal_none_iff_not_unifiable store

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder
