import Mettapedia.Logic.LP.IndependentOutputUnification

/-!
# The chosen unifier under a change of variable coordinates

Existence of some renamed solution is weaker than transporting the actual
substitution returned by the ordered solver. A permutation preserves every
decision of the existing Martelli--Montanari algorithm, including elimination
orientation and occurs checks. The transport acts on the full substitution,
so later shared-variable constraints retain their meaning.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.UnificationPermutation

open UnificationRenaming

variable {σ : LPSignature}

abbrev transport (permutation : Equiv.Perm σ.vars) (theta : Subst σ) : Subst σ :=
  IndependentOutputUnification.Coordinates.transport permutation theta

theorem transport_apply (permutation : Equiv.Perm σ.vars) (theta : Subst σ) (term : Term σ) :
    (transport permutation theta).applyTerm (rename permutation term) =
      rename permutation (theta.applyTerm term) :=
  push_apply permutation permutation.symm permutation.symm_apply_apply theta term

theorem transport_id (permutation : Equiv.Perm σ.vars) :
    transport permutation (Subst.id σ) = Subst.id σ :=
  IndependentOutputUnification.Coordinates.transport_id permutation

theorem transport_comp (permutation : Equiv.Perm σ.vars) (after before : Subst σ) :
    transport permutation (after ∘ₛ before) =
      transport permutation after ∘ₛ transport permutation before :=
  IndependentOutputUnification.Coordinates.transport_comp permutation after before

theorem transport_single [DecidableEq σ.vars] (permutation : Equiv.Perm σ.vars)
    (name : σ.vars) (term : Term σ) :
    transport permutation (Subst.single name term) =
      Subst.single (permutation name) (rename permutation term) :=
  IndependentOutputUnification.Coordinates.transport_single permutation name term

theorem occurs_rename [DecidableEq σ.vars] (permutation : Equiv.Perm σ.vars)
    (name : σ.vars) (term : Term σ) :
    (rename permutation term).occursIn (permutation name) = term.occursIn name :=
  IndependentOutputUnification.Coordinates.occurs_rename permutation name term

theorem equations_apply (permutation : Equiv.Perm σ.vars) (theta : Subst σ)
    (eqs : List (Term σ × Term σ)) :
    (transport permutation theta).applyEqs (equations permutation eqs) =
      equations permutation (theta.applyEqs eqs) :=
  IndependentOutputUnification.Coordinates.transport_applyEqs permutation theta eqs

theorem equations_pairs (permutation : Equiv.Perm σ.vars) {arity : Nat}
    (left right : Fin arity → Term σ) :
    finPairsToList (fun i => rename permutation (left i)) (fun i => rename permutation (right i)) =
      equations permutation (finPairsToList left right) :=
  (IndependentOutputUnification.Coordinates.equations_pairs permutation left right).symm

theorem equations_cons (permutation : Equiv.Perm σ.vars)
    (left right : Term σ) (rest : List (Term σ × Term σ)) :
    equations permutation ((left, right) :: rest) =
      (rename permutation left, rename permutation right) :: equations permutation rest := rfl

theorem equations_single [DecidableEq σ.vars] (permutation : Equiv.Perm σ.vars)
    (name : σ.vars) (term : Term σ) (rest : List (Term σ × Term σ)) :
    (Subst.single (permutation name) (rename permutation term)).applyEqs (equations permutation rest) =
      equations permutation ((Subst.single name term).applyEqs rest) :=
  IndependentOutputUnification.Coordinates.elimination_equations permutation name term rest

/-- Reuse the existing exact solver-coordinate theorem; the atom and type
scope adapters below depend on this same solver, not a parallel algorithm. -/
theorem unifyTotal_transport [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (permutation : Equiv.Perm σ.vars)
    (eqs : List (Term σ × Term σ)) :
    unifyTotal (equations permutation eqs) = (unifyTotal eqs).map (transport permutation) :=
  IndependentOutputUnification.Coordinates.total_equivariant permutation eqs

theorem selected_substitution [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (permutation : Equiv.Perm σ.vars)
    (eqs : List (Term σ × Term σ)) (theta : Subst σ)
    (accepted : unifyTotal eqs = some theta) :
    unifyTotal (equations permutation eqs) = some (transport permutation theta) := by
  rw [unifyTotal_transport, accepted]
  rfl

theorem selected_instance [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (permutation : Equiv.Perm σ.vars)
    (eqs : List (Term σ × Term σ)) (theta : Subst σ)
    (accepted : unifyTotal eqs = some theta) (term : Term σ) :
    (unifyTotal (equations permutation eqs)).map (fun found => found.applyTerm (rename permutation term)) =
      some (rename permutation (theta.applyTerm term)) := by
  rw [selected_substitution permutation eqs theta accepted]
  exact congrArg some (transport_apply permutation theta term)

namespace Controls

open UnificationRenaming.Controls (sig distinctProblem)

theorem ordered_elimination_keeps_orientation :
    (unifyTotal (σ := sig) [(.var 0, .var 1)]).map (fun theta => theta 0) = some (.var 1) ∧
    (unifyTotal (σ := sig) [(.var 1, .var 0)]).map (fun theta => theta 1) = some (.var 0) := by
  simp [unifyTotal, Subst.applyEqs, Subst.comp, Subst.single, Subst.id, Subst.applyTerm]

theorem renaming_changes_coordinates_not_shared_constraints :
    unifyTotal (σ := sig) (equations (Equiv.swap 0 1) [(.var 0, .var 1)]) =
      (unifyTotal (σ := sig) [(.var 0, .var 1)]).map (transport (σ := sig) (Equiv.swap 0 1)) :=
  unifyTotal_transport (σ := sig) (Equiv.swap 0 1) _

theorem noninjective_substitution_is_not_coordinate_change :
    (∃ theta, unifyTotal distinctProblem = some theta) ∧
      unifyTotal (equations (σ := sig) (fun _ => 0) distinctProblem) = none :=
  ⟨UnificationRenaming.Controls.distinct_variables_have_solution,
    UnificationRenaming.Controls.forgetting_identity_rejects⟩

end Controls

end Mettapedia.Logic.LP.UnificationPermutation
