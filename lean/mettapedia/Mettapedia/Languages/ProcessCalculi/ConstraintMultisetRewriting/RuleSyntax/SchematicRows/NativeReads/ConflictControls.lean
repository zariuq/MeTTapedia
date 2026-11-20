import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.ConflictCores
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.IndexControls

/-! # Strong inconsistent cores are not failed universal guards -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.ConflictControls

open Mettapedia.Logic.LP
open RuleSyntax.Controls (atoms)

abbrev X := OneFrame.frames (FirstOrder.action atoms)
def five : Term atoms := .const 5
def six : Term atoms := .const 6
def core : EquationStore (Term atoms) := [(.var 0, five), (.var 0, six)]
def split : EquationStore (Term atoms) := [(.var 0, five), (.var 1, six)]

theorem whole_core_is_refuted : ConflictCores.Refutes X (a := PUnit.unit) core :=
  ConflictCores.total_unifier_supplies_core core (by cbv)

theorem one_opening_preserves_refutation (opening : Subst atoms) :
    ConflictCores.Refutes X (a := PUnit.unit) (X.applyStore (a := PUnit.unit) (b := PUnit.unit) opening core) :=
  ConflictCores.refutes_instantiation X (a := PUnit.unit) core whole_core_is_refuted opening

theorem independent_openings_destroy_the_core : X.Solvable (a := PUnit.unit) split := by
  let point : Subst atoms := fun name => if name = 0 then five else six
  refine ⟨PUnit.unit, point, ?_⟩
  intro equation member
  simp only [split, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem failed_universal_guard_is_not_refutation :
    FirstOrderLicence.check (Subst.id atoms) (fun _ : Nat => .var 0) ∅ (.equal (.var 0) five) = false ∧
      X.Solvable (a := PUnit.unit) ([] : EquationStore (Term atoms)) ∧
      (QuantifierControls.point 5).applyTerm (.var 0) = five := by
  refine ⟨by simp [FirstOrderLicence.check, five, Subst.id, Subst.applyTerm],
    ⟨PUnit.unit, Subst.id atoms, ?_⟩, rfl⟩
  intro equation impossible
  cases impossible

#print axioms whole_core_is_refuted
#print axioms one_opening_preserves_refutation
#print axioms independent_openings_destroy_the_core
#print axioms failed_universal_guard_is_not_refutation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.ConflictControls
