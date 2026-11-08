import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalChecks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalInterfaceControls

/-!
# A concrete answer cannot discharge a forgotten check

The equality example succeeds after one proposed binding but is not entailed
by the original empty equation store. The count example has a closed check
argument and a variable occurrence value; retaining the argument alone still
loses the obligation. These are negative controls for interface inference.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalChecks.Controls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls (signature A zero one)

def label (_ : Nat) : Term signature := .var 0
def equality : Check (Term signature) := .equal (.var 0) (.const 0)
def countOne : Check (Term signature) := .count (.const 0) 1

theorem concrete_success_is_not_a_universal_guard :
    (∀ residual, equality.Holds A (A.compose residual zero) label ∅) ∧
      ¬ A.Entails [] (fun assignment => equality.Holds A assignment label ∅) := by
  constructor
  · intro residual
    rfl
  · intro universal
    have impossible := universal one (A.models_nil one)
    change (Term.const (σ := signature) 1) = .const 0 at impossible
    cases impossible

theorem a_closed_pattern_alone_has_a_principal_interface :
    A.PrincipalOn [] zero [Term.const 0] := by
  refine ⟨A.models_nil zero, ?_⟩
  intro candidate _
  refine ⟨A.identity, ?_⟩
  intro term member
  have same := List.mem_singleton.mp member
  subst term
  rfl

/-- Every residual of this answer gives one matching occurrence, but a
different original solution gives zero. The world value must be retained. -/
theorem closed_check_pattern_does_not_cover_the_occurrence_world :
    (∀ residual, countOne.Holds A (A.compose residual zero) label {0}) ∧
      ¬ A.Entails [] (fun assignment => countOne.Holds A assignment label {0}) := by
  constructor
  · intro residual
    simp [countOne, Check.Holds, Check.matches, FirstOrder.action,
      Subst.comp, Subst.applyTerm, zero, Subst.single, label]
  · intro universal
    have impossible := universal one (A.models_nil one)
    simp [countOne, Check.Holds, Check.matches, FirstOrder.action,
      Subst.applyTerm, one, Subst.single, label] at impossible

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalChecks.Controls
