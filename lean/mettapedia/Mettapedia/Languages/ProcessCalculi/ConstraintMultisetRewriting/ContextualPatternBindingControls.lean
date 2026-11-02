import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternBinding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingControls

/-!
# Contextual pattern-binding controls

Swapped distinct parameters have a principal answer. A repeated-variable
spine has no inverse, while ordinary application still permits it. An
undeclared object-variable dependency is rejected. In contrast, inability to
recover a symbolic right side must not reject a solvable flex-flex equation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternBinding.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualBinding.Controls

def swap : Ren base [(), ()] [(), ()]
  | _, .zero => .succ .zero
  | _, .succ .zero => .zero
  | _, .succ (.succ impossible) => nomatch impossible

theorem swap_involution : ∀ sort (position : Var [(), ()] sort),
    swap sort (swap sort position) = position
  | _, .zero => rfl
  | _, .succ .zero => rfl
  | _, .succ (.succ impossible) => nomatch impossible

def inverseSwap : Strengthener (S := extended) swap where
  un := fun sort position => some (swap sort position)
  un_rho := fun sort position => congrArg some (swap_involution sort position)
  rho_un := by
    intro sort position original found
    have same := Option.some.inj found
    rw [← same]
    exact swap_involution sort position

theorem swapped_parameters_compute_the_principal_answer :
    solve? fId swap inverseSwap (rename (S := extended) swap body) =
      some (ContextualBinding.answer fId body) := rfl

theorem swapped_parameters_have_a_principal_solution :
    (ContextualFamilies.action declaration [(), ()] ()).Principal
      [(rename (S := extended) swap (generator declaration fId), rename (S := extended) swap body)]
      (ContextualBinding.answer fId body) :=
  solve_principal (S := base) (declaration := declaration)
    fId swap inverseSwap _ swapped_parameters_compute_the_principal_answer

def repeated : Ren base [(), ()] [()]
  | _, .zero => .zero
  | _, .succ .zero => .zero
  | _, .succ (.succ impossible) => nomatch impossible

theorem repeated_parameters_have_no_inverse : ¬ Nonempty (Strengthener (S := extended) repeated) := by
  rintro ⟨inverse⟩
  have first := inverse.un_rho () (Var.zero : Var [(), ()] ())
  have second := inverse.un_rho () (Var.succ .zero : Var [(), ()] ())
  have same := first.symm.trans second
  have positions := Option.some.inj same
  cases positions

def emptySpine : Ren base [] [()] := fun _ position => nomatch position

def inverseEmpty : Strengthener (S := extended) emptySpine where
  un := fun _ _ => none
  un_rho := fun _ position => nomatch position
  rho_un := by intro sort position original impossible; cases impossible

theorem undeclared_object_dependency_is_not_recovered :
    solve? (S := base) (declaration := declaration) nullaryId emptySpine inverseEmpty
      (Term.var (S := extended) (Γ := [()]) .zero) = none := rfl

def unaryId : Nat × Nat := (1, 0)

def flexibleRight : Term extended [()] () :=
  .op (.inr (.mk unaryId)) (.cons (.var .zero) .nil)

theorem symbolic_right_side_is_not_structurally_recovered :
    solve? nullaryId emptySpine inverseEmpty flexibleRight = none := rfl

def allConstant : Assignment declaration declaration := fun _ => .op (.inl .constant) .nil

/-- Both sides can become a constant. Treating structural recovery failure
as global unification failure would remove this valid answer. -/
theorem unrecovered_flex_flex_equation_is_still_consistent :
    (ContextualFamilies.action declaration [()] ()).Consistent
      [(rename (S := extended) emptySpine (generator declaration nullaryId), flexibleRight)] := by
  refine ⟨allConstant, ?_⟩
  intro equation member
  have same := List.mem_singleton.mp member
  subst equation
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternBinding.Controls
