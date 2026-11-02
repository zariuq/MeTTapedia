import Mettapedia.OSLF.Syntax.BindingRenamingInverse
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameSelectionControls

/-!
# Scope inversion accepts permutations and refuses undeclared dependence

The executable inverse recovers reordered mixed-sort parameters and lifts
under a binder. Repeated arguments remain legal applications, but cannot have
a left inverse. A compound application also remains available even though it
is outside the variable-spine recognizer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRenamingInverse.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open ContextualFrameSelection.Controls (base before swappedMap repeatedMap compoundArguments)

instance : DecidableEq before.Srt := inferInstanceAs (DecidableEq Bool)

def backward : Ren before [false, true] [true, false] := fun _ position => match position with
  | .zero => .succ .zero
  | .succ .zero => .zero
  | .succ (.succ impossible) => nomatch impossible

theorem backward_forward : ∀ sort (position : Var [true, false] sort),
    backward sort (swappedMap sort position) = position
  | _, .zero => rfl
  | _, .succ .zero => rfl
  | _, .succ (.succ impossible) => nomatch impossible

theorem swapped_injective : ∀ sort, Function.Injective (swappedMap sort) := by
  intro sort first second same
  exact (backward_forward sort first).symm.trans
    ((congrArg (backward sort) same).trans (backward_forward sort second))

def inverse : Strengthener swappedMap := RenamingInverse.strengthener swappedMap swapped_injective

theorem the_inverse_recovers_a_reordered_parameter :
    RenamingInverse.inverse swappedMap false Var.zero = some (Var.succ Var.zero) := rfl

theorem strengthening_uses_the_recovered_formal_position :
    strengthenT inverse (Term.var (S := before) (Γ := [false, true]) (.succ .zero)) =
      some (Term.var (S := before) (Γ := [true, false]) .zero) := rfl

theorem lifting_keeps_the_binders_own_variable :
    strengthenT (inverse.liftS [false]) (Term.var (S := before) (Γ := [false, false, true]) .zero) =
      some (Term.var (S := before) (Γ := [false, true, false]) .zero) := rfl

def inclusion : Ren before [false] [true, false] := fun _ position => match position with
  | .zero => .succ .zero
  | .succ impossible => nomatch impossible

theorem undeclared_ambient_dependence_is_not_recognized :
    RenamingInverse.inverse inclusion true Var.zero = none := rfl

theorem repetition_cannot_be_given_a_false_left_inverse : ¬ Nonempty (Strengthener repeatedMap) := by
  rintro ⟨recovered⟩
  have first := recovered.un_rho false Var.zero
  have second := recovered.un_rho false (Var.succ Var.zero)
  have impossible := first.symm.trans second
  cases impossible

theorem compound_arguments_still_instantiate_an_ordinary_body :
    bind (argsToSub compoundArguments) (Term.var (S := before) (Γ := [false]) .zero) =
      Term.op (S := before) (Γ := []) (.inl (.constant false)) Args.nil := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRenamingInverse.Controls
