import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternOccurs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameControls

/-!
# Occurs controls distinguish rigid containment from erasable arguments

`F[] = pair(F[],c)` has no finite contextual solution in any later frame.
In contrast, `F[] = G[F[]]` is solved by taking both images to be constant:
the argument of `G` is erased. That application is valid ordinary syntax and
lies outside the variable-spine pattern fragment. A hole occurrence in its
raw support therefore cannot license a general occurs rejection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternOccurs.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPatternFragment

abbrev base := ContextualFrame.Controls.signature
def declaration : Bool → MetaArity base
  | false => ([], ())
  | true => ([()], ())
abbrev extended := signature base declaration

def hole : Term extended [] () := generator declaration false
def constant {Γ : Ctx base} : Term extended Γ () := .op (.inl .constant) .nil
def rigidArguments : Args extended (base.arity (s := ()) ContextualFrame.Controls.Operator.pair) [] :=
  .cons hole (.cons constant .nil)
def rigid : Term extended [] () := .op (.inl .pair) rigidArguments
def rigidProblem : ContextualResidual.Problem declaration := [(observe hole, observe rigid)]

theorem rigid_fields_are_patterns : PatternArgs base declaration rigidArguments :=
  checkArgs_sound rigidArguments (by rfl)

theorem the_occurrence_is_detected : false ∈ supportArgs rigidArguments := by decide

theorem the_rigid_occurs_equation_has_no_finite_model
    {Variables : Type} (next : Variables → MetaArity base) (candidate : Assignment declaration next) :
    ¬ ContextualResidual.Models candidate rigidProblem := by
  exact selected_occurs_equation_refutes_models candidate false
    (fun _ position => nomatch position) ContextualFrame.Controls.Operator.pair rigidArguments
    rigid_fields_are_patterns the_occurrence_is_detected rigidProblem (List.mem_singleton_self _)

def erasedArgument : Term extended [] () := .op (.inr (.mk true)) (.cons hole .nil)
def erasableProblem : ContextualResidual.Problem declaration := [(observe hole, observe erasedArgument)]
def erase : Assignment declaration declaration
  | false => constant
  | true => constant

theorem raw_support_also_detects_the_erasable_occurrence : false ∈ support erasedArgument := by decide

theorem the_general_application_is_outside_the_pattern_fragment : check erasedArgument = false := rfl

theorem the_general_application_has_an_actual_finite_solution : ContextualResidual.Models erase erasableProblem := by
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem the_selected_image_is_finite_and_has_one_node : termSize (erase false) = 1 := rfl

theorem the_argument_is_really_erased : instantiate erase erasedArgument = constant := rfl

theorem the_erasing_images_themselves_are_patterns : ∀ identity, Pattern base declaration (erase identity)
  | false => Pattern.rigid (S := base) (declaration := declaration) .constant .nil .nil
  | true => Pattern.rigid (S := base) (declaration := declaration) .constant .nil .nil

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternOccurs.Controls
