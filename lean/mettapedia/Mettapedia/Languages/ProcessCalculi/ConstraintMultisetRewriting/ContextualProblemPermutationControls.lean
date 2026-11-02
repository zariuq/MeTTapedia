import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemPermutation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemMapping
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverSelect
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingWorklistControls

/-!
# Queue observations preserve duplicates without identifying search choices

Moving a later equation to the front preserves models and finite measures.
The first selected binding changes, so that observation does not identify
solver schedules. Instantiation composes while retaining all three equation
positions. Changing an equation is a separate operation and can lose a model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemPermutationControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport
open ContextualEquationWeight
open ContextualSolverCases

abbrev base := ContextualBindingWorklist.Controls.base
abbrev source := ContextualBindingWorklist.Controls.declaration
abbrev extended := signature base source
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def openEquation : Equation (Observation base source) :=
  (observe (generator source false), observe (Term.var (S := extended) (Γ := [(), ()]) .zero))
def closedEquation : Equation (Observation base source) :=
  (observe (generator source true), observe (ContextualBindingWorklist.Controls.constant (Γ := [])))
def original : Problem source := [openEquation, closedEquation, openEquation]
def rotated : Problem source := [closedEquation, openEquation, openEquation]
def candidate : Assignment source source
  | false => .var .zero
  | true => ContextualBindingWorklist.Controls.constant

theorem the_actual_later_equation_moves_with_a_permutation : original.Perm rotated :=
  ContextualProblemPermutation.selected_to_head closedEquation [openEquation] [openEquation]

theorem the_original_queue_has_an_independent_model : Models candidate original := by
  intro equation member
  simp only [original, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem rotation_preserves_that_model : Models candidate rotated :=
  (ContextualProblemPermutation.models_permutation candidate the_actual_later_equation_moves_with_a_permutation).mp
    the_original_queue_has_an_independent_model

theorem duplicate_constraints_still_occupy_three_positions_and_weigh_ten :
    original.length = 3 ∧ rotated.length = 3 ∧ weight original = 10 ∧ weight rotated = 10 := by
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> decide +kernel

def bindingName {equation : Equation (Observation base source)} : RootCase base source equation → Option Bool
  | .binding recovered => some recovered.chosen
  | .reflexive _ | .imitation _ _ _ _ | .selfPair _ _ _ _ | .flexPair _ _ _ _ _ _ | .reverse _ => none

theorem the_original_first_choice_binds_the_open_declaration :
    (ContextualSolverSelect.choose original).bind (fun choice => bindingName choice.selected) = some false := by
  decide +kernel

theorem the_rotated_first_choice_binds_the_closed_declaration :
    (ContextualSolverSelect.choose rotated).bind (fun choice => bindingName choice.selected) = some true := by
  decide +kernel

def firstBinding : Assignment source source := ContextualBinding.answer false (.var .zero)
def secondBinding : Assignment source source := ContextualBinding.answer true ContextualBindingWorklist.Controls.constant

theorem actual_mapping_composes_on_the_three_equations :
    mapProblem secondBinding (mapProblem firstBinding original) =
      mapProblem (Assignment.compose secondBinding firstBinding) original :=
  ContextualProblemMapping.composition firstBinding secondBinding original

theorem mapping_retains_three_duplicate_valued_positions :
    (mapProblem secondBinding (mapProblem firstBinding original)).length = 3 := by
  rw [ContextualProblemMapping.length, ContextualProblemMapping.length]
  rfl

def altered : Problem source :=
  [(observe (generator source false), observe (Term.var (S := extended) (Γ := [(), ()]) (.succ .zero)))]

theorem changing_the_formal_parameter_loses_the_old_model : ¬ Models candidate altered := by
  intro solved
  have impossible := solved _ List.mem_cons_self
  change observe (Term.var (S := extended) (Γ := [(), ()]) Var.zero) =
    observe (Term.var (S := extended) (Γ := [(), ()]) (.succ .zero)) at impossible
  have different := observe_injective impossible
  cases different

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemPermutationControls
