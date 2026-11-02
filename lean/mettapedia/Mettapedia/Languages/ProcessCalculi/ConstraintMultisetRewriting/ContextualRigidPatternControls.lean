import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidPatterns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameImitationControls

/-!
# Normalized fields keep their actual structural-fragment checks

Two flexible field equations and a unary hole under a lambda remain patterns.
A compound application remains an ordinary retained equation outside that
fragment; normalization does not manufacture a successful pattern check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidPatternControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment

abbrev base := ContextualFrameImitationControls.base
abbrev source := ContextualFrameImitationControls.declaration
abbrev extended := signature base source
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def body : Term extended [()] () :=
  ContextualFrameImitationControls.pair (ContextualFrameImitationControls.call (.var .zero))
    ContextualFrameImitationControls.hole
def problem : Problem source := [(observe body, observe body)]
def lambda : Term extended [] () := .op (.inl .lam)
  (.cons (ContextualFrameImitationControls.call (.var .zero)) .nil)
def binderProblem : Problem source := [(observe lambda, observe lambda)]
def compound : Term extended [] () := .op (.inl .lam)
  (.cons (ContextualFrameImitationControls.call ContextualFrameImitationControls.constant) .nil)
def compoundProblem : Problem source := [(observe compound, observe compound)]

theorem both_original_queues_are_patterns : ProblemPattern problem ∧ ProblemPattern binderProblem := by
  constructor <;> apply checkProblem_iff _ |>.mp <;> decide +kernel

theorem the_actual_two_field_queue_passes_the_executable_check :
    (ContextualRigidSolver.normalize problem).map checkProblem = some true := by
  decide +kernel

theorem the_actual_binder_field_passes_the_executable_check :
    (ContextualRigidSolver.normalize binderProblem).map checkProblem = some true := by
  decide +kernel

theorem the_actual_binder_field_keeps_one_local_object_variable :
    ((ContextualRigidSolver.normalize binderProblem).bind fun remaining => remaining[0]?).map
      (fun equation => equation.1.1.length) = some 1 := by
  decide +kernel

theorem all_successful_normalizations_of_the_source_queue_keep_the_fragment
    {remaining : Problem source} (computed : ContextualRigidSolver.normalize problem = some remaining) :
    ProblemPattern remaining :=
  ContextualRigidPatterns.normalization_patterns problem both_original_queues_are_patterns.1 computed

theorem the_compound_field_remains_outside_the_fragment :
    (ContextualRigidSolver.normalize compoundProblem).map checkProblem = some false := by
  decide +kernel

theorem the_compound_field_remains_an_equation_rather_than_a_refutation :
    (ContextualRigidSolver.normalize compoundProblem).map List.length = some 1 := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidPatternControls
