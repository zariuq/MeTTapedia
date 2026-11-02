import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveRunNormalization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveProgress

/-!
# The actual selector discharges identical open meta applications

The canonical completed record removes the queue; it is not the worklist's
identity update, which leaves the queue intact. The selector equality below
checks the existing recognition, root-case and located-update operations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveRun

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual ContextualFrameUpdate ContextualSolverCases

variable {S : Signature} {V : Type} [DecidableEq V] {source : V → MetaArity S}

def completed (observations : List (Observation S source)) : Update (diagonals observations) where
  Variables := V
  equality := inferInstance
  declaration := source
  answer := generator source
  remaining := []
  valid := by
    constructor
    · intro Next next candidate _
      exact diagonals_models _ observations
    · intro Next next candidate _
      exact ⟨candidate, (by intro equation member; cases member),
        fun identity => (instantiate_generator candidate identity).symm⟩

def dropFirst (first : Leaf source) (rest : List (Leaf source)) : Update (leafProblem (first :: rest)) where
  Variables := V
  equality := inferInstance
  declaration := source
  answer := generator source
  remaining := leafProblem rest
  valid := by
    constructor
    · intro Next next candidate _
      exact leaf_models _ (first :: rest)
    · intro Next next candidate _
      exact ⟨candidate, leaf_models candidate rest, fun identity => (instantiate_generator candidate identity).symm⟩

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

theorem actual_reflexive_recognition {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort) :
    ContextualSolverSelect.tryEquation (observe term, observe term) = some (.reflexive term) := by
  simp only [ContextualSolverSelect.tryEquation, observe, dif_pos, ContextualSolverSelect.tryTerms,
    ContextualSolverSelect.tryReflexiveTerms, Option.orElse_some]

theorem actual_head_choice (first : Leaf source) (rest : List (Leaf source)) :
    ContextualFrameWorklist.choose (leafProblem (first :: rest)) = some (dropFirst first rest) := by
  change Option.map Choice.perform
    (ContextualSolverSelect.choose ((first.observation, first.observation) :: leafProblem rest)) = _
  simp only [ContextualSolverSelect.choose, Leaf.observation, actual_reflexive_recognition,
    Option.map_some]
  apply congrArg some
  simp only [Choice.perform, RootCase.perform, ContextualReflexive.discharge, Update.keep_left, Update.keep_right,
    List.nil_append, ContextualReflexiveProgress.map_identity]
  rfl

theorem actual_empty_choice : ContextualFrameWorklist.choose ([] : Problem source) = none := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveRun
