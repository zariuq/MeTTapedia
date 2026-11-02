import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveRunTerms

/-!
# A naturality square for two actual reflexive worklist runs

The declaration change may instantiate a hole by a compound term or erase
it entirely. Each side runs with its own computed normalization-leaf bound.
The theorem proves both real returns and then the answer square; it does not
assume an identity update, equal fuel, or a bijection of declaration families.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveRun

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual ContextualFrameUpdate ContextualFrameWorklist

variable {S : Signature} {V W : Type} [DecidableEq V] [DecidableEq W]
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {source : V → MetaArity S} {next : W → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

theorem actual_two_run_answer_square (assignment : Assignment source next)
    (terms : List (Term (signature S source) Γ sort)) :
    run (fuel terms) source (observeProblem (termDiagonals terms)) =
        .residual (completedTerms (termDiagonals terms) terms rfl) ∧
      run (fuel (terms.map (instantiate assignment))) next
          (observeProblem (ContextualFrameUnifier.mapProblem assignment (termDiagonals terms))) =
        .residual (completedTerms (ContextualFrameUnifier.mapProblem assignment (termDiagonals terms))
          (terms.map (instantiate assignment)) (map_termDiagonals assignment terms)) ∧
      Assignment.compose assignment (completedTerms (termDiagonals terms) terms rfl).answer =
        Assignment.compose
          (completedTerms (ContextualFrameUnifier.mapProblem assignment (termDiagonals terms))
            (terms.map (instantiate assignment)) (map_termDiagonals assignment terms)).answer assignment := by
  refine ⟨actual_term_run _ _ rfl, actual_term_run _ _ _, ?_⟩
  change Assignment.compose assignment (generator source) = Assignment.compose (generator next) assignment
  rw [Assignment.compose_identity_right, Assignment.compose_identity_left]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveRun
