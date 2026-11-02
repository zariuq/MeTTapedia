import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemPermutation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverMeasure

/-!
# Reversing one equation preserves constraint truth and the solver measures

The declaration frame, context tags and both sides remain present. Symmetry
of the equality constraint preserves every model; active support and tree
weight agree. These are the observations used to justify a reversed solver
case at its original queue position.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemOrientation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport
open ContextualEquationWeight
open ContextualPatternFragment

variable {S : Signature} {V Next : Type} {source : V → MetaArity S} {next : Next → MetaArity S}

def flip (equation : Equation (Observation S source)) : Equation (Observation S source) := (equation.2, equation.1)

theorem models_cons (candidate : Assignment source next) (equation : Equation (Observation S source)) (rest : Problem source) :
    Models candidate (equation :: rest) ↔ Models candidate (flip equation :: rest) := by
  simp only [Models, List.forall_mem_cons, flip]
  exact and_congr eq_comm Iff.rfl

theorem models_at (candidate : Assignment source next) (equation : Equation (Observation S source)) (before after : Problem source) :
    Models candidate (before ++ equation :: after) ↔ Models candidate (before ++ flip equation :: after) := by
  rw [models_append, models_append]
  exact and_congr Iff.rfl (models_cons candidate equation after)

theorem active_at [DecidableEq V] (equation : Equation (Observation S source)) (before after : Problem source) :
    active (before ++ equation :: after) = active (before ++ flip equation :: after) := by
  simp only [active, List.flatMap_append, List.flatMap_cons, List.toFinset_append, flip]
  ac_rfl

theorem weight_at (equation : Equation (Observation S source)) (before after : Problem source) :
    weight (before ++ equation :: after) = weight (before ++ flip equation :: after) := by
  rw [weight_append, weight_append, weight_cons, weight_cons]
  dsimp only [equationSize, flip]
  omega

theorem measure_at [DecidableEq V] (candidate : Assignment source next)
    (equation : Equation (Observation S source)) (before after : Problem source) :
    ContextualSolverMeasure.measure candidate (before ++ equation :: after) =
      ContextualSolverMeasure.measure candidate (before ++ flip equation :: after) := by
  dsimp only [ContextualSolverMeasure.measure]
  rw [active_at equation before after, weight_at equation before after]

theorem patterns_cons (equation : Equation (Observation S source)) (rest : Problem source) :
    ProblemPattern (equation :: rest) ↔ ProblemPattern (flip equation :: rest) := by
  simp only [ProblemPattern, List.forall_mem_cons, flip]
  exact and_congr and_comm Iff.rfl

theorem patterns_at (equation : Equation (Observation S source)) (before after : Problem source) :
    ProblemPattern (before ++ equation :: after) ↔ ProblemPattern (before ++ flip equation :: after) := by
  simp only [ProblemPattern, List.forall_mem_append]
  exact and_congr Iff.rfl (patterns_cons equation after)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemOrientation
