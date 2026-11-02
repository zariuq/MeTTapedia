import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveRun

/-!
# Homogeneous term stores use the actual reflexive worklist result

Input transport changes only the problem index of the computed update. Its
variable carrier, declarations, answer and residual are explicit data, so
the source endpoint construction sees the real original family directly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveRun

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual ContextualFrameUpdate ContextualFrameWorklist

variable {S : Signature} {V W : Type} {source : V → MetaArity S} {next : W → MetaArity S}
  {Γ : Ctx S} {sort : S.Srt}

def termDiagonals (terms : List (Term (signature S source) Γ sort)) :
    EquationStore (Term (signature S source) Γ sort) := terms.map fun term => (term, term)

theorem observe_termDiagonals (terms : List (Term (signature S source) Γ sort)) :
    observeProblem (termDiagonals terms) = diagonals (terms.map observe) := by
  simp only [observeProblem, termDiagonals, diagonals, List.map_map]
  rfl

theorem map_termDiagonals (assignment : Assignment source next)
    (terms : List (Term (signature S source) Γ sort)) :
    ContextualFrameUnifier.mapProblem assignment (termDiagonals terms) =
      termDiagonals (terms.map (instantiate assignment)) := by
  simp only [ContextualFrameUnifier.mapProblem, termDiagonals, List.map_map]
  rfl

theorem termDiagonals_models (assignment : Assignment source next)
    (terms : List (Term (signature S source) Γ sort)) :
    ContextualFrameUnifier.Models assignment (termDiagonals terms) := by
  intro equation member
  obtain ⟨term, _present, rfl⟩ := List.mem_map.mp member
  rfl

def fuel (terms : List (Term (signature S source) Γ sort)) : Nat :=
  (queueLeaves (terms.map observe)).length + 1

variable [DecidableEq V]

def completedFor (problem : Problem source) (observations : List (Observation S source))
    (same : problem = diagonals observations) : Update problem where
  Variables := V
  equality := inferInstance
  declaration := source
  answer := generator source
  remaining := []
  valid := by rw [same]; exact (completed observations).valid

def completedTerms (problem : EquationStore (Term (signature S source) Γ sort))
    (terms : List (Term (signature S source) Γ sort)) (same : problem = termDiagonals terms) :
    Update (observeProblem problem) := completedFor _ (terms.map observe) (by rw [same, observe_termDiagonals])

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

theorem actual_run_for (problem : Problem source) (observations : List (Observation S source))
    (same : problem = diagonals observations) :
    run ((queueLeaves observations).length + 1) source problem = .residual (completedFor problem observations same) := by
  cases same
  exact actual_run observations

theorem actual_term_run (problem : EquationStore (Term (signature S source) Γ sort))
    (terms : List (Term (signature S source) Γ sort)) (same : problem = termDiagonals terms) :
    run (fuel terms) source (observeProblem problem) = .residual (completedTerms problem terms same) :=
  actual_run_for _ _ _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveRun
