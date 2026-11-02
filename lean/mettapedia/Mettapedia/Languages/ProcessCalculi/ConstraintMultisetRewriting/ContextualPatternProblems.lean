import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternPreservation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual

/-!
# Structural patterns on heterogeneous contextual equation queues

Both existing terms in each equation belong to the declared structural
fragment. Instantiating with pattern images preserves this property across
declaration families, object contexts and result sorts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternFragment

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

variable {S : Signature} {V Next : Type} {source : V → MetaArity S} {next : Next → MetaArity S}

def ProblemPattern (problem : Problem source) : Prop :=
  ∀ equation ∈ problem, Pattern S source equation.1.2.2 ∧ Pattern S source equation.2.2.2

def checkProblem (problem : Problem source) : Bool :=
  problem.all fun equation => check equation.1.2.2 && check equation.2.2.2

theorem checkProblem_iff (problem : Problem source) : checkProblem problem = true ↔ ProblemPattern problem := by
  simp only [checkProblem, List.all_eq_true, Bool.and_eq_true, ProblemPattern, check_iff]

theorem map_patterns (assignment : Assignment source next)
    (images : ∀ identity, Pattern S next (assignment identity)) (problem : Problem source)
    (patterned : ProblemPattern problem) : ProblemPattern (mapProblem assignment problem) := by
  intro equation member
  obtain ⟨original, selected, rfl⟩ := List.mem_map.mp member
  rcases original with ⟨⟨Γ, sort, left⟩, ⟨Δ, result, right⟩⟩
  exact ⟨instantiate_preserves assignment images left (patterned _ selected).1,
    instantiate_preserves assignment images right (patterned _ selected).2⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternFragment
