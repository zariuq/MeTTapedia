import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual

/-!
# Contextual queue mapping composes on the existing terms

The map instantiates both typed observations in every equation. Composition
uses the common instantiation law, preserves the order of retained portions,
and keeps every equation position, including duplicate-valued constraints.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemMapping

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

variable {S : Signature} {V W Next : Type}
  {source : V → MetaArity S} {target : W → MetaArity S} {next : Next → MetaArity S}

theorem composition (first : Assignment source target) (second : Assignment target next) (problem : Problem source) :
    mapProblem second (mapProblem first problem) = mapProblem (Assignment.compose second first) problem := by
  unfold mapProblem
  rw [List.map_map]
  congr 1
  funext equation
  exact congrArg₂ (fun left right => (left, right))
    (instantiateObservation_comp first second equation.1) (instantiateObservation_comp first second equation.2)

theorem append (assignment : Assignment source target) (first second : Problem source) :
    mapProblem assignment (first ++ second) = mapProblem assignment first ++ mapProblem assignment second :=
  List.map_append

theorem length (assignment : Assignment source target) (problem : Problem source) :
    (mapProblem assignment problem).length = problem.length := by
  simp only [mapProblem, List.length_map]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemMapping
