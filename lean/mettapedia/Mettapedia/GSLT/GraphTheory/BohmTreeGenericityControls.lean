import Mettapedia.GSLT.GraphTheory.BohmTreeGenericity
import Mettapedia.GSLT.GraphTheory.SolvabilityControls

/-! Positive and negative controls for exact Böhm observations under
replacement of subterms. -/

namespace Mettapedia.GSLT.GraphTheory.BohmTreeGenericityControls

open Mettapedia.GSLT.GraphTheory
open Mettapedia.GSLT.GraphTheory.SolvabilityControls

private theorem tree_variable_applied (argument : LambdaTerm) :
    BohmObservation.tree 2 (.app (.var 0) argument) =
      .node 0 0 [BohmObservation.tree 1 argument] :=
  BohmObservation.tree_node_of_reaches (term := .app (.var 0) argument)
    (hnf := .app (.var 0) argument) (arguments := [argument]) Relation.ReflTransGen.refl rfl 1

/-- `x Ω` and `x (λy. Ω)` have the same exact observations: one unsolvable
argument is exchanged for another. -/
theorem exchange_of_unsolvable_arguments :
    BohmObservation.Equivalent (.app (.var 0) LambdaTerm.Omega)
      (.app (.var 0) (.lam LambdaTerm.Omega)) :=
  LambdaContext.equivalent_plug_of_unsolvable (.appRight (.var 0) .hole) Omega_unsolvable
    lam_Omega_unsolvable

/-- Filling can add information strictly: `x Ω` is observed as `x ⊥`, and
`x I` as `x (λy. y)`. -/
theorem filling_adds_information :
    BohmObservation.tree 2 (.app (.var 0) LambdaTerm.Omega) = .node 0 0 [.bot] ∧
      BohmObservation.tree 2 (.app (.var 0) LambdaTerm.I) = .node 0 0 [.node 1 0 []] := by
  constructor
  · rw [tree_variable_applied, Omega_mathematical_observation]
  · rw [tree_variable_applied, identity_mathematical_observation 0]

/-- The replaced subterm must be unsolvable: replacing the solvable argument
`I` of `x I` by `K` gives an observation that is not above the original. -/
theorem replacing_solvable_is_not_monotone :
    ¬BohmTree.InformationLE (BohmObservation.tree 2 (.app (.var 0) LambdaTerm.I))
      (BohmObservation.tree 2 (.app (.var 0) LambdaTerm.K)) := by
  have constant : BohmObservation.tree 1 LambdaTerm.K = .node 2 1 [] :=
    BohmObservation.tree_node_of_reaches (term := LambdaTerm.K) (hnf := LambdaTerm.K)
      (arguments := []) Relation.ReflTransGen.refl rfl 0
  rw [tree_variable_applied, tree_variable_applied, identity_mathematical_observation 0, constant]
  intro below
  cases below with
  | node children =>
      cases children with
      | cons head _ => cases head

/-- `H` equates `x Ω` with `x (λy. Ω)`, so these terms have the same exact
observations also by `BohmObservation.equivalent_of_unsolvableTheory`. -/
theorem unsolvableTheory_instance :
    BohmObservation.Equivalent (.app (.var 0) LambdaTerm.Omega)
      (.app (.var 0) (.lam LambdaTerm.Omega)) :=
  BohmObservation.equivalent_of_unsolvableTheory
    (unsolvableTheory.congAppRight
      (unsolvableTheory_equatesUnsolvables _ _ Omega_unsolvable lam_Omega_unsolvable))

end Mettapedia.GSLT.GraphTheory.BohmTreeGenericityControls
