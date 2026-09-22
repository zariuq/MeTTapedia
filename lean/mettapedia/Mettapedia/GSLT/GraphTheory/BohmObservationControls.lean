import Mettapedia.GSLT.GraphTheory.BohmObservations

/-! Positive and negative controls for uncapped mathematical observations. -/

namespace Mettapedia.GSLT.GraphTheory

open Mettapedia.GSLT.Core

theorem identity_mathematical_observation (depth : Nat) :
    BohmObservation.tree (depth + 1) LambdaTerm.I = .node 1 0 [] := by
  apply (BohmObservation.tree_eq_iff _ _ _).mpr
  exact .node Relation.ReflTransGen.refl rfl List.Forall₂.nil

theorem variable_mathematical_observation (depth index : Nat) :
    BohmObservation.tree (depth + 1) (.var index) = .node 0 index [] := by
  apply (BohmObservation.tree_eq_iff _ _ _).mpr
  exact .node Relation.ReflTransGen.refl rfl List.Forall₂.nil

/-- Finite-depth mathematical trees retain different actual head shapes. -/
theorem identity_and_variable_observations_differ (depth : Nat) :
    BohmObservation.tree (depth + 1) LambdaTerm.I ≠
      BohmObservation.tree (depth + 1) (.var 0) := by
  rw [identity_mathematical_observation, variable_mathematical_observation]
  intro h
  cases h

theorem Omega_mathematical_observation (depth : Nat) :
    BohmObservation.tree depth LambdaTerm.Omega = .bot := by
  cases depth with
  | zero =>
      exact (BohmObservation.tree_eq_iff _ _ _).mpr (.zero _)
  | succ depth => exact (BohmObservation.tree_bot_iff _ _).mpr Omega_unsolvable

/-- The same real beta step that changes the bounded observation preserves
every uncapped finite-depth observation. -/
theorem budget_counterexample_uncapped_agrees (depth : Nat) :
    let argument := LambdaTerm.app LambdaTerm.I (.app LambdaTerm.I LambdaTerm.I)
    BohmObservation.tree depth (.app LambdaTerm.I argument) =
      BohmObservation.tree depth argument :=
  BohmObservation.tree_beta_eq (.var 0)
    (.app LambdaTerm.I (.app LambdaTerm.I LambdaTerm.I)) depth

/-- The budget counterexample is not bottom mathematically at positive depth. -/
theorem budget_counterexample_uncapped_identity (depth : Nat) :
    BohmObservation.tree (depth + 1)
      (.app LambdaTerm.I (.app LambdaTerm.I (.app LambdaTerm.I LambdaTerm.I))) =
      .node 1 0 [] := by
  have first :
      BohmObservation.tree (depth + 1)
        (.app LambdaTerm.I (.app LambdaTerm.I (.app LambdaTerm.I LambdaTerm.I))) =
      BohmObservation.tree (depth + 1)
        (.app LambdaTerm.I (.app LambdaTerm.I LambdaTerm.I)) :=
    BohmObservation.tree_beta_eq (.var 0)
      (.app LambdaTerm.I (.app LambdaTerm.I LambdaTerm.I)) (depth + 1)
  have second :
      BohmObservation.tree (depth + 1) (.app LambdaTerm.I (.app LambdaTerm.I LambdaTerm.I)) =
      BohmObservation.tree (depth + 1) (.app LambdaTerm.I LambdaTerm.I) :=
    BohmObservation.tree_beta_eq (.var 0) (.app LambdaTerm.I LambdaTerm.I) (depth + 1)
  have third :
      BohmObservation.tree (depth + 1) (.app LambdaTerm.I LambdaTerm.I) =
      BohmObservation.tree (depth + 1) LambdaTerm.I :=
    BohmObservation.tree_beta_eq (.var 0) LambdaTerm.I (depth + 1)
  exact first.trans (second.trans (third.trans (identity_mathematical_observation depth)))

/-- Bounded bottom need not be a mathematical bottom observation. -/
theorem bounded_and_uncapped_bottom_disagree :
    let term := LambdaTerm.app LambdaTerm.I
      (.app LambdaTerm.I (.app LambdaTerm.I LambdaTerm.I))
    bohmTree 1 term = .bot ∧ BohmObservation.tree 1 term ≠ .bot := by
  dsimp only
  refine ⟨rfl, ?_⟩
  rw [budget_counterexample_uncapped_identity 0]
  intro h
  cases h

/-- A genuinely successful depth-one evaluation matches its mathematical tree. -/
theorem depth_one_search_agrees :
    BohmObservation.tree 1 (.app LambdaTerm.I LambdaTerm.I) =
      bohmTree 1 (.app LambdaTerm.I LambdaTerm.I) := by
  apply (BohmObservation.tree_eq_iff _ _ _).mpr
  exact BohmObservation.depth_one_of_search (hnf := LambdaTerm.I) rfl

/-- Recursive observations retain ordered, observably distinct argument trees. -/
theorem ordered_argument_observations :
    BohmObservation.tree 2 (.app (.app (.var 0) LambdaTerm.I) (.var 1)) =
      .node 0 0 [.node 1 0 [], .node 0 1 []] := by
  apply (BohmObservation.tree_eq_iff _ _ _).mpr
  exact .node Relation.ReflTransGen.refl rfl
    (.cons (.node Relation.ReflTransGen.refl rfl .nil)
      (.cons (.node Relation.ReflTransGen.refl rfl .nil) .nil))

theorem swapped_argument_observations :
    BohmObservation.tree 2 (.app (.app (.var 0) (.var 1)) LambdaTerm.I) =
      .node 0 0 [.node 0 1 [], .node 1 0 []] := by
  apply (BohmObservation.tree_eq_iff _ _ _).mpr
  exact .node Relation.ReflTransGen.refl rfl
    (.cons (.node Relation.ReflTransGen.refl rfl .nil)
      (.cons (.node Relation.ReflTransGen.refl rfl .nil) .nil))

theorem swapping_arguments_changes_mathematical_tree :
    BohmObservation.tree 2 (.app (.app (.var 0) LambdaTerm.I) (.var 1)) ≠
      BohmObservation.tree 2 (.app (.app (.var 0) (.var 1)) LambdaTerm.I) := by
  rw [ordered_argument_observations, swapped_argument_observations]
  intro h
  cases h

/-- An unsolvable argument is bottom without destroying its solvable parent. -/
theorem unsolvable_child_observation :
    BohmObservation.tree 2 (.app (.var 0) LambdaTerm.Omega) = .node 0 0 [.bot] := by
  apply (BohmObservation.tree_eq_iff _ _ _).mpr
  exact .node Relation.ReflTransGen.refl rfl (.cons (.bottom Omega_unsolvable) .nil)

end Mettapedia.GSLT.GraphTheory
