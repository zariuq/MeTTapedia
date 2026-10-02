import Mettapedia.GSLT.GraphTheory.BohmTreeSemantics

/-! Positive and negative controls for search fuel versus semantic observations. -/

namespace Mettapedia.GSLT.GraphTheory

theorem beta_search_eventually_agrees (body argument : LambdaTerm) (depth : Nat) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel →
      BohmSearch.observe (fun _ => fuel) depth (.app (.lam body) argument) =
        BohmSearch.observe (fun _ => fuel) depth (argument.subst 0 body) :=
  (BohmObservation.equivalent_iff_eventual_agreement _ _).mp
    (BohmObservation.beta_equivalent body argument) depth

/-- β-convertible terms are observed identically by every sufficiently large
budget, at each fixed depth. -/
theorem conversion_search_eventually_agrees {first second : LambdaTerm}
    (convertible : Relation.EqvGen ParRed first second) (depth : Nat) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel →
      BohmSearch.observe (fun _ => fuel) depth first =
        BohmSearch.observe (fun _ => fuel) depth second :=
  (BohmObservation.equivalent_iff_eventual_agreement _ _).mp
    (BohmObservation.equivalent_of_conversion convertible) depth

/-- A successful root search does not certify every recursively requested node. -/
theorem root_success_can_leave_unknown_argument :
    toHNF 1 (.app (.var 0) (.app LambdaTerm.I LambdaTerm.I)) =
        some (.app (.var 0) (.app LambdaTerm.I LambdaTerm.I)) ∧
      BohmSearch.observe (fun _ => 1) 2 (.app (.var 0) (.app LambdaTerm.I LambdaTerm.I)) =
        .node 0 0 [.bot] := ⟨rfl, rfl⟩

theorem root_success_is_not_full_observation :
    BohmSearch.observe (fun _ => 1) 2 (.app (.var 0) (.app LambdaTerm.I LambdaTerm.I)) ≠
      BohmObservation.tree 2 (.app (.var 0) (.app LambdaTerm.I LambdaTerm.I)) := by
  have argument : BohmObservation.tree 1 (.app LambdaTerm.I LambdaTerm.I) = .node 1 0 [] :=
    (BohmObservation.tree_beta_eq (.var 0) LambdaTerm.I 1).trans
      (identity_mathematical_observation 0)
  have exactTree := BohmObservation.tree_node_of_reaches
    (term := .app (.var 0) (.app LambdaTerm.I LambdaTerm.I))
    (hnf := .app (.var 0) (.app LambdaTerm.I LambdaTerm.I))
    (arguments := [.app LambdaTerm.I LambdaTerm.I]) Relation.ReflTransGen.refl rfl 1
  rw [root_success_can_leave_unknown_argument.2, exactTree]
  simp only [List.map_cons, List.map_nil, argument]
  intro equality
  cases equality

/-- Beta equality is a semantic contract, not equality of budget diagnostics. -/
theorem same_budget_beta_can_differ :
    let argument := LambdaTerm.app LambdaTerm.I (.app LambdaTerm.I LambdaTerm.I)
    BohmObservation.Equivalent (.app LambdaTerm.I argument) argument ∧
      BohmSearch.observe (fun _ => 3) 1 (.app LambdaTerm.I argument) ≠
        BohmSearch.observe (fun _ => 3) 1 argument := by
  dsimp only
  refine ⟨BohmObservation.beta_equivalent (.var 0) _, ?_⟩
  change (BohmTree.bot : BohmTree) ≠ .node 1 0 []
  intro equality
  cases equality

/-- Increasing the fuel reveals the missing information without changing its meaning. -/
theorem more_fuel_recovers_identity :
    BohmSearch.observe (fun _ => 4) 1
      (.app LambdaTerm.I (.app LambdaTerm.I (.app LambdaTerm.I LambdaTerm.I))) =
        .node 1 0 [] := rfl

/-- Known unsolvability and inconclusive timeout may have the same finite output. -/
theorem timeout_does_not_identify_solvability :
    BohmSearch.observe (fun _ => 1) 1 (.app LambdaTerm.I LambdaTerm.I) =
        BohmSearch.observe (fun _ => 1) 1 LambdaTerm.Omega ∧
      (LambdaTerm.app LambdaTerm.I LambdaTerm.I).Solvable ∧ LambdaTerm.Omega.Unsolvable := by
  refine ⟨?_, solvable_of_toHNF (t := LambdaTerm.app LambdaTerm.I LambdaTerm.I)
    (fuel := 2) (hnf := LambdaTerm.I) rfl, Omega_unsolvable⟩
  rw [show BohmSearch.observe (fun _ => 1) 1 (.app LambdaTerm.I LambdaTerm.I) = .bot from rfl]
  simp only [BohmSearch.observe, unsolvable_toHNF_none Omega_unsolvable]

end Mettapedia.GSLT.GraphTheory
