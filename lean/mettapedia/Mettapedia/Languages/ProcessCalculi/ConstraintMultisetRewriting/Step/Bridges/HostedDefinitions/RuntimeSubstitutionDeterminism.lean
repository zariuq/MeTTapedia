import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeSubstitutionSteps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.LiteralPaths

/-!
# Checked clause and environment uniqueness for the finite helper

Rigid literal paths distinguish every pair of different helper clauses.
Separately, a checked path to each slot recovers every argument of a matched
clause. Together these give uniqueness of the actual next source term.
Neither condition is imposed on a surrounding language or its nondeterministic
main reduction rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution

open SourceLanguage.Elaboration
open LiteralPaths

/-- Phase names and the inner constructor names at the first three fields. -/
def probes : List (List Nat) := [[1, 0], [1, 1, 0], [1, 2, 0], [1, 3, 0]]

theorem pairs_checked :
    (List.finRange rules.length).all (fun first =>
      (List.finRange rules.length).all (fun second =>
        if first = second then true else separated probes (rules.get first) (rules.get second))) = true := by
  decide +kernel

theorem rules_separated (first second : Fin rules.length) (different : first ≠ second) :
    separated probes (rules.get first) (rules.get second) = true := by
  have row := List.all_eq_true.mp pairs_checked first (by simp)
  have pair := List.all_eq_true.mp row second (by simp)
  simpa only [if_neg different] using pair

theorem rules_deterministic : ∀ rule ∈ rules, EquationDeterministic rule := by
  intro rule inside
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply equation_deterministic
  all_goals decide +kernel

theorem step_deterministic {call first second : MClosed}
    (one : Step call first) (two : Step call second) : first = second := by
  obtain ⟨firstRule, firstAnswer⟩ := one
  obtain ⟨secondRule, secondAnswer⟩ := two
  by_cases same : firstRule = secondRule
  · subst secondRule
    exact rules_deterministic (rules.get firstRule) (List.get_mem _ _) call first second firstAnswer secondAnswer
  · exact False.elim (separated_no_common_call probes (rules.get firstRule) (rules.get secondRule)
      (rules_separated firstRule secondRule same) call first second ⟨firstAnswer, secondAnswer⟩)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution
