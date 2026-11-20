import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeSubstitution

/-! # Literal active heads of every helper equation -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution

theorem rules_heads : ∀ rule ∈ rules,
    literalHead rule.lhs = some activeTag ∧ literalHead rule.rhs = some activeTag := by
  have checked : rules.all (fun rule => decide
    (literalHead rule.lhs = some activeTag ∧ literalHead rule.rhs = some activeTag)) = true := by
    decide +kernel
  intro rule inside
  exact of_decide_eq_true (List.all_eq_true.mp checked rule inside)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution
