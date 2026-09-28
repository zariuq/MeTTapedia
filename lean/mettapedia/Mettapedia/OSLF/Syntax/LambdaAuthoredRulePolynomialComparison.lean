import Mettapedia.OSLF.Syntax.LambdaRuleDerivationPolynomial
import Mettapedia.OSLF.Syntax.LambdaIntrinsicPresentation

/-!
# The authored lambda beta schema and its indexed constructor

The actual intrinsic Chapter 7 beta presentation has one closed root rule.
Its firing data give the beta constructor of the indexed derivation algebra,
and every closed beta constructor is an authored root firing. Contextual
congruence and binder-local premises remain separate constructors; this
comparison does not claim that the closed root schema expresses them.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaAuthoredRulePolynomialComparison

open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaIntrinsicPresentation
open Mettapedia.OSLF.Binding.LambdaRuleDerivationPolynomial

/-- A directly authored closed beta firing produces a retained constructor
tree with the same endpoints. -/
theorem authored_root_has_beta_tree
    {source target : Term sig [] .term}
    (firing : betaRule.RootStep source target) :
    Nonempty (Derivation source target) := by
  obtain ⟨body, arg, rfl, rfl⟩ :=
    (beta_root_iff source target).mp firing
  exact ⟨.roll (.beta body arg) (fun impossible => impossible.elim)⟩

/-- Conversely, every directly constructed closed beta node is an instance
of the canonical authored schema, not merely of a hand-written relation. -/
theorem beta_constructor_is_authored_root
    (body : Term sig [Srt.term] .term)
    (arg : Term sig [] .term) :
    betaRule.RootStep (appT (lamT body) arg) (inst body arg) :=
  beta_root_instance body arg

/-- The earlier authored root-to-contextual comparison factors through the
proof-relevant polynomial witness. -/
theorem authored_root_factors_through_tree
    {source target : Term sig [] .term}
    (firing : betaRule.RootStep source target) :
    LambdaContextualRung.Step [] source target := by
  obtain ⟨tree⟩ := authored_root_has_beta_tree firing
  exact toStep _ tree

#print axioms authored_root_has_beta_tree
#print axioms beta_constructor_is_authored_root
#print axioms authored_root_factors_through_tree

end Mettapedia.OSLF.Binding.LambdaAuthoredRulePolynomialComparison
