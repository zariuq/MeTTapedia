import Mettapedia.OSLF.Syntax.AuthoredPositionedRulePolynomial
import Mettapedia.OSLF.Syntax.ContextualRootEvents
import Mettapedia.OSLF.Syntax.Presentation

/-!
# Root-event comparison for semantic authored rules

At the free term model, the semantic rule-instance data are exactly the
repository's already established syntactic contextual root events, together
with their selected authored rule index. The equivalence preserves the
ambient context, result sort, both endpoints, and the individual occurrence.
It does not identify a root event with a firing beneath an outer context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.AuthoredPositionedRootComparison

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables

variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (PositionedRewrite (withMetas S M)))

/-- A syntactic root event carries its ambient context and ordered authored
rule index. -/
abbrev RootOccurrence :=
  Σ Γ : Ctx S, Σ i : Fin R.length,
    ContextualRootEvents.Instance ((R.get i).unpositioned) Γ

/-- The syntactic root-event representation and the semantic occurrence
representation coincide at the actual free term binding clone. -/
def rootEquiv : RootOccurrence R ≃
    AuthoredPositionedRulePolynomial.RuleInstance R
      (BindingCloneAlgebra.terms S) where
  toFun := fun ⟨Γ, i, firing⟩ =>
    { index := i
      ambient := Γ
      valuation := firing.body
      close := firing.close }
  invFun := fun occurrence =>
    ⟨occurrence.ambient, occurrence.index,
      { body := occurrence.valuation
        close := occurrence.close }⟩
  left_inv := by
    intro occurrence
    rcases occurrence with ⟨Γ, i, ⟨body, close⟩⟩
    rfl
  right_inv := by
    intro occurrence
    cases occurrence
    rfl

/-- The representation equivalence preserves the exact syntactic source
and target of every authored root firing. -/
theorem rootEquiv_judgment
    (occurrence : RootOccurrence R) :
    AuthoredPositionedRulePolynomial.judgmentOf R
        (BindingCloneAlgebra.terms S) (rootEquiv R occurrence) =
      ⟨occurrence.1, (R.get occurrence.2.1).sort,
        occurrence.2.2.source, occurrence.2.2.target⟩ := by
  rcases occurrence with ⟨Γ, i, firing⟩
  rcases firing with ⟨body, close⟩
  change
    (⟨Γ, (R.get i).sort,
      interpretSchema (BindingCloneAlgebra.terms S) body
        (fun _ var => Term.var var) close (R.get i).lhs,
      interpretSchema (BindingCloneAlgebra.terms S) body
        (fun _ var => Term.var var) close (R.get i).rhs⟩ :
      AuthoredPositionedRulePolynomial.Judgment (BindingCloneAlgebra.terms S)) =
    (⟨Γ, (R.get i).sort,
      ContextualAssignment.instantiate body
        (fun _ var => Term.var var) close (R.get i).lhs,
      ContextualAssignment.instantiate body
        (fun _ var => Term.var var) close (R.get i).rhs⟩ :
      AuthoredPositionedRulePolynomial.Judgment (BindingCloneAlgebra.terms S))
  have sourceEq := interpretSchema_terms body
    (fun _ var => Term.var var) close (R.get i).lhs
  have targetEq := interpretSchema_terms body
    (fun _ var => Term.var var) close (R.get i).rhs
  exact congrArg
    (fun endpoints : Term S Γ (R.get i).sort × Term S Γ (R.get i).sort =>
      (⟨Γ, (R.get i).sort, endpoints⟩ :
        AuthoredPositionedRulePolynomial.Judgment (BindingCloneAlgebra.terms S)))
    (congrArg₂ Prod.mk sourceEq targetEq)

/-- Send an actual syntactic root occurrence to an equation-class model.
The occurrence and authored rule index remain explicit; only its term values
are projected to equation classes. -/
noncomputable def projectRoot (E : List (EqAxiom S M))
    (occurrence : RootOccurrence R) :
    AuthoredPositionedRulePolynomial.RuleInstance R
      (BindingEquationQuotientModel.algebra E) :=
  AuthoredPositionedRulePolynomial.mapInstance R
    (BindingEquationQuotientModel.projection E) (rootEquiv R occurrence)

/-- Projecting a root event commutes with taking its sorted endpoints.
The rule index is retained, but projection need not be injective on raw
metavariable or closing assignments. -/
theorem projectRoot_judgment (E : List (EqAxiom S M))
    (occurrence : RootOccurrence R) :
    AuthoredPositionedRulePolynomial.judgmentOf R
        (BindingEquationQuotientModel.algebra E)
        (projectRoot R E occurrence) =
      AuthoredPositionedRulePolynomial.mapJudgment
        (BindingEquationQuotientModel.projection E)
        ⟨occurrence.1, (R.get occurrence.2.1).sort,
          occurrence.2.2.source, occurrence.2.2.target⟩ := by
  rw [projectRoot, AuthoredPositionedRulePolynomial.mapInstance_judgment,
    rootEquiv_judgment]

#print axioms rootEquiv
#print axioms rootEquiv_judgment
#print axioms projectRoot_judgment

end Mettapedia.OSLF.Binding.AuthoredPositionedRootComparison
