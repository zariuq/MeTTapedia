import Mettapedia.OSLF.Syntax.BindingPureContextualInterpretation
import Mettapedia.OSLF.Syntax.BindingCloneEquationTransport
import Mettapedia.OSLF.Syntax.SecondOrderEquationContext
import Mettapedia.OSLF.Syntax.BindingEquationFamilyModel

/-!
# Canonical instances and full ordinary equation families

For an equation with no metavariable declarations, its injected-variable
instance determines every contextual ordinary-environment instance by the
full clone substitution laws. Consequently full clone maps transport these
families to arbitrary target environments. This uses neither surjectivity nor
an assertion that target environment values come from the source.

Equations with arbitrary target metavariable bodies are outside this result.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingFirstOrderFamilyTransport

open FreeBindingTerms BindingSubstitutionAlgebra SecondOrderContext

universe u v

variable {S : Signature}

def Canonical (algebra : BindingCloneAlgebra.Algebra.{u} S) (equation : EqAxiom S []) : Prop :=
  BindingCloneFoldSubstitution.interpret algebra (BaseEquation.ofEmptySchema equation).left =
    BindingCloneFoldSubstitution.interpret algebra (BaseEquation.ofEmptySchema equation).right

/-- An injected-variable instance already gives every complete ordinary
semantic instance, with an independent captured ambient environment. -/
theorem contextual_of_canonical (algebra : BindingCloneAlgebra.Algebra.{u} S)
    (equation : EqAxiom S []) (canonical : Canonical algebra equation)
    {Θ Γ : Ctx S}
    (valuation : SemanticContextualMetavariables.Valuation (M := []) algebra Θ)
    (ambient : Environment S algebra.substitution.Carrier Θ Γ)
    (ordinary : Environment S algebra.substitution.Carrier equation.ctx Γ) :
    SemanticContextualMetavariables.interpretSchema algebra valuation ambient ordinary equation.lhs =
      SemanticContextualMetavariables.interpretSchema algebra valuation ambient ordinary equation.rhs := by
  have left := BindingPureContextualInterpretation.interpret_embed algebra valuation ambient ordinary
    (BaseEquation.ofEmptySchema equation).left
  have right := BindingPureContextualInterpretation.interpret_embed algebra valuation ambient ordinary
    (BaseEquation.ofEmptySchema equation).right
  have leftEndpoint := congrArg
    (SemanticContextualMetavariables.interpretSchema algebra valuation ambient ordinary)
    (BaseEquation.ofEmptySchema_left equation).symm
  have rightEndpoint := congrArg
    (SemanticContextualMetavariables.interpretSchema algebra valuation ambient ordinary)
    (BaseEquation.ofEmptySchema_right equation).symm
  exact (leftEndpoint.trans left).trans
    ((congrArg (algebra.substitution.substitute ordinary) canonical).trans
      (rightEndpoint.trans right).symm)

/-- Full satisfaction yields the canonical instance by choosing the actual
variable injection environment; substitution identity removes that instance. -/
theorem canonical_of_contextual (algebra : BindingCloneAlgebra.Algebra.{u} S)
    {family : EqAxiom S [] → Prop}
    (satisfaction : BindingEquationFamilyModel.Satisfies algebra family)
    (equation : EqAxiom S []) (admitted : family equation) : Canonical algebra equation := by
  let valuation : SemanticContextualMetavariables.Valuation (M := []) algebra [] :=
    fun position => Fin.elim0 position
  let ambient : Environment S algebra.substitution.Carrier [] equation.ctx :=
    fun _ position => nomatch position
  let ordinary : Environment S algebra.substitution.Carrier equation.ctx equation.ctx :=
    fun _ position => algebra.substitution.injectVar position
  have source := satisfaction equation admitted valuation ambient ordinary
  have left := BindingPureContextualInterpretation.interpret_embed algebra valuation ambient ordinary
    (BaseEquation.ofEmptySchema equation).left
  have right := BindingPureContextualInterpretation.interpret_embed algebra valuation ambient ordinary
    (BaseEquation.ofEmptySchema equation).right
  have leftEndpoint := congrArg
    (SemanticContextualMetavariables.interpretSchema algebra valuation ambient ordinary)
    (BaseEquation.ofEmptySchema_left equation).symm
  have rightEndpoint := congrArg
    (SemanticContextualMetavariables.interpretSchema algebra valuation ambient ordinary)
    (BaseEquation.ofEmptySchema_right equation).symm
  exact (algebra.substitution.substitute_identity _).symm.trans
    ((leftEndpoint.trans left).symm.trans
      (source.trans ((rightEndpoint.trans right).trans (algebra.substitution.substitute_identity _))))

/-- A full clone map carries the canonical instance. Target contexts and
their supplied values do not need to be images of source values. -/
theorem canonical_map {source : BindingCloneAlgebra.Algebra.{u} S}
    {target : BindingCloneAlgebra.Algebra.{v} S} (arrow : FreeBindingClone.Hom source target)
    {equation : EqAxiom S []} (canonical : Canonical source equation) : Canonical target equation :=
  (BindingCloneEquationTransport.interpret_naturality arrow
    (BaseEquation.ofEmptySchema equation).left).symm.trans
    ((congrArg arrow.raw.map canonical).trans
      (BindingCloneEquationTransport.interpret_naturality arrow
        (BaseEquation.ofEmptySchema equation).right))

theorem satisfies_map {source : BindingCloneAlgebra.Algebra.{u} S}
    {target : BindingCloneAlgebra.Algebra.{v} S} (arrow : FreeBindingClone.Hom source target)
    {family : EqAxiom S [] → Prop}
    (satisfaction : BindingEquationFamilyModel.Satisfies source family) :
    BindingEquationFamilyModel.Satisfies target family := by
  intro equation admitted Θ Γ valuation ambient ordinary
  exact contextual_of_canonical target equation
    (canonical_map arrow (canonical_of_contextual source satisfaction equation admitted))
    valuation ambient ordinary

end Mettapedia.OSLF.Binding.BindingFirstOrderFamilyTransport
