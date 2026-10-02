import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafEquations
import Mettapedia.OSLF.Syntax.BindingEquationQuotientModel
import Mettapedia.OSLF.Syntax.CategoricalBindingEquationEquivalence

/-!
# Equation models in the operational presheaf target

The constructed binding interpretation is packaged with its full contextual
equation law. The canonical instance uses the actual authored equation quotient
and its proved contextual satisfaction theorem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafProgramModel

open IntrinsicScopedOperationalPresheafPrograms
open IntrinsicScopedOperationalPresheafEquations
open CategoricalBindingEquationEquivalence
open SecondOrderContext

universe u
variable {S : Signature} {N : List (MetaArity S)}

/-- A clone satisfying the authored contextual equations gives a satisfying
categorical interpretation in its actual operational presheaf target. -/
noncomputable def satisfyingInterpretation (A : BindingCloneAlgebra.Algebra.{u} S)
    (equations : List (EqAxiom S N))
    (sat : BindingEquationInterpretation.Satisfies A equations) :
    SatisfyingInterpretation (D := target A) (authoredEquationPresentation S equations) :=
  ⟨⟨model A⟩, model_satisfies A equations sat⟩

/-- The actual equation quotient's operational binding model satisfies the
authored categorical presentation, including captured ambient parameters. -/
theorem quotient_model_satisfies (equations : List (EqAxiom S N)) :
    (model (BindingEquationQuotientModel.algebra equations)).Satisfies
      (authoredEquationPresentation S equations) :=
  model_satisfies (BindingEquationQuotientModel.algebra equations) equations
    (BindingEquationQuotientModel.algebra_satisfies equations)

/-- The canonical authored quotient interpretation uses the quotient clone's
own presheaf base and its proved full contextual equation law. -/
noncomputable def quotientSatisfyingInterpretation (equations : List (EqAxiom S N)) :
    SatisfyingInterpretation
      (D := target (BindingEquationQuotientModel.algebra equations))
      (authoredEquationPresentation S equations) :=
  satisfyingInterpretation (BindingEquationQuotientModel.algebra equations) equations
    (BindingEquationQuotientModel.algebra_satisfies equations)

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafProgramModel
