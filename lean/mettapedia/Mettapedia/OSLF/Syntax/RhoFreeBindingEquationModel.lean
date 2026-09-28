import Mettapedia.OSLF.Syntax.FreeBindingEquationModel
import Mettapedia.OSLF.Syntax.RhoEquationModelControls

/-!
# The authored reflective equations have a free binding-clone model

The local intrinsic reflective presentation's binary parallel operator and
its commutative-monoid equations instantiate the general semantic
equation-model construction. Their quotient model is initial among binding
clones that satisfy all three local axioms under every semantic continuation
valuation and ordinary-variable assignment. The raw term algebra is excluded
by the separately proved commutativity negative control. The book's Chapter 7
bag-valued parallel operator and QuoteDrop equation are a further source
comparison, not a result of this instance.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoFreeBindingEquationModel

open CategoryTheory.Limits
open Mettapedia.OSLF.Binding.RhoSchema

/-- The equation list used by the free model is the equation component of
the actual authored rho presentation. -/
theorem authored_equations : rho.eqs = rhoE := rfl

/-- The quotient of the authored rho syntax satisfies commutativity,
associativity and the right-unit law for every semantic valuation. -/
theorem rho_quotient_satisfies :
    BindingEquationInterpretation.Satisfies
      (BindingEquationQuotientModel.algebra rho.eqs) rho.eqs :=
  BindingEquationQuotientModel.algebra_satisfies rho.eqs

/-- The authored rho equation model has the full initial-object property,
including substitution and the input binder. -/
noncomputable def rho_equation_model_initial :
    IsInitial (FreeBindingEquationModel.presented rho.eqs) :=
  FreeBindingEquationModel.presentedIsInitial rho.eqs

end Mettapedia.OSLF.Binding.RhoFreeBindingEquationModel
