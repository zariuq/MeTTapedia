import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramSelectedExponentials
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedYonedaProgramProducts

/-!
# Canonical program data for the operational Yoneda embedding

The program interpretation uses the actual product comparisons and the
independently represented selected exponentials. Keeping this construction
as one value makes its meaning and constructor comparisons share the same
categorical data.
-/

set_option autoImplicit false
noncomputable section
namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open CategoricalBindingModel
open IntrinsicScopedLocalPolynomial
universe w
variable {S : Signature} {K : List (MetaArity S)}

/-- The actual product and selected-power interpretation of the program
restriction of the operational Yoneda embedding. -/
def programData (R : List (LocalRule S)) (equations : List (EqAxiom S K)) :
    PreservingData (programRestriction.{w} R equations) :=
  programRestrictionData R equations (programExponential R equations)

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
end
