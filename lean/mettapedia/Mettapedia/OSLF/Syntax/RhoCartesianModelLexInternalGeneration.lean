import Mettapedia.OSLF.Syntax.CartesianModelLexInternalGeneration
import Mettapedia.OSLF.Syntax.RhoCartesianModelLexTarget

/-!
# Internal generation and faithful restriction for authored rho contexts

The actual two-sorted rho context presentation satisfies internal finite-
limit generation. Consequently a map of left-exact interpretations in any
finitely complete target is determined by its values on rho contexts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoCartesianModelLexInternalGeneration

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.CartesianContextModels
open Mettapedia.OSLF.Binding.RhoCartesianContextModels

universe u v

private instance : HasFiniteProducts Contexts :=
  hasFiniteProducts_of_has_binary_and_terminal

theorem rho_finitePresentation_generated
    (X : FinitePresentationObjects Contexts) :
    AuthoredFiniteLimitClosure Contexts X :=
  finitePresentationObjects_authoredFiniteLimitGenerated Contexts X

theorem rho_restriction_faithful
    (D : Type u) [Category.{v} D] [HasFiniteLimits D] :
    (restrictLeftExactTarget Contexts D).Faithful :=
  restrictLeftExactTarget_faithful Contexts D

end Mettapedia.OSLF.Binding.RhoCartesianModelLexInternalGeneration
