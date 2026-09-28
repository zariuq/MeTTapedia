import Mettapedia.OSLF.Syntax.FormalFiniteLimitObjects
import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedContextEmbedding
import Mettapedia.OSLF.Syntax.RhoCommunicationSchema

/-!
# The two finite-limit constructions on authored rho contexts

The formal finite-limit object category is instantiated on the actual rho
substitution contexts. Its embedding is fully faithful but does not preserve
the existing terminal context. The ambient Yoneda closure preserves that
context, so no finite-limit-preserving comparison from the ambient closure
can extend the identity interpretation of authored contexts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoFormalFiniteLimitBoundary

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.FormalFiniteLimits

abbrev Contexts := Syntactic.Ctxt sig

theorem formal_hasFiniteLimits : HasFiniteLimits (Objects Contexts) := inferInstance

instance formal_base_full : (base Contexts).Full := inferInstance

instance formal_base_faithful : (base Contexts).Faithful := inferInstance

theorem formal_base_not_preserves_terminal :
    ¬ PreservesLimit (Functor.empty.{0} Contexts) (base Contexts) :=
  base_not_preserves_terminal Contexts

theorem ambient_base_preserves_finite_products :
    PreservesFiniteProducts (contextIntoFiniteLimitGenerated sig) :=
  contextIntoFiniteLimitGenerated_preservesFiniteProducts sig

theorem no_lex_comparison_from_ambient
    (extension :
      (Mettapedia.OSLF.FiniteLimitYoneda.Generated Contexts).FullSubcategory ⥤
        Objects Contexts)
    [PreservesFiniteLimits extension]
    (comparison :
      Mettapedia.OSLF.FiniteLimitYoneda.intoGenerated Contexts ⋙ extension ≅
      base Contexts) : False :=
  no_lex_extension_from_ambient Contexts extension comparison

end Mettapedia.OSLF.Binding.RhoFormalFiniteLimitBoundary
