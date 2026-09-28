import Mettapedia.OSLF.Syntax.CartesianModelSetSemantics
import Mettapedia.OSLF.Syntax.RhoCartesianModelFiniteGeneration

/-!
# Set-valued finite-limit semantics for authored rho models

The name and process context representations of the actual reflective rho
presentation extend to finite-limit-preserving set-valued semantics on the
relative finite-presentation category. Restriction recovers the original
authored model naturally in substitutions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoCartesianModelSetSemantics

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.CartesianContextModels
open Mettapedia.OSLF.Binding.RhoCartesianContextModels

private instance : HasFiniteProducts Contexts :=
  hasFiniteProducts_of_has_binary_and_terminal

noncomputable def nameSemantics : FinitePresentationObjects Contexts ⥤ Type :=
  finitePresentationSemantics Contexts nameModel

noncomputable def processSemantics : FinitePresentationObjects Contexts ⥤ Type :=
  finitePresentationSemantics Contexts processModel

theorem nameSemantics_preservesFiniteLimits :
    PreservesFiniteLimits nameSemantics :=
  finitePresentationSemantics_preservesFiniteLimits Contexts nameModel

theorem processSemantics_preservesFiniteLimits :
    PreservesFiniteLimits processSemantics :=
  finitePresentationSemantics_preservesFiniteLimits Contexts processModel

noncomputable def nameSemantics_authoredIso :
    authoredContext Contexts ⋙ nameSemantics ≅ nameModel.1 :=
  authoredContextSemanticsIso Contexts nameModel

noncomputable def processSemantics_authoredIso :
    authoredContext Contexts ⋙ processSemantics ≅ processModel.1 :=
  authoredContextSemanticsIso Contexts processModel

theorem rho_modelSemantics_full :
    (finitePresentationSemanticsFunctor Contexts).Full :=
  finitePresentationSemanticsFunctor_full Contexts

theorem rho_modelSemantics_faithful :
    (finitePresentationSemanticsFunctor Contexts).Faithful :=
  finitePresentationSemanticsFunctor_faithful Contexts

end Mettapedia.OSLF.Binding.RhoCartesianModelSetSemantics
