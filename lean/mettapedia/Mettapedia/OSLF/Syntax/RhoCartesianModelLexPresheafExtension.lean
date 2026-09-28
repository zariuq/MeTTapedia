import Mettapedia.OSLF.Syntax.CartesianModelLexPresheafExtension
import Mettapedia.OSLF.Syntax.RhoCartesianModelLexTarget

/-!
# A presheaf extension of the authored rho context embedding

Yoneda embeds the actual rho context category in presheaves on itself. The
generic pointwise extension supplies a left-exact interpretation of all
relative rho presentations and recovers this authored embedding on
restriction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoCartesianModelLexPresheafExtension

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.CartesianContextModels
open Mettapedia.OSLF.Binding.RhoCartesianContextModels

private instance : HasFiniteProducts Contexts :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- The rho context Yoneda embedding as an authored cartesian model. -/
noncomputable def rhoContextYonedaModel :
    CartesianTargetInterpretations Contexts (Contextsᵒᵖ ⥤ Type) :=
  ⟨yoneda, by
    change PreservesFiniteProducts
      (yoneda : Contexts ⥤ Contextsᵒᵖ ⥤ Type)
    infer_instance⟩

/-- Its canonical extension to relative finite presentations. -/
noncomputable def rhoContextYonedaExtension :
    LeftExactTargetInterpretations Contexts (Contextsᵒᵖ ⥤ Type) :=
  extendPresheafAuthoredModel Contexts Contexts rhoContextYonedaModel

/-- The extension agrees with Yoneda on every authored rho context. -/
noncomputable def rhoContextYonedaRestrictionIso :
    authoredContext Contexts ⋙ rhoContextYonedaExtension.1 ≅
      (yoneda : Contexts ⥤ Contextsᵒᵖ ⥤ Type) :=
  extendPresheafAuthoredModelRestrictionIso
    Contexts Contexts rhoContextYonedaModel

end Mettapedia.OSLF.Binding.RhoCartesianModelLexPresheafExtension
