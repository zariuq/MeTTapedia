import Mettapedia.OSLF.Syntax.CartesianModelLexTarget
import Mettapedia.OSLF.Syntax.CartesianModelLexUniqueness
import Mettapedia.OSLF.Syntax.RhoCartesianModelLexRestriction

/-!
# Presheaf-valued interpretations of authored rho contexts

The Yoneda interpretation of finite rho presentations has values in a
presheaf category. Its restriction is a product-preserving interpretation
of the actual two-sorted rho context category, exercising the general
arbitrary-target restriction on a non-set-valued example.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoCartesianModelLexTarget

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.CartesianContextModels
open Mettapedia.OSLF.Binding.RhoCartesianContextModels

private instance : HasFiniteProducts Contexts :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- The representable semantics of all finite rho presentations, with
presheaves on finite presentations as the target. -/
noncomputable def rhoYonedaLex : LeftExactTargetInterpretations Contexts
    ((FinitePresentationObjects Contexts)ᵒᵖ ⥤ Type) :=
  yonedaTargetInterpretation Contexts

/-- The induced authored rho model retains its existing context products. -/
noncomputable def rhoYonedaAuthored : CartesianTargetInterpretations Contexts
    ((FinitePresentationObjects Contexts)ᵒᵖ ⥤ Type) :=
  (restrictLeftExactTarget Contexts
    ((FinitePresentationObjects Contexts)ᵒᵖ ⥤ Type)).obj rhoYonedaLex

theorem rhoYonedaAuthored_preservesProducts :
    PreservesFiniteProducts rhoYonedaAuthored.1 :=
  rhoYonedaAuthored.2

/-- For rho interpretations in the presheaf target, agreement on the actual
authored contexts determines every component in their finite-limit closure. -/
theorem rho_transformations_agree_on_generated_presentations
    (T U : LeftExactTargetInterpretations Contexts
      ((FinitePresentationObjects Contexts)ᵒᵖ ⥤ Type))
    (α β : T ⟶ U)
    (hcontexts : ∀ X : Contexts,
      α.hom.app ((authoredContext Contexts).obj X) =
        β.hom.app ((authoredContext Contexts).obj X))
    (P : FinitePresentationObjects Contexts)
    (hP : AuthoredFiniteLimitClosure Contexts P) :
    α.hom.app P = β.hom.app P :=
  transformation_eq_on_authoredFiniteLimitClosure Contexts _
    T U α β hcontexts P hP

end Mettapedia.OSLF.Binding.RhoCartesianModelLexTarget
