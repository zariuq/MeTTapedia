import Mettapedia.GSLT.LanguageDef.CostOneDecorationDisplayed
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryObject

/-!
# Projection of rho's hereditary Cost total point

The retained rho elaboration evaluates under the lawful total-space
projection to the exact finite-support hereditary Cost₁ object.  Applying the
compact one-step functor then gives precisely that object's compact output.

Both statements remain indexed by the generator-alignment and reflective-
support witnesses used to construct the rho point.  No unconditional rho
inhabitance is asserted here.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- The lawful total-space projection retains rho's exact selected
finite-support hereditary Cost₁ domain object. -/
@[simp]
theorem rhoHereditaryCostOneElaborationTotal_projection_obj_of
    (alignable : CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel)
    (preservesReflectiveSupport : RhoHereditaryReflectiveSupportPreserving) :
    CostOneElaborationTotal.projection.obj
        (rhoHereditaryCostOneElaborationTotal_of alignable
          preservesReflectiveSupport) =
      (⟨rhoHereditaryCostOneDomainObject_of alignable
        preservesReflectiveSupport⟩ : CostElaborationBase) :=
  rfl

/-- Compact one-step Cost on rho's retained total point is exactly the
compact output of the same finite-support hereditary domain object. -/
@[simp]
theorem rhoHereditaryCostOneElaborationTotal_compactCostOneFunctor_obj_of
    (alignable : CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel)
    (preservesReflectiveSupport : RhoHereditaryReflectiveSupportPreserving) :
    CostOneElaborationTotal.compactCostOneFunctor.obj
        (rhoHereditaryCostOneElaborationTotal_of alignable
          preservesReflectiveSupport) =
      (rhoHereditaryCostOneDomainObject_of alignable
        preservesReflectiveSupport).compactOutput :=
  rfl

/-- Erasing rho's checked hereditary point retains the complete decoration
of the concrete cut-order elaboration used to inhabit its fibre. -/
@[simp]
theorem rhoHereditaryCostOneElaborationTotal_forgetToDecoration_obj_of
    (alignable : CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel)
    (preservesReflectiveSupport : RhoHereditaryReflectiveSupportPreserving) :
    CostOneElaborationTotal.forgetToDecoration.obj
        (rhoHereditaryCostOneElaborationTotal_of alignable
          preservesReflectiveSupport) =
      CostOneDecorationTotal.ofDecoration
        (⟨rhoHereditaryCostOneDomainObject_of alignable
          preservesReflectiveSupport⟩ : CostElaborationBase)
        rhoCostElaborationTotal.fiber.2.decoration :=
  rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
