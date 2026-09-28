import Mettapedia.OSLF.Syntax.CartesianModelLexPresheafExtension
import Mettapedia.OSLF.Syntax.CartesianModelLexRepresentability

/-!
# Yoneda-mediated extension of authored cartesian models

An authored model in a small finitely complete target is first embedded
by Yoneda into target presheaves. Its pointwise Set-valued extension is
left-exact. Internal finite-limit generation then proves that every value
of this presheaf extension is representable by a target object. Descent to
a target-valued functor and its coherence is a further construction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits

variable (C : Type) [SmallCategory C] [HasFiniteProducts C]
variable (D : Type) [SmallCategory D] [HasFiniteLimits D]

/-- Yoneda turns a target-valued authored model into a presheaf-valued
authored model while preserving its authored finite products. -/
noncomputable def yonedaOfCartesianTargetModel
    (F : CartesianTargetInterpretations C D) :
    CartesianTargetInterpretations C (Dᵒᵖ ⥤ Type) :=
  ⟨F.1 ⋙ yoneda, by
    have hF : PreservesFiniteProducts F.1 := F.2
    have hY : PreservesFiniteProducts (yoneda : D ⥤ Dᵒᵖ ⥤ Type) :=
      inferInstance
    exact comp_preservesFiniteProducts _ _⟩

/-- The canonical Yoneda-mediated presheaf extension. -/
noncomputable def yonedaPresheafExtension
    (F : CartesianTargetInterpretations C D) :
    LeftExactTargetInterpretations C (Dᵒᵖ ⥤ Type) :=
  extendPresheafAuthoredModel C D (yonedaOfCartesianTargetModel C D F)

/-- Every value of the Yoneda-mediated extension is actually representable:
the restriction comparison establishes the claim on authored contexts,
and left-exactness propagates it through their internal finite-limit
closure. -/
theorem yonedaPresheafExtension_representable
    (F : CartesianTargetInterpretations C D)
    (X : FinitePresentationObjects C) :
    RepresentableTargetPresheaves D
      ((yonedaPresheafExtension C D F).1.obj X) := by
  let Fp := yonedaOfCartesianTargetModel C D F
  let E := yonedaPresheafExtension C D F
  have hbase (Y : C) :
      RepresentableTargetPresheaves D (E.1.obj ((authoredContext C).obj Y)) := by
    have hiso : E.1.obj ((authoredContext C).obj Y) ≅
        (yoneda : D ⥤ Dᵒᵖ ⥤ Type).obj (F.1.obj Y) :=
      (extendPresheafAuthoredModelRestrictionIso C D Fp).app Y
    exact Functor.essImage.ofIso hiso.symm
      (Functor.obj_mem_essImage (yoneda : D ⥤ Dᵒᵖ ⥤ Type) _)
  exact representable_of_authoredContexts C D E hbase X

end Mettapedia.OSLF.CartesianContextModels
