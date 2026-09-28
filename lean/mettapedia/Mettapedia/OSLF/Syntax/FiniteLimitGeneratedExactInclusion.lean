import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedContextEmbedding
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite

/-!
# Finite limits computed by the generated presheaf inclusion

Closing represented contexts under terminal objects, binary products and
equalizers makes the generated full subcategory finitely complete. The same
closure is stable under every finite product. Its inclusion into presheaves
therefore creates and preserves every finite limit, rather than only the three
generating shapes. This identifies the exact ambient limits used by the
generated category without claiming a free-extension universal property.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding

open CategoryTheory
open CategoryTheory.Limits

variable (S : Signature)

/-- Closure under the two product generators implies closure under all finite
products of ambient presheaves. -/
theorem finiteLimitGenerated_closedUnderFiniteProducts :
    (finiteLimitGenerated S).IsClosedUnderFiniteProducts :=
  Mettapedia.OSLF.FiniteLimitYoneda.closedUnderFiniteProducts (Syntactic.Ctxt S)

@[instance_reducible]
noncomputable def finiteLimitGenerated_inclusionCreatesFiniteProducts :
    CreatesFiniteProducts (finiteLimitGenerated S).ι :=
  Mettapedia.OSLF.FiniteLimitYoneda.inclusionCreatesFiniteProducts
    (Syntactic.Ctxt S)

@[instance_reducible]
noncomputable def finiteLimitGenerated_inclusionCreatesFiniteLimits :
    CreatesFiniteLimits (finiteLimitGenerated S).ι :=
  Mettapedia.OSLF.FiniteLimitYoneda.inclusionCreatesFiniteLimits
    (Syntactic.Ctxt S)

theorem finiteLimitGenerated_inclusionPreservesFiniteLimits :
    PreservesFiniteLimits (finiteLimitGenerated S).ι :=
  Mettapedia.OSLF.FiniteLimitYoneda.inclusionPreservesFiniteLimits
    (Syntactic.Ctxt S)

end Mettapedia.OSLF.Binding

namespace Mettapedia.OSLF.Binding.UnaryContextBoundary

open CategoryTheory
open CategoryTheory.Limits

/-- The formal fixed-point equalizer inside the generated finitely complete
subcategory. -/
noncomputable def generatedFixedPoint :
    (finiteLimitGenerated signature).FullSubcategory :=
  equalizer ((contextIntoFiniteLimitGenerated signature).map (𝟙 one))
    ((contextIntoFiniteLimitGenerated signature).map nextArrow)

/-- The generated equalizer is exactly the previously identified empty
presheaf equalizer after inclusion, up to the canonical limit isomorphism. -/
noncomputable def generatedFixedPoint_ambientIso :
    (finiteLimitGenerated signature).ι.obj generatedFixedPoint ≅
      fixedPointPresheaf := by
  have : PreservesFiniteLimits (finiteLimitGenerated signature).ι :=
    finiteLimitGenerated_inclusionPreservesFiniteLimits signature
  let diagram := parallelPair
    ((contextIntoFiniteLimitGenerated signature).map (𝟙 one))
    ((contextIntoFiniteLimitGenerated signature).map nextArrow)
  let comparison : diagram ⋙ (finiteLimitGenerated signature).ι ≅
      parallelPair yonedaIdentity yonedaNext := by
    refine parallelPair.ext
      (F := diagram ⋙ (finiteLimitGenerated signature).ι)
      (G := parallelPair yonedaIdentity yonedaNext)
      (Iso.refl _) (Iso.refl _) ?_ ?_
    · change yoneda.map (𝟙 one) ≫ 𝟙 (yoneda.obj one) =
        𝟙 (yoneda.obj one) ≫ yonedaIdentity
      simp [yonedaIdentity]
    · change yoneda.map nextArrow ≫ 𝟙 (yoneda.obj one) =
        𝟙 (yoneda.obj one) ≫ yonedaNext
      simp [yonedaNext]
  exact (preservesLimitIso (finiteLimitGenerated signature).ι diagram).trans
    (HasLimit.isoOfNatIso comparison)

/-- The generated fixed-point equalizer is an initial object of this concrete
finite-limit-generated category. -/
noncomputable def generatedFixedPoint_isInitial :
    IsInitial generatedFixedPoint := by
  let ambientInitial : IsInitial
      ((finiteLimitGenerated signature).ι.obj generatedFixedPoint) :=
    fixedPointPresheaf_isInitial.ofIso generatedFixedPoint_ambientIso.symm
  apply IsInitial.ofUniqueHom
    (fun target => ObjectProperty.homMk (ambientInitial.to target.obj))
  intro target arrow
  apply ObjectProperty.hom_ext
  exact ambientInitial.hom_ext arrow.hom (ambientInitial.to target.obj)

/-- The added initial equalizer is not disguised as any original context. -/
theorem generatedFixedPoint_not_rawContext :
    ¬ ∃ Γ : Syntactic.Ctxt signature,
      Nonempty (generatedFixedPoint ≅
        (contextIntoFiniteLimitGenerated signature).obj Γ) := by
  rintro ⟨Γ, ⟨e⟩⟩
  exact fixedPointPresheaf_not_representable
    ⟨Γ, ⟨generatedFixedPoint_ambientIso.symm ≪≫
      (finiteLimitGenerated signature).ι.mapIso e⟩⟩

end Mettapedia.OSLF.Binding.UnaryContextBoundary
