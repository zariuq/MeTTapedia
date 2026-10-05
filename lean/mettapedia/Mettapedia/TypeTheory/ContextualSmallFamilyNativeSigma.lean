import Mettapedia.TypeTheory.ContextualSmallFamilyNativeSlice

/-!
# Contextual dependent sums as actual codomain composition

Nested total coordinates are reassociated naturally, retaining the base,
argument, and result. Composition along the argument projection is left
adjoint to the literal pullback for arbitrary wider slice consumers.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyNativeSigma

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open ContextualNaturalSlices ContextualSmallFamilyTypeFormers ContextualSmallFamilyNativeSlice

universe u v w

variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

def compositeProjection :=
  (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body)).comp
    (ContextualSmallFamilyUniverse.projection domain)

def sumForward : Map (compositeProjection domain body)
    (ContextualSmallFamilyUniverse.projection (sigma domain body)) where
  mapping :=
    { app _ receipt := ⟨receipt.1.1, ⟨receipt.1.2, receipt.2⟩⟩
      naturality _ _ := rfl }
  square _ _ := rfl

def sumBackward : Map (ContextualSmallFamilyUniverse.projection (sigma domain body))
    (compositeProjection domain body) where
  mapping :=
    { app _ receipt := ⟨⟨receipt.1, receipt.2.1⟩, receipt.2.2⟩
      naturality _ _ := rfl }
  square _ _ := rfl

theorem sum_left : (sumForward domain body).comp (sumBackward domain body) =
    Map.identity (compositeProjection domain body) := by
  apply Map.ext
  intro _ _
  rfl

theorem sum_right : (sumBackward domain body).comp (sumForward domain body) =
    Map.identity (ContextualSmallFamilyUniverse.projection (sigma domain body)) := by
  apply Map.ext
  intro _ _
  rfl

variable {X : D ⥤ Type w} (operation : NaturalHom X base)

def compositeCurry (mapping : Map (compositeProjection domain body) operation) :
    Map (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body))
      (pullbackProjection domain operation) where
  mapping :=
    { app point receipt :=
        ⟨(mapping.mapping.app point receipt, receipt.1), mapping.square point receipt⟩
      naturality step receipt := Subtype.ext (Prod.ext
        (mapping.mapping.naturality step receipt) rfl) }
  square _ _ := rfl

def compositeUncurry (mapping : Map
    (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body))
    (pullbackProjection domain operation)) : Map (compositeProjection domain body) operation where
  mapping := mapping.mapping.comp (pullbackFirst operation (ContextualSmallFamilyUniverse.projection domain))
  square point receipt := (mapping.mapping.app point receipt).property.trans
    (congrArg ((ContextualSmallFamilyUniverse.projection domain).app point) (mapping.square point receipt))

theorem composite_uncurry_curry (mapping : Map (compositeProjection domain body) operation) :
    compositeUncurry domain body operation (compositeCurry domain body operation mapping) = mapping := by
  apply Map.ext
  intro _ _
  rfl

theorem composite_curry_uncurry (mapping : Map
    (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body))
    (pullbackProjection domain operation)) :
    compositeCurry domain body operation (compositeUncurry domain body operation mapping) = mapping := by
  apply Map.ext
  intro point receipt
  apply Subtype.ext
  exact Prod.ext rfl (mapping.square point receipt).symm

def sigmaCodomainHomEquiv :
    Map (ContextualSmallFamilyUniverse.projection (sigma domain body)) operation ≃
      Map (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body))
        (pullbackProjection domain operation) where
  toFun mapping := compositeCurry domain body operation ((sumForward domain body).comp mapping)
  invFun mapping := (sumBackward domain body).comp (compositeUncurry domain body operation mapping)
  left_inv mapping := by
    dsimp only
    rw [composite_uncurry_curry, ← Map.assoc, sum_right, Map.identity_comp]
  right_inv mapping := by
    dsimp only
    rw [← Map.assoc, sum_left, Map.identity_comp, composite_curry_uncurry]

theorem sigma_classifies_all_consumers
    (mapping : Map (ContextualSmallFamilyUniverse.projection (sigma domain body)) operation) :
    (sigmaCodomainHomEquiv domain body operation).symm
      (sigmaCodomainHomEquiv domain body operation mapping) = mapping :=
  (sigmaCodomainHomEquiv domain body operation).symm_apply_apply mapping

theorem sigma_retains_selected_coordinates (point : D)
    (receipt : (ContextualSmallFamilyUniverse.total (bodyOnTotal domain body)).obj point) :
    (sumForward domain body).mapping.app point receipt = ⟨receipt.1.1, ⟨receipt.1.2, receipt.2⟩⟩ := rfl

end Mettapedia.TypeTheory.ContextualSmallFamilyNativeSigma
