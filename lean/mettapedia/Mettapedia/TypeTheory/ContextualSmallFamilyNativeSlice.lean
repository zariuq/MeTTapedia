import Mettapedia.TypeTheory.ContextualNaturalSlices

/-!
# Original-bound dependent products in actual contextual slices

The source of a slice consumer may be arbitrarily wider. Its actual fibre
family, the literal pullback, and the reassociated comprehension coordinates
are compared by explicit inverse natural maps. The resulting codomain
product universal property retains original source values and all future
arguments while the function fibres stay in the original context universe.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyNativeSlice

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open ContextualNaturalSlices ContextualSmallFamilyTypeFormers

universe u v w h k

variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

def reindexHom {E : Type v} {K : Type w} [Category.{u} E] [Category.{u} K]
    (change : K ⥤ E) {first : E ⥤ Type h} {second : E ⥤ Type k}
    (operation : WiderPresheafDependentFunctions.Hom first second) :
    WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.restrict change first)
      (WiderPresheafDependentFunctions.restrict change second) where
  app point := operation.app (change.obj point)
  naturality step value := operation.naturality (change.map step) value

def flattenHom {first : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type h}
    {second : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type k}
    (operation : WiderPresheafDependentFunctions.Hom first second) :
    WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.restrict (ContextualSmallFamilyComprehension.flatten domain) first)
      (WiderPresheafDependentFunctions.restrict (ContextualSmallFamilyComprehension.flatten domain) second) :=
  reindexHom (ContextualSmallFamilyComprehension.flatten domain) operation

def unflattenHom {first : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type h}
    {second : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type k}
    (operation : WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.restrict (ContextualSmallFamilyComprehension.flatten domain) first)
      (WiderPresheafDependentFunctions.restrict (ContextualSmallFamilyComprehension.flatten domain) second)) :
    WiderPresheafDependentFunctions.Hom first second where
  app point value := operation.app ((ContextualSmallFamilyComprehension.unflatten domain).obj point) value
  naturality step value := operation.naturality ((ContextualSmallFamilyComprehension.unflatten domain).map step) value

theorem unflatten_flattenHom
    {first : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type h}
    {second : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type k}
    (operation : WiderPresheafDependentFunctions.Hom first second) :
    unflattenHom domain (flattenHom domain operation) = operation := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point value
  rfl

theorem flatten_unflattenHom
    {first : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type h}
    {second : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type k}
    (operation : WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.restrict (ContextualSmallFamilyComprehension.flatten domain) first)
      (WiderPresheafDependentFunctions.restrict (ContextualSmallFamilyComprehension.flatten domain) second)) :
    flattenHom domain (unflattenHom domain operation) = operation := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point value
  rfl

def flattenHomEquiv
    (first : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type h)
    (second : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type k) :
    WiderPresheafDependentFunctions.Hom first second ≃
      WiderPresheafDependentFunctions.Hom
        (WiderPresheafDependentFunctions.restrict (ContextualSmallFamilyComprehension.flatten domain) first)
        (WiderPresheafDependentFunctions.restrict (ContextualSmallFamilyComprehension.flatten domain) second) where
  toFun := flattenHom domain
  invFun := unflattenHom domain
  left_inv := unflatten_flattenHom domain
  right_inv := flatten_unflattenHom domain

def bodyOnTotal : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u :=
  WiderPresheafDependentFunctions.restrict (ContextualSmallFamilyComprehension.unflatten domain) body

variable {X : D ⥤ Type w} (operation : NaturalHom X base)

abbrev pullbackFamily := pullback operation (ContextualSmallFamilyUniverse.projection domain)

abbrev pullbackProjection := pullbackSecond operation (ContextualSmallFamilyUniverse.projection domain)

def pullbackBodyToFamily
    (mapping : Map (pullbackProjection domain operation)
      (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body))) :
    WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.over domain (fibres operation)) body := by
  let fibreBody := fromTotal (pullbackProjection domain operation) (bodyOnTotal domain body) mapping
  let changed := (pullbackFibreBackward operation (ContextualSmallFamilyUniverse.projection domain)).comp fibreBody
  exact flattenHom domain changed

def familyBodyToPullback
    (mapping : WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.over domain (fibres operation)) body) :
    Map (pullbackProjection domain operation)
      (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body)) := by
  let expanded := unflattenHom domain (first :=
    WiderPresheafDependentFunctions.restrict
      (ContextualSmallFamilyUniverse.elementMap (ContextualSmallFamilyUniverse.projection domain)) (fibres operation))
    (second := bodyOnTotal domain body) mapping
  exact toTotal (pullbackProjection domain operation) (bodyOnTotal domain body)
    ((pullbackFibreForward operation (ContextualSmallFamilyUniverse.projection domain)).comp expanded)

theorem family_pullback_left
    (mapping : Map (pullbackProjection domain operation)
      (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body))) :
    familyBodyToPullback domain body operation (pullbackBodyToFamily domain body operation mapping) = mapping := by
  unfold familyBodyToPullback pullbackBodyToFamily
  dsimp only
  rw [unflatten_flattenHom]
  rw [← WiderPresheafDependentFunctions.Hom.assoc, pullback_fibre_left,
    WiderPresheafDependentFunctions.Hom.identity_comp]
  exact to_fromTotal _ _ mapping

theorem family_pullback_right
    (mapping : WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.over domain (fibres operation)) body) :
    pullbackBodyToFamily domain body operation (familyBodyToPullback domain body operation mapping) = mapping := by
  unfold familyBodyToPullback pullbackBodyToFamily
  dsimp only
  rw [from_toTotal, ← WiderPresheafDependentFunctions.Hom.assoc, pullback_fibre_right,
    WiderPresheafDependentFunctions.Hom.identity_comp]
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point value
  rfl

def pullbackBodyEquiv :
    Map (pullbackProjection domain operation)
      (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body)) ≃
    WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.over domain (fibres operation)) body where
  toFun := pullbackBodyToFamily domain body operation
  invFun := familyBodyToPullback domain body operation
  left_inv := family_pullback_left domain body operation
  right_inv := family_pullback_right domain body operation

def codomainHomEquiv :
    Map (pullbackProjection domain operation)
      (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body)) ≃
      Map operation (ContextualSmallFamilyUniverse.projection (pi domain body)) :=
  (pullbackBodyEquiv domain body operation).trans
    ((ContextualSmallFamilyNativeAdjunction.smallHomEquiv domain body (fibres operation)).trans
      (totalHomEquiv operation (pi domain body)))

def transpose
    (mapping : Map (pullbackProjection domain operation)
      (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body))) :
    Map operation (ContextualSmallFamilyUniverse.projection (pi domain body)) :=
  codomainHomEquiv domain body operation mapping

def application
    (mapping : Map operation (ContextualSmallFamilyUniverse.projection (pi domain body))) :
    Map (pullbackProjection domain operation)
      (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body)) :=
  (codomainHomEquiv domain body operation).symm mapping

theorem beta
    (mapping : Map (pullbackProjection domain operation)
      (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body))) :
    application domain body operation (transpose domain body operation mapping) = mapping :=
  (codomainHomEquiv domain body operation).symm_apply_apply mapping

theorem eta (mapping : Map operation (ContextualSmallFamilyUniverse.projection (pi domain body))) :
    transpose domain body operation (application domain body operation mapping) = mapping :=
  (codomainHomEquiv domain body operation).apply_symm_apply mapping

theorem transpose_unique
    (mapping : Map (pullbackProjection domain operation)
      (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body)))
    (candidate : Map operation (ContextualSmallFamilyUniverse.projection (pi domain body)))
    (computes : application domain body operation candidate = mapping) :
    candidate = transpose domain body operation mapping := by
  rw [← computes, eta]

theorem application_value
    (mapping : Map operation (ContextualSmallFamilyUniverse.projection (pi domain body)))
    (point : domain.Elements) (receipt : Fibre operation point.1.1 point.1.2) :
    (application domain body operation mapping).mapping.app point.1.1
      ⟨(receipt.val, (ContextualSmallFamilyComprehension.flatten domain |>.obj point).2), receipt.property⟩ =
      ⟨(ContextualSmallFamilyComprehension.flatten domain |>.obj point).2,
        evaluateValue domain body point.1
          ((fromTotal operation (pi domain body) mapping).app point.1 receipt) point.2⟩ := rfl

def evaluation : Map
    (pullbackProjection domain (ContextualSmallFamilyUniverse.projection (pi domain body)))
    (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body)) :=
  application domain body (ContextualSmallFamilyUniverse.projection (pi domain body))
    (Map.identity (ContextualSmallFamilyUniverse.projection (pi domain body)))

theorem evaluation_value (point : domain.Elements) (term : ProductAt domain body point.1) :
    (evaluation domain body).mapping.app point.1.1
      ⟨(⟨point.1.2, term⟩, (ContextualSmallFamilyComprehension.flatten domain |>.obj point).2), rfl⟩ =
      ⟨(ContextualSmallFamilyComprehension.flatten domain |>.obj point).2,
        evaluateValue domain body point.1 term point.2⟩ := rfl

theorem application_counit
    (mapping : Map operation (ContextualSmallFamilyUniverse.projection (pi domain body))) :
    (pullbackMap mapping (ContextualSmallFamilyUniverse.projection domain)).comp
      (evaluation domain body) = application domain body operation mapping := by
  apply Map.ext
  intro point pair
  rcases pair with ⟨⟨value, ⟨parameter, argument⟩⟩, saved⟩
  change operation.app point value = parameter at saved
  subst parameter
  have matched : mapping.mapping.app point value =
      ⟨operation.app point value,
        (fromTotal operation (pi domain body) mapping).app
          ⟨point, operation.app point value⟩ ⟨value, rfl⟩⟩ := by
    exact (congrArg (fun map => map.mapping.app point value)
      (to_fromTotal operation (pi domain body) mapping)).symm
  change (evaluation domain body).mapping.app point
      ⟨(mapping.mapping.app point value, ⟨operation.app point value, argument⟩), _⟩ = _
  have samePair :
      (⟨(mapping.mapping.app point value, ⟨operation.app point value, argument⟩),
        mapping.square point value⟩ :
          (pullbackFamily domain (ContextualSmallFamilyUniverse.projection (pi domain body))).obj point) =
        ⟨(⟨operation.app point value,
          (fromTotal operation (pi domain body) mapping).app
            ⟨point, operation.app point value⟩ ⟨value, rfl⟩⟩,
          ⟨operation.app point value, argument⟩), rfl⟩ :=
    Subtype.ext (Prod.ext matched rfl)
  exact congrArg ((evaluation domain body).mapping.app point) samePair

theorem codomain_beta
    (mapping : Map (pullbackProjection domain operation)
      (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body))) :
    (pullbackMap (transpose domain body operation mapping)
      (ContextualSmallFamilyUniverse.projection domain)).comp (evaluation domain body) = mapping := by
  rw [application_counit, beta]

theorem codomain_eta
    (mapping : Map operation (ContextualSmallFamilyUniverse.projection (pi domain body))) :
    transpose domain body operation
      ((pullbackMap mapping (ContextualSmallFamilyUniverse.projection domain)).comp
        (evaluation domain body)) = mapping := by
  rw [application_counit, eta]

theorem application_natural_source {Y : D ⥤ Type h} (other : NaturalHom Y base)
    (earlier : Map other operation)
    (mapping : Map operation (ContextualSmallFamilyUniverse.projection (pi domain body))) :
    application domain body other (earlier.comp mapping) =
      (pullbackMap earlier (ContextualSmallFamilyUniverse.projection domain)).comp
        (application domain body operation mapping) := by
  rw [← application_counit, pullbackMap_comp, Map.assoc, application_counit]

theorem transpose_natural_source {Y : D ⥤ Type h} (other : NaturalHom Y base)
    (earlier : Map other operation)
    (mapping : Map (pullbackProjection domain operation)
      (ContextualSmallFamilyUniverse.projection (bodyOnTotal domain body))) :
    transpose domain body other
      ((pullbackMap earlier (ContextualSmallFamilyUniverse.projection domain)).comp mapping) =
      earlier.comp (transpose domain body operation mapping) := by
  apply (codomainHomEquiv domain body other).symm.injective
  change application domain body other _ = application domain body other _
  rw [beta, application_natural_source, beta]

end Mettapedia.TypeTheory.ContextualSmallFamilyNativeSlice
