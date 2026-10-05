import Mettapedia.TypeTheory.ContextualWPolynomialAction
import Mettapedia.TypeTheory.ContextualSmallFamilyWPolynomialCone

/-!
# Full contextual polynomial target maps over wider parameters

Each target map acts on every future branch, while its prefix coherence
retains the actual parameter equation. No global smallness of the
parameter presheaf is required.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWAction

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers
open PowerClassPresheafBaseChange

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable {firstTarget secondTarget : base.Elements ⥤ Type u}

def onCone (operation : NatTrans firstTarget secondTarget) (point : base.Elements) :
    NatTrans (futureDomain firstTarget point) (futureDomain secondTarget point) :=
  ContextualSmallFamilyTypeFormerCoherence.restrictNat
    (ContextualSmallFamilyUniverse.futureElement point.1 point.2) operation

theorem onCone_prefix (operation : NatTrans firstTarget secondTarget)
    {first second : base.Elements} (step : first ⟶ second) :
    HEq (ContextualWPolynomialAction.restrictNat (ContextualSmallFamilyUniverse.futurePrefix step.1)
      (onCone operation first)) (onCone operation second) := by
  apply ContextualWPolynomialAction.nat_ext_heq
    (futureDomain_prefix firstTarget step) (futureDomain_prefix secondTarget step)
  intro future left right values
  exact naturalApplication_heq operation (prefixPoint_eq step future) left right values

def mapValue (operation : NatTrans firstTarget secondTarget) (point : base.Elements)
    (node : ContextualSmallFamilyWPolynomial.At domain body firstTarget point) :
    ContextualSmallFamilyWPolynomial.At domain body secondTarget point :=
  ContextualWPolynomialAction.mapValue (ContextualSmallFamilyWTypes.signature domain body point)
    (onCone operation point) (ContextualSmallFamilyUniverse.root point.1) node

theorem mapValue_natural (operation : NatTrans firstTarget secondTarget)
    {first second : base.Elements} (step : first ⟶ second)
    (node : ContextualSmallFamilyWPolynomial.At domain body firstTarget first) :
    ContextualSmallFamilyWPolynomial.pMap domain body secondTarget step (mapValue domain body operation first node) =
      mapValue domain body operation second (ContextualSmallFamilyWPolynomial.pMap domain body firstTarget step node) := by
  apply eq_of_heq
  let coneChange := ContextualSmallFamilyUniverse.futurePrefix step.1
  let root := ContextualSmallFamilyUniverse.root second.1
  let moved := (ContextualWPolynomialReindexing.family
    (ContextualSmallFamilyWPolynomial.signature domain body firstTarget first)).map
      (ContextualSmallFamilyUniverse.rootArrow step.1) node
  have restricted := ContextualWPolynomialAction.mapValue_restrict
    (ContextualSmallFamilyWTypes.signature domain body first) (onCone operation first)
    (ContextualSmallFamilyUniverse.rootArrow step.1) node
  have afterRestriction := congrArg
    (ContextualWPolynomialReindexing.pull coneChange
      (ContextualSmallFamilyWPolynomial.signature domain body secondTarget first) root) restricted
  have afterPull := ContextualWPolynomialAction.mapValue_pullData coneChange
    (ContextualSmallFamilyWTypes.signature domain body first) (onCone operation first) moved root rfl
  have afterCast := ContextualWPolynomialAction.mapValue_heq
    (ContextualSmallFamilyWTypes.signature_prefix domain body step)
    (futureDomain_prefix firstTarget step) (futureDomain_prefix secondTarget step)
    (ContextualWPolynomialAction.restrictNat coneChange (onCone operation first)) (onCone operation second)
    (onCone_prefix operation step) root
    (ContextualWPolynomialReindexing.pull coneChange
      (ContextualSmallFamilyWPolynomial.signature domain body firstTarget first) root moved)
    (ContextualSmallFamilyWPolynomial.pMap domain body firstTarget step node)
    (ContextualSmallFamilyWPolynomial.pMap_value domain body firstTarget step node).symm
  exact (ContextualSmallFamilyWPolynomial.pMap_value domain body secondTarget step
    (mapValue domain body operation first node)).trans
      ((heq_of_eq afterRestriction).trans ((heq_of_eq afterPull).trans afterCast))

def map (operation : NatTrans firstTarget secondTarget) :
    NatTrans (ContextualSmallFamilyWPolynomial.polynomial domain body firstTarget)
      (ContextualSmallFamilyWPolynomial.polynomial domain body secondTarget) where
  app point := TypeCat.ofHom (mapValue domain body operation point)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro node
    exact (mapValue_natural domain body operation step node).symm

theorem mapValue_coneReadout (operation : NatTrans firstTarget secondTarget) (point : base.Elements)
    (future : Future.Objects point.1)
    (node : ContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWPolynomial.signature domain body firstTarget point) future) :
    HEq (ContextualSmallFamilyWPolynomialCone.coneEquiv domain body secondTarget point future
      (ContextualWPolynomialAction.mapValue (ContextualSmallFamilyWTypes.signature domain body point)
        (onCone operation point) future node))
      (mapValue domain body operation (ContextualSmallFamilyWCone.futurePoint point future)
        (ContextualSmallFamilyWPolynomialCone.coneEquiv domain body firstTarget point future node)) := by
  let coneChange := ContextualSmallFamilyUniverse.futurePrefix future.2
  let root := ContextualSmallFamilyUniverse.root future.1
  let step := ContextualSmallFamilyWCone.futureStep point future
  have afterPull := ContextualWPolynomialAction.mapValue_pullData coneChange
    (ContextualSmallFamilyWTypes.signature domain body point) (onCone operation point) node root
    (ContextualSmallFamilyWCone.nativeRoot_eq point future)
  have afterCast := ContextualWPolynomialAction.mapValue_heq
    (ContextualSmallFamilyWTypes.signature_prefix domain body step)
    (futureDomain_prefix firstTarget step) (futureDomain_prefix secondTarget step)
    (ContextualWPolynomialAction.restrictNat coneChange (onCone operation point))
    (onCone operation (ContextualSmallFamilyWCone.futurePoint point future))
    (onCone_prefix operation step) root
    (ContextualWPolynomialReindexing.pullData coneChange
      (ContextualSmallFamilyWPolynomial.signature domain body firstTarget point) node root
      (ContextualSmallFamilyWCone.nativeRoot_eq point future))
    (ContextualSmallFamilyWPolynomialCone.coneEquiv domain body firstTarget point future node)
    (ContextualSmallFamilyWPolynomialCone.coneEquiv_value domain body firstTarget point future node).symm
  exact (ContextualSmallFamilyWPolynomialCone.coneEquiv_value domain body secondTarget point future
    (ContextualWPolynomialAction.mapValue (ContextualSmallFamilyWTypes.signature domain body point)
      (onCone operation point) future node)).trans ((heq_of_eq afterPull).trans afterCast)

theorem mapValue_identity (point : base.Elements)
    (node : ContextualSmallFamilyWPolynomial.At domain body firstTarget point) :
    mapValue domain body (identityNat firstTarget) point node = node := by
  rcases node with ⟨label, branches⟩
  apply congrArg (Sigma.mk label)
  apply ContextualWTypes.Branches.ext
  intro future arrow position
  rfl

theorem mapValue_composition {thirdTarget : base.Elements ⥤ Type u}
    (first : NatTrans firstTarget secondTarget) (later : NatTrans secondTarget thirdTarget)
    (point : base.Elements) (node : ContextualSmallFamilyWPolynomial.At domain body firstTarget point) :
    mapValue domain body (composeNat first later) point node =
      mapValue domain body later point (mapValue domain body first point node) := by
  rcases node with ⟨label, branches⟩
  apply congrArg (Sigma.mk label)
  apply ContextualWTypes.Branches.ext
  intro future arrow position
  rfl

theorem map_identity : map domain body (identityNat firstTarget) =
    identityNat (ContextualSmallFamilyWPolynomial.polynomial domain body firstTarget) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact mapValue_identity domain body point

theorem map_composition {thirdTarget : base.Elements ⥤ Type u}
    (first : NatTrans firstTarget secondTarget) (later : NatTrans secondTarget thirdTarget) :
    map domain body (composeNat first later) = composeNat (map domain body first) (map domain body later) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact mapValue_composition domain body first later point

end Mettapedia.TypeTheory.ContextualSmallFamilyWAction
