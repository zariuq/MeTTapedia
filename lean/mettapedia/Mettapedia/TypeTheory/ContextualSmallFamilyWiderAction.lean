import Mettapedia.TypeTheory.WiderContextualWPolynomialAction
import Mettapedia.TypeTheory.ContextualSmallFamilyWiderPolynomialCone
import Mettapedia.TypeTheory.ContextualSmallFamilyNativeAdjunction

/-!
# Cross-universe contextual polynomial target action

A natural consumer map acts on the complete future branch tables. Its
actual prefix coherence retains the parameter equations and all positions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWiderAction

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers
open ContextualSmallFamilyWiderPolynomial (futureTarget futureTarget_prefix)
open PowerClassPresheafBaseChange

universe u v h k l
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable {firstTarget : base.Elements ⥤ Type h} {secondTarget : base.Elements ⥤ Type k}

def onCone (operation : WiderPresheafDependentFunctions.Hom firstTarget secondTarget) (point : base.Elements) :
    WiderPresheafDependentFunctions.Hom (futureTarget firstTarget point) (futureTarget secondTarget point) :=
  WiderContextualWPolynomialAction.restrictNat
    (ContextualSmallFamilyUniverse.futureElement point.1 point.2) operation

theorem onCone_prefix (operation : WiderPresheafDependentFunctions.Hom firstTarget secondTarget)
    {first second : base.Elements} (step : first ⟶ second) :
    HEq (WiderContextualWPolynomialAction.restrictNat (ContextualSmallFamilyUniverse.futurePrefix step.1)
      (onCone operation first)) (onCone operation second) := by
  apply WiderContextualWPolynomialAction.nat_ext_heq
    (futureTarget_prefix firstTarget step) (futureTarget_prefix secondTarget step)
  intro future left right values
  exact ContextualSmallFamilyNativeAdjunction.homApplication_heq operation (prefixPoint_eq step future) left right values

def mapValue (operation : WiderPresheafDependentFunctions.Hom firstTarget secondTarget) (point : base.Elements)
    (node : ContextualSmallFamilyWiderPolynomial.At domain body firstTarget point) :
    ContextualSmallFamilyWiderPolynomial.At domain body secondTarget point :=
  WiderContextualWPolynomialAction.mapValue (ContextualSmallFamilyWTypes.signature domain body point)
    (onCone operation point) (ContextualSmallFamilyUniverse.root point.1) node

theorem mapValue_natural (operation : WiderPresheafDependentFunctions.Hom firstTarget secondTarget)
    {first second : base.Elements} (step : first ⟶ second)
    (node : ContextualSmallFamilyWiderPolynomial.At domain body firstTarget first) :
    ContextualSmallFamilyWiderPolynomial.pMap domain body secondTarget step (mapValue domain body operation first node) =
      mapValue domain body operation second (ContextualSmallFamilyWiderPolynomial.pMap domain body firstTarget step node) := by
  apply eq_of_heq
  let coneChange := ContextualSmallFamilyUniverse.futurePrefix step.1
  let root := ContextualSmallFamilyUniverse.root second.1
  let moved := (WiderContextualWPolynomialReindexing.family
    (ContextualSmallFamilyWiderPolynomial.signature domain body firstTarget first)).map
      (ContextualSmallFamilyUniverse.rootArrow step.1) node
  have restricted := WiderContextualWPolynomialAction.mapValue_restrict
    (ContextualSmallFamilyWTypes.signature domain body first) (onCone operation first)
    (ContextualSmallFamilyUniverse.rootArrow step.1) node
  have afterRestriction := congrArg
    (WiderContextualWPolynomialReindexing.pull coneChange
      (ContextualSmallFamilyWiderPolynomial.signature domain body secondTarget first) root) restricted
  have afterPull := WiderContextualWPolynomialAction.mapValue_pullData coneChange
    (ContextualSmallFamilyWTypes.signature domain body first) (onCone operation first) moved root rfl
  have afterCast := WiderContextualWPolynomialAction.mapValue_heq
    (ContextualSmallFamilyWTypes.signature_prefix domain body step)
    (futureTarget_prefix firstTarget step) (futureTarget_prefix secondTarget step)
    (WiderContextualWPolynomialAction.restrictNat coneChange (onCone operation first)) (onCone operation second)
    (onCone_prefix operation step) root
    (WiderContextualWPolynomialReindexing.pull coneChange
      (ContextualSmallFamilyWiderPolynomial.signature domain body firstTarget first) root moved)
    (ContextualSmallFamilyWiderPolynomial.pMap domain body firstTarget step node)
    (ContextualSmallFamilyWiderPolynomial.pMap_value domain body firstTarget step node).symm
  exact (ContextualSmallFamilyWiderPolynomial.pMap_value domain body secondTarget step
    (mapValue domain body operation first node)).trans
      ((heq_of_eq afterRestriction).trans ((heq_of_eq afterPull).trans afterCast))

def map (operation : WiderPresheafDependentFunctions.Hom firstTarget secondTarget) :
    WiderPresheafDependentFunctions.Hom (ContextualSmallFamilyWiderPolynomial.polynomial domain body firstTarget)
      (ContextualSmallFamilyWiderPolynomial.polynomial domain body secondTarget) where
  app point := mapValue domain body operation point
  naturality step node := mapValue_natural domain body operation step node

theorem mapValue_coneReadout (operation : WiderPresheafDependentFunctions.Hom firstTarget secondTarget) (point : base.Elements)
    (future : Future.Objects point.1)
    (node : WiderContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWiderPolynomial.signature domain body firstTarget point) future) :
    HEq (ContextualSmallFamilyWiderPolynomialCone.coneEquiv domain body secondTarget point future
      (WiderContextualWPolynomialAction.mapValue (ContextualSmallFamilyWTypes.signature domain body point)
        (onCone operation point) future node))
      (mapValue domain body operation (ContextualSmallFamilyWCone.futurePoint point future)
        (ContextualSmallFamilyWiderPolynomialCone.coneEquiv domain body firstTarget point future node)) := by
  let coneChange := ContextualSmallFamilyUniverse.futurePrefix future.2
  let root := ContextualSmallFamilyUniverse.root future.1
  let step := ContextualSmallFamilyWCone.futureStep point future
  have afterPull := WiderContextualWPolynomialAction.mapValue_pullData coneChange
    (ContextualSmallFamilyWTypes.signature domain body point) (onCone operation point) node root
    (ContextualSmallFamilyWCone.nativeRoot_eq point future)
  have afterCast := WiderContextualWPolynomialAction.mapValue_heq
    (ContextualSmallFamilyWTypes.signature_prefix domain body step)
    (futureTarget_prefix firstTarget step) (futureTarget_prefix secondTarget step)
    (WiderContextualWPolynomialAction.restrictNat coneChange (onCone operation point))
    (onCone operation (ContextualSmallFamilyWCone.futurePoint point future))
    (onCone_prefix operation step) root
    (WiderContextualWPolynomialReindexing.pullData coneChange
      (ContextualSmallFamilyWiderPolynomial.signature domain body firstTarget point) node root
      (ContextualSmallFamilyWCone.nativeRoot_eq point future))
    (ContextualSmallFamilyWiderPolynomialCone.coneEquiv domain body firstTarget point future node)
    (ContextualSmallFamilyWiderPolynomialCone.coneEquiv_value domain body firstTarget point future node).symm
  exact (ContextualSmallFamilyWiderPolynomialCone.coneEquiv_value domain body secondTarget point future
    (WiderContextualWPolynomialAction.mapValue (ContextualSmallFamilyWTypes.signature domain body point)
      (onCone operation point) future node)).trans ((heq_of_eq afterPull).trans afterCast)

theorem mapValue_identity (point : base.Elements)
    (node : ContextualSmallFamilyWiderPolynomial.At domain body firstTarget point) :
    mapValue domain body (WiderPresheafDependentFunctions.Hom.identity firstTarget) point node = node := by
  rcases node with ⟨label, branches⟩
  apply congrArg (Sigma.mk label)
  apply WiderContextualWAlgebras.Branches.ext
  intro future arrow position
  rfl

theorem mapValue_composition {thirdTarget : base.Elements ⥤ Type l}
    (first : WiderPresheafDependentFunctions.Hom firstTarget secondTarget) (later : WiderPresheafDependentFunctions.Hom secondTarget thirdTarget)
    (point : base.Elements) (node : ContextualSmallFamilyWiderPolynomial.At domain body firstTarget point) :
    mapValue domain body (first.comp later) point node =
      mapValue domain body later point (mapValue domain body first point node) := by
  rcases node with ⟨label, branches⟩
  apply congrArg (Sigma.mk label)
  apply WiderContextualWAlgebras.Branches.ext
  intro future arrow position
  rfl

theorem map_identity : map domain body (WiderPresheafDependentFunctions.Hom.identity firstTarget) =
    WiderPresheafDependentFunctions.Hom.identity (ContextualSmallFamilyWiderPolynomial.polynomial domain body firstTarget) := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point node
  exact mapValue_identity domain body point node

theorem map_composition {thirdTarget : base.Elements ⥤ Type l}
    (first : WiderPresheafDependentFunctions.Hom firstTarget secondTarget) (later : WiderPresheafDependentFunctions.Hom secondTarget thirdTarget) :
    map domain body (first.comp later) = (map domain body first).comp (map domain body later) := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point node
  exact mapValue_composition domain body first later point node


end Mettapedia.TypeTheory.ContextualSmallFamilyWiderAction
