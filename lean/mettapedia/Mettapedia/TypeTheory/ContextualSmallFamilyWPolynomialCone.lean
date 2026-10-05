import Mettapedia.TypeTheory.ContextualSmallFamilyWPolynomial

/-!
# Full future polynomial comparison with the wider contextual family

Constructed local future inverses compare every original cone polynomial
with the independently formed polynomial of its transported parameter.
The comparison retains the complete branch table and has actual natural
inverse maps.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWPolynomialCone

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyWPolynomial
open ContextualSmallFamilyWCone (futurePoint futureStep nativeRoot_eq)
open PowerClassPresheafBaseChange

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u) (target : base.Elements ⥤ Type u)

noncomputable def coneEquiv (point : base.Elements) (future : Future.Objects point.1) :
    ContextualWPolynomialReindexing.At (signature domain body target point) future ≃ At domain body target (futurePoint point future) :=
  ((ContextualWPolynomialReindexing.pointEquiv (signature domain body target point) (nativeRoot_eq point future).symm).trans
    (ContextualWPolynomialReindexing.pullEquiv (ContextualWLocalChange.prefixChange future.2)
      (signature domain body target point) (ContextualSmallFamilyUniverse.root future.1))).trans
    (ContextualWPolynomialReindexing.signatureEquiv (signature_prefix domain body target (futureStep point future))
      (ContextualSmallFamilyUniverse.root future.1))

theorem coneEquiv_value (point : base.Elements) (future : Future.Objects point.1)
    (node : ContextualWPolynomialReindexing.At (signature domain body target point) future) :
    HEq (coneEquiv domain body target point future node)
      (ContextualWPolynomialReindexing.pullData (ContextualSmallFamilyUniverse.futurePrefix future.2)
        (signature domain body target point) node (ContextualSmallFamilyUniverse.root future.1) (nativeRoot_eq point future)) := by
  let raised := ContextualWPolynomialReindexing.pointEquiv (signature domain body target point) (nativeRoot_eq point future).symm node
  have outer := ContextualWPolynomialReindexing.signatureEquiv_heq
    (signature_prefix domain body target (futureStep point future)) (ContextualSmallFamilyUniverse.root future.1)
    (ContextualWPolynomialReindexing.pullEquiv (ContextualWLocalChange.prefixChange future.2)
      (signature domain body target point) (ContextualSmallFamilyUniverse.root future.1) raised)
  refine outer.trans ?_
  exact ContextualWPolynomialReindexing.pullData_congr rfl rfl rfl raised node
    (ContextualWPolynomialReindexing.pointEquiv_heq (signature domain body target point) (nativeRoot_eq point future).symm node)
    rfl (nativeRoot_eq point future)

theorem coneEquiv_root_heq (point : base.Elements)
    (node : At domain body target point) :
    HEq (coneEquiv domain body target point (ContextualSmallFamilyUniverse.root point.1) node) node := by
  have pulled := ContextualWPolynomialReindexing.pullData_congr (ContextualSmallFamilyUniverse.prefix_id point.1)
    (leftSignature := signature domain body target point) rfl rfl node node HEq.rfl
    (nativeRoot_eq point (ContextualSmallFamilyUniverse.root point.1)) rfl
  exact (coneEquiv_value domain body target point (ContextualSmallFamilyUniverse.root point.1) node).trans
    (pulled.trans (ContextualWPolynomialReindexing.pull_identity (signature domain body target point) _ node))

theorem coneEquiv_natural (point : base.Elements) {first second : Future.Objects point.1}
    (step : first ⟶ second) (tree : ContextualWPolynomialReindexing.At (signature domain body target point) first) :
    pMap domain body target ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).map step)
      (coneEquiv domain body target point first tree) =
    coneEquiv domain body target point second
      ((ContextualWPolynomialReindexing.family (signature domain body target point)).map step tree) := by
  apply eq_of_heq
  let oldSignature := signature domain body target point
  let firstPrefix := ContextualSmallFamilyUniverse.futurePrefix first.2
  let lastPrefix := ContextualSmallFamilyUniverse.futurePrefix step.1
  let firstRoot := ContextualSmallFamilyUniverse.root first.1
  let lastRoot := ContextualSmallFamilyUniverse.root second.1
  have signatureEq := signature_prefix domain body target (futureStep point first)
  have restrictEq := ContextualWPolynomialReindexing.restrict_signature_heq signatureEq.symm
    (ContextualSmallFamilyUniverse.rootArrow step.1)
    (coneEquiv domain body target point first tree)
    (ContextualWPolynomialReindexing.pullData firstPrefix oldSignature tree firstRoot (nativeRoot_eq point first))
    (coneEquiv_value domain body target point first tree)
  have afterCast := ContextualWPolynomialReindexing.pull_congr (first := lastPrefix) rfl signatureEq.symm rfl _ _ restrictEq
  have lastEq : firstPrefix.obj (lastPrefix.obj lastRoot) = second := by
    apply Future.objects_ext (first := firstPrefix.obj (lastPrefix.obj lastRoot)) (second := second) rfl
    exact heq_of_eq ((Category.assoc first.2 step.1 (𝟙 second.1)).symm.trans
      ((congrArg (fun arrow => arrow ≫ 𝟙 second.1) step.2).trans (Category.comp_id second.2)))
  have arrowEq := ContextualSmallFamilyUniverse.futureArrow_heq (nativeRoot_eq point first) lastEq
    (firstPrefix.map (ContextualSmallFamilyUniverse.rootArrow step.1)) step HEq.rfl
  have afterRestriction := ContextualWPolynomialReindexing.pullData_restrict firstPrefix oldSignature
    (ContextualSmallFamilyUniverse.rootArrow step.1) (nativeRoot_eq point first) lastEq step arrowEq tree
  have afterPull := ContextualWPolynomialReindexing.pullData_congr (first := lastPrefix) rfl
    (leftSignature := ContextualWPolynomialReindexing.under firstPrefix oldSignature) rfl rfl _ _
    afterRestriction.symm rfl rfl
  have afterComposition := ContextualWPolynomialReindexing.pull_comp_data lastPrefix firstPrefix oldSignature
    ((ContextualWPolynomialReindexing.family oldSignature).map step tree)
    (lastPrefix.obj lastRoot) lastEq lastRoot rfl
  have contextEq : ContextualSmallFamilyUniverse.futurePrefix second.2 = Cat.compose lastPrefix firstPrefix :=
    (congrArg ContextualSmallFamilyUniverse.futurePrefix step.2.symm).trans
      (ContextualSmallFamilyUniverse.prefix_comp first.2 step.1)
  have compareCombined := ContextualWPolynomialReindexing.pullData_congr contextEq.symm
    (leftSignature := oldSignature) rfl (leftPoint := lastRoot) rfl
    ((ContextualWPolynomialReindexing.family oldSignature).map step tree) _ HEq.rfl
    lastEq (nativeRoot_eq point second)
  exact (pMap_value domain body target ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).map step)
    (coneEquiv domain body target point first tree)).trans
      (afterCast.trans (afterPull.trans (afterComposition.trans
        (compareCombined.trans (coneEquiv_value domain body target point second
          ((ContextualWPolynomialReindexing.family (signature domain body target point)).map step tree)).symm))))

noncomputable def coneReadout (point : base.Elements) :
    NatTrans (ContextualWPolynomialReindexing.family (signature domain body target point))
      (ContextualSmallFamilyUniverse.restrict (ContextualSmallFamilyUniverse.futureElement point.1 point.2)
        (polynomial domain body target)) where
  app future := TypeCat.ofHom (coneEquiv domain body target point future)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro node
    exact (coneEquiv_natural domain body target point step node).symm

noncomputable def coneReadoutInverse (point : base.Elements) :
    NatTrans (ContextualSmallFamilyUniverse.restrict (ContextualSmallFamilyUniverse.futureElement point.1 point.2)
      (polynomial domain body target)) (ContextualWPolynomialReindexing.family (signature domain body target point)) :=
  Nat.inverse (coneReadout domain body target point) (coneEquiv domain body target point) (fun _ _ => rfl)

noncomputable def prefixEquiv {first second : base.Elements} (step : first ⟶ second) (future : Future.Objects second.1) :
    ContextualWPolynomialReindexing.At (signature domain body target first) ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future) ≃
      ContextualWPolynomialReindexing.At (signature domain body target second) future :=
  (ContextualWPolynomialReindexing.pullEquiv (ContextualWLocalChange.prefixChange step.1)
    (signature domain body target first) future).trans
    (ContextualWPolynomialReindexing.signatureEquiv (signature_prefix domain body target step) future)

theorem prefixEquiv_value {first second : base.Elements} (step : first ⟶ second) (future : Future.Objects second.1)
    (tree : ContextualWPolynomialReindexing.At (signature domain body target first) ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future)) :
    HEq (prefixEquiv domain body target step future tree)
      (ContextualWPolynomialReindexing.pull (ContextualSmallFamilyUniverse.futurePrefix step.1) (signature domain body target first) future tree) :=
  ContextualWPolynomialReindexing.signatureEquiv_heq _ _ _

theorem prefix_readout {first second : base.Elements} (step : first ⟶ second) (future : Future.Objects second.1)
    (tree : ContextualWPolynomialReindexing.At (signature domain body target first) ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future)) :
    HEq (coneEquiv domain body target first ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future) tree)
      (coneEquiv domain body target second future (prefixEquiv domain body target step future tree)) := by
  let oldSignature := signature domain body target first
  let firstPrefix := ContextualSmallFamilyUniverse.futurePrefix step.1
  let lastPrefix := ContextualSmallFamilyUniverse.futurePrefix future.2
  let root := ContextualSmallFamilyUniverse.root future.1
  have signatureEq := signature_prefix domain body target step
  have afterCast := ContextualWPolynomialReindexing.pullData_congr (first := lastPrefix) rfl signatureEq.symm rfl
    (prefixEquiv domain body target step future tree)
    (ContextualWPolynomialReindexing.pull firstPrefix oldSignature future tree)
    (prefixEquiv_value domain body target step future tree) (nativeRoot_eq second future) (nativeRoot_eq second future)
  have afterComposition := ContextualWPolynomialReindexing.pull_comp_data lastPrefix firstPrefix oldSignature tree
    future rfl root (nativeRoot_eq second future)
  have compareCombined := ContextualWPolynomialReindexing.pullData_congr
    (ContextualSmallFamilyUniverse.prefix_comp step.1 future.2).symm (leftSignature := oldSignature) rfl
    (leftPoint := root) rfl tree tree HEq.rfl
    (congrArg firstPrefix.obj (nativeRoot_eq second future))
    (nativeRoot_eq first (firstPrefix.obj future))
  exact (coneEquiv_value domain body target first (firstPrefix.obj future) tree).trans
    ((coneEquiv_value domain body target second future (prefixEquiv domain body target step future tree)).trans
      (afterCast.trans (afterComposition.trans compareCombined))).symm

end Mettapedia.TypeTheory.ContextualSmallFamilyWPolynomialCone
