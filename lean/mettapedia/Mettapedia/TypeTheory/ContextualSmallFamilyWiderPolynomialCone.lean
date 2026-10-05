import Mettapedia.TypeTheory.ContextualSmallFamilyWiderPolynomial

/-!
# Wider contextual polynomial readouts on complete future cones

The constructed future inverses compare whole polynomial branch tables,
including arbitrary wider values, with the independently formed family
at the transported parameter. Forward and inverse readouts are natural.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWiderPolynomialCone

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyWiderPolynomial
open ContextualSmallFamilyWCone (futurePoint futureStep nativeRoot_eq)
open PowerClassPresheafBaseChange

universe u v h
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u) (target : base.Elements ⥤ Type h)

def inverseNat {K : Type v} [Category.{u} K] {first second : K ⥤ Type h}
    (operation : NatTrans first second) (fibres : ∀ point, first.obj point ≃ second.obj point)
    (realizes : ∀ point value, operation.app point value = fibres point value) : NatTrans second first where
  app point := TypeCat.ofHom ((fibres point).symm)
  naturality source destination step := by
    apply ConcreteCategory.hom_ext
    intro value
    apply (fibres destination).injective
    have naturally := congrArg (fun function => function ((fibres source).symm value))
      (operation.naturality step)
    change operation.app destination (first.map step ((fibres source).symm value)) =
      second.map step (operation.app source ((fibres source).symm value)) at naturally
    rw [realizes, realizes, (fibres source).apply_symm_apply] at naturally
    exact ((fibres destination).apply_symm_apply _).trans naturally.symm

noncomputable def coneEquiv (point : base.Elements) (future : Future.Objects point.1) :
    WiderContextualWPolynomialReindexing.At (signature domain body target point) future ≃ At domain body target (futurePoint point future) :=
  ((WiderContextualWPolynomialReindexing.pointEquiv (signature domain body target point) (nativeRoot_eq point future).symm).trans
    (WiderContextualWPolynomialReindexing.pullEquiv (ContextualWLocalChange.prefixChange future.2)
      (signature domain body target point) (ContextualSmallFamilyUniverse.root future.1))).trans
    (WiderContextualWPolynomialReindexing.signatureEquiv (signature_prefix domain body target (futureStep point future))
      (ContextualSmallFamilyUniverse.root future.1))

theorem coneEquiv_value (point : base.Elements) (future : Future.Objects point.1)
    (node : WiderContextualWPolynomialReindexing.At (signature domain body target point) future) :
    HEq (coneEquiv domain body target point future node)
      (WiderContextualWPolynomialReindexing.pullData (ContextualSmallFamilyUniverse.futurePrefix future.2)
        (signature domain body target point) node (ContextualSmallFamilyUniverse.root future.1) (nativeRoot_eq point future)) := by
  let raised := WiderContextualWPolynomialReindexing.pointEquiv (signature domain body target point) (nativeRoot_eq point future).symm node
  have outer := WiderContextualWPolynomialReindexing.signatureEquiv_heq
    (signature_prefix domain body target (futureStep point future)) (ContextualSmallFamilyUniverse.root future.1)
    (WiderContextualWPolynomialReindexing.pullEquiv (ContextualWLocalChange.prefixChange future.2)
      (signature domain body target point) (ContextualSmallFamilyUniverse.root future.1) raised)
  refine outer.trans ?_
  exact WiderContextualWPolynomialReindexing.pullData_congr rfl rfl rfl raised node
    (WiderContextualWPolynomialReindexing.pointEquiv_heq (signature domain body target point) (nativeRoot_eq point future).symm node)
    rfl (nativeRoot_eq point future)

theorem coneEquiv_root_heq (point : base.Elements)
    (node : At domain body target point) :
    HEq (coneEquiv domain body target point (ContextualSmallFamilyUniverse.root point.1) node) node := by
  have pulled := WiderContextualWPolynomialReindexing.pullData_congr (ContextualSmallFamilyUniverse.prefix_id point.1)
    (leftSignature := signature domain body target point) rfl rfl node node HEq.rfl
    (nativeRoot_eq point (ContextualSmallFamilyUniverse.root point.1)) rfl
  exact (coneEquiv_value domain body target point (ContextualSmallFamilyUniverse.root point.1) node).trans
    (pulled.trans (WiderContextualWPolynomialReindexing.pull_identity (signature domain body target point) _ node))

theorem coneEquiv_natural (point : base.Elements) {first second : Future.Objects point.1}
    (step : first ⟶ second) (tree : WiderContextualWPolynomialReindexing.At (signature domain body target point) first) :
    pMap domain body target ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).map step)
      (coneEquiv domain body target point first tree) =
    coneEquiv domain body target point second
      ((WiderContextualWPolynomialReindexing.family (signature domain body target point)).map step tree) := by
  apply eq_of_heq
  let oldSignature := signature domain body target point
  let firstPrefix := ContextualSmallFamilyUniverse.futurePrefix first.2
  let lastPrefix := ContextualSmallFamilyUniverse.futurePrefix step.1
  let firstRoot := ContextualSmallFamilyUniverse.root first.1
  let lastRoot := ContextualSmallFamilyUniverse.root second.1
  have signatureEq := signature_prefix domain body target (futureStep point first)
  have restrictEq := WiderContextualWPolynomialReindexing.restrict_signature_heq signatureEq.symm
    (ContextualSmallFamilyUniverse.rootArrow step.1)
    (coneEquiv domain body target point first tree)
    (WiderContextualWPolynomialReindexing.pullData firstPrefix oldSignature tree firstRoot (nativeRoot_eq point first))
    (coneEquiv_value domain body target point first tree)
  have afterCast := WiderContextualWPolynomialReindexing.pull_congr (first := lastPrefix) rfl signatureEq.symm rfl _ _ restrictEq
  have lastEq : firstPrefix.obj (lastPrefix.obj lastRoot) = second := by
    apply Future.objects_ext (first := firstPrefix.obj (lastPrefix.obj lastRoot)) (second := second) rfl
    exact heq_of_eq ((Category.assoc first.2 step.1 (𝟙 second.1)).symm.trans
      ((congrArg (fun arrow => arrow ≫ 𝟙 second.1) step.2).trans (Category.comp_id second.2)))
  have arrowEq := ContextualSmallFamilyUniverse.futureArrow_heq (nativeRoot_eq point first) lastEq
    (firstPrefix.map (ContextualSmallFamilyUniverse.rootArrow step.1)) step HEq.rfl
  have afterRestriction := WiderContextualWPolynomialReindexing.pullData_restrict firstPrefix oldSignature
    (ContextualSmallFamilyUniverse.rootArrow step.1) (nativeRoot_eq point first) lastEq step arrowEq tree
  have afterPull := WiderContextualWPolynomialReindexing.pullData_congr (first := lastPrefix) rfl
    (leftSignature := WiderContextualWPolynomialReindexing.under firstPrefix oldSignature) rfl rfl _ _
    afterRestriction.symm rfl rfl
  have afterComposition := WiderContextualWPolynomialReindexing.pull_comp_data lastPrefix firstPrefix oldSignature
    ((WiderContextualWPolynomialReindexing.family oldSignature).map step tree)
    (lastPrefix.obj lastRoot) lastEq lastRoot rfl
  have contextEq : ContextualSmallFamilyUniverse.futurePrefix second.2 = Cat.compose lastPrefix firstPrefix :=
    (congrArg ContextualSmallFamilyUniverse.futurePrefix step.2.symm).trans
      (ContextualSmallFamilyUniverse.prefix_comp first.2 step.1)
  have compareCombined := WiderContextualWPolynomialReindexing.pullData_congr contextEq.symm
    (leftSignature := oldSignature) rfl (leftPoint := lastRoot) rfl
    ((WiderContextualWPolynomialReindexing.family oldSignature).map step tree) _ HEq.rfl
    lastEq (nativeRoot_eq point second)
  exact (pMap_value domain body target ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).map step)
    (coneEquiv domain body target point first tree)).trans
      (afterCast.trans (afterPull.trans (afterComposition.trans
        (compareCombined.trans (coneEquiv_value domain body target point second
          ((WiderContextualWPolynomialReindexing.family (signature domain body target point)).map step tree)).symm))))

noncomputable def coneReadout (point : base.Elements) :
    NatTrans (WiderContextualWPolynomialReindexing.family (signature domain body target point))
      (ContextualSmallFamilyUniverse.restrict (ContextualSmallFamilyUniverse.futureElement point.1 point.2)
        (polynomial domain body target)) where
  app future := TypeCat.ofHom (coneEquiv domain body target point future)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro node
    exact (coneEquiv_natural domain body target point step node).symm

noncomputable def coneReadoutInverse (point : base.Elements) :
    NatTrans (ContextualSmallFamilyUniverse.restrict (ContextualSmallFamilyUniverse.futureElement point.1 point.2)
      (polynomial domain body target)) (WiderContextualWPolynomialReindexing.family (signature domain body target point)) :=
  inverseNat (coneReadout domain body target point) (coneEquiv domain body target point) (fun _ _ => rfl)

noncomputable def prefixEquiv {first second : base.Elements} (step : first ⟶ second) (future : Future.Objects second.1) :
    WiderContextualWPolynomialReindexing.At (signature domain body target first) ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future) ≃
      WiderContextualWPolynomialReindexing.At (signature domain body target second) future :=
  (WiderContextualWPolynomialReindexing.pullEquiv (ContextualWLocalChange.prefixChange step.1)
    (signature domain body target first) future).trans
    (WiderContextualWPolynomialReindexing.signatureEquiv (signature_prefix domain body target step) future)

theorem prefixEquiv_value {first second : base.Elements} (step : first ⟶ second) (future : Future.Objects second.1)
    (tree : WiderContextualWPolynomialReindexing.At (signature domain body target first) ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future)) :
    HEq (prefixEquiv domain body target step future tree)
      (WiderContextualWPolynomialReindexing.pull (ContextualSmallFamilyUniverse.futurePrefix step.1) (signature domain body target first) future tree) :=
  WiderContextualWPolynomialReindexing.signatureEquiv_heq _ _ _

theorem prefix_readout {first second : base.Elements} (step : first ⟶ second) (future : Future.Objects second.1)
    (tree : WiderContextualWPolynomialReindexing.At (signature domain body target first) ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future)) :
    HEq (coneEquiv domain body target first ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future) tree)
      (coneEquiv domain body target second future (prefixEquiv domain body target step future tree)) := by
  let oldSignature := signature domain body target first
  let firstPrefix := ContextualSmallFamilyUniverse.futurePrefix step.1
  let lastPrefix := ContextualSmallFamilyUniverse.futurePrefix future.2
  let root := ContextualSmallFamilyUniverse.root future.1
  have signatureEq := signature_prefix domain body target step
  have afterCast := WiderContextualWPolynomialReindexing.pullData_congr (first := lastPrefix) rfl signatureEq.symm rfl
    (prefixEquiv domain body target step future tree)
    (WiderContextualWPolynomialReindexing.pull firstPrefix oldSignature future tree)
    (prefixEquiv_value domain body target step future tree) (nativeRoot_eq second future) (nativeRoot_eq second future)
  have afterComposition := WiderContextualWPolynomialReindexing.pull_comp_data lastPrefix firstPrefix oldSignature tree
    future rfl root (nativeRoot_eq second future)
  have compareCombined := WiderContextualWPolynomialReindexing.pullData_congr
    (ContextualSmallFamilyUniverse.prefix_comp step.1 future.2).symm (leftSignature := oldSignature) rfl
    (leftPoint := root) rfl tree tree HEq.rfl
    (congrArg firstPrefix.obj (nativeRoot_eq second future))
    (nativeRoot_eq first (firstPrefix.obj future))
  exact (coneEquiv_value domain body target first (firstPrefix.obj future) tree).trans
    ((coneEquiv_value domain body target second future (prefixEquiv domain body target step future tree)).trans
      (afterCast.trans (afterComposition.trans compareCombined))).symm


end Mettapedia.TypeTheory.ContextualSmallFamilyWiderPolynomialCone
