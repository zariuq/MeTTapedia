import Mettapedia.TypeTheory.ContextualSmallFamilyWTypes

/-!
# Actual W readout from small future cones

At every retained future point, the original cone-tree fibre is
constructively equivalent to the independently formed W fibre of the
transported parameter. The inverse is indexed tree recursion through
constructed local future inverses, not a selected representative.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWCone

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyWTypes
open PowerClassPresheafBaseChange

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

def futurePoint (point : base.Elements) (future : Future.Objects point.1) : base.Elements :=
  (ContextualSmallFamilyUniverse.futureElement point.1 point.2).obj future

def futureStep (point : base.Elements) (future : Future.Objects point.1) : point ⟶ futurePoint point future :=
  CategoryOfElements.homMk _ _ future.2 rfl

theorem nativeRoot_eq (point : base.Elements) (future : Future.Objects point.1) :
    (ContextualSmallFamilyUniverse.futurePrefix future.2).obj
      (ContextualSmallFamilyUniverse.root future.1) = future :=
  Future.objects_ext rfl (heq_of_eq (Category.comp_id future.2))

noncomputable def coneEquiv (point : base.Elements) (future : Future.Objects point.1) :
    ContextualWReindexing.Tree (signature domain body point) future ≃ WAt domain body (futurePoint point future) :=
  ((ContextualWReindexing.pointEquiv (signature domain body point) (nativeRoot_eq point future).symm).trans
    (ContextualWLocalChange.naturalEquiv (ContextualWLocalChange.prefixChange future.2)
      (futureDomain domain point) (futureBody domain body point) (ContextualSmallFamilyUniverse.root future.1))).trans
    (ContextualWReindexing.signatureEquiv (signature_prefix domain body (futureStep point future))
      (ContextualSmallFamilyUniverse.root future.1))

theorem coneEquiv_raw (point : base.Elements) (future : Future.Objects point.1)
    (tree : ContextualWReindexing.Tree (signature domain body point) future) :
    HEq (coneEquiv domain body point future tree).val
      (ContextualWReindexing.pullData (ContextualSmallFamilyUniverse.futurePrefix future.2)
        (signature domain body point) tree.val (ContextualSmallFamilyUniverse.root future.1) (nativeRoot_eq point future)) := by
  let raised := ContextualWReindexing.pointEquiv (signature domain body point) (nativeRoot_eq point future).symm tree
  have outer := ContextualWReindexing.signatureEquiv_raw
    (signature_prefix domain body (futureStep point future)) (ContextualSmallFamilyUniverse.root future.1)
    (ContextualWLocalChange.naturalEquiv (ContextualWLocalChange.prefixChange future.2)
      (futureDomain domain point) (futureBody domain body point) (ContextualSmallFamilyUniverse.root future.1) raised)
  refine outer.trans ?_
  exact ContextualWReindexing.pullData_congr rfl rfl rfl raised.val tree.val
    (ContextualWReindexing.pointEquiv_raw (signature domain body point) (nativeRoot_eq point future).symm tree)
    rfl (nativeRoot_eq point future)

theorem coneEquiv_root_raw (point : base.Elements) (tree : WAt domain body point) :
    HEq (coneEquiv domain body point (ContextualSmallFamilyUniverse.root point.1) tree).val tree.val := by
  have pulled := ContextualWReindexing.pullData_congr (ContextualSmallFamilyUniverse.prefix_id point.1)
    (leftSignature := signature domain body point) rfl rfl tree.val tree.val HEq.rfl
    (nativeRoot_eq point (ContextualSmallFamilyUniverse.root point.1)) rfl
  exact (coneEquiv_raw domain body point (ContextualSmallFamilyUniverse.root point.1) tree).trans
    (pulled.trans (ContextualWReindexing.pull_identity (signature domain body point) _ tree.val))

theorem coneEquiv_natural (point : base.Elements) {first second : Future.Objects point.1}
    (step : first ⟶ second) (tree : ContextualWReindexing.Tree (signature domain body point) first) :
    wMap domain body ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).map step)
      (coneEquiv domain body point first tree) =
    coneEquiv domain body point second
      ((ContextualWTypes.family (futureDomain domain point) (futureBody domain body point)).map step tree) := by
  apply Subtype.ext
  apply eq_of_heq
  let oldSignature := signature domain body point
  let firstPrefix := ContextualSmallFamilyUniverse.futurePrefix first.2
  let lastPrefix := ContextualSmallFamilyUniverse.futurePrefix step.1
  let firstRoot := ContextualSmallFamilyUniverse.root first.1
  let lastRoot := ContextualSmallFamilyUniverse.root second.1
  have signatureEq := signature_prefix domain body (futureStep point first)
  have restrictEq := ContextualWReindexing.restrict_signature_heq signatureEq.symm
    (ContextualSmallFamilyUniverse.rootArrow step.1)
    (coneEquiv domain body point first tree).val
    (ContextualWReindexing.pullData firstPrefix oldSignature tree.val firstRoot (nativeRoot_eq point first))
    (coneEquiv_raw domain body point first tree)
  have afterCast := ContextualWReindexing.pull_congr (first := lastPrefix) rfl signatureEq.symm rfl _ _ restrictEq
  have lastEq : firstPrefix.obj (lastPrefix.obj lastRoot) = second := by
    apply Future.objects_ext (first := firstPrefix.obj (lastPrefix.obj lastRoot)) (second := second) rfl
    exact heq_of_eq ((Category.assoc first.2 step.1 (𝟙 second.1)).symm.trans
      ((congrArg (fun arrow => arrow ≫ 𝟙 second.1) step.2).trans (Category.comp_id second.2)))
  have arrowEq := ContextualSmallFamilyUniverse.futureArrow_heq (nativeRoot_eq point first) lastEq
    (firstPrefix.map (ContextualSmallFamilyUniverse.rootArrow step.1)) step HEq.rfl
  have afterRestriction := ContextualWReindexing.pullData_restrict firstPrefix oldSignature
    (ContextualSmallFamilyUniverse.rootArrow step.1) (nativeRoot_eq point first) lastEq step arrowEq tree.val
  have afterPull := ContextualWReindexing.pullData_congr (first := lastPrefix) rfl
    (leftSignature := ContextualWReindexing.under firstPrefix oldSignature) rfl rfl _ _
    afterRestriction.symm rfl rfl
  have afterComposition := ContextualWReindexing.pull_comp_data lastPrefix firstPrefix oldSignature
    (ContextualWTypes.restrict oldSignature.1 oldSignature.2 step tree.val)
    (lastPrefix.obj lastRoot) lastEq lastRoot rfl
  have contextEq : ContextualSmallFamilyUniverse.futurePrefix second.2 = Cat.compose lastPrefix firstPrefix :=
    (congrArg ContextualSmallFamilyUniverse.futurePrefix step.2.symm).trans
      (ContextualSmallFamilyUniverse.prefix_comp first.2 step.1)
  have compareCombined := ContextualWReindexing.pullData_congr contextEq.symm
    (leftSignature := oldSignature) rfl (leftPoint := lastRoot) rfl
    (ContextualWTypes.restrict oldSignature.1 oldSignature.2 step tree.val) _ HEq.rfl
    lastEq (nativeRoot_eq point second)
  exact (wMap_raw domain body ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).map step)
    (coneEquiv domain body point first tree)).trans
      (afterCast.trans (afterPull.trans (afterComposition.trans
        (compareCombined.trans (coneEquiv_raw domain body point second
          ((ContextualWTypes.family (futureDomain domain point) (futureBody domain body point)).map step tree)).symm))))

noncomputable def coneReadout (point : base.Elements) :
    NatTrans (ContextualWTypes.family (futureDomain domain point) (futureBody domain body point))
      (ContextualSmallFamilyUniverse.restrict (ContextualSmallFamilyUniverse.futureElement point.1 point.2)
        (w domain body)) where
  app future := TypeCat.ofHom (coneEquiv domain body point future)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro tree
    exact (coneEquiv_natural domain body point step tree).symm

noncomputable def coneReadoutInverse (point : base.Elements) :
    NatTrans (ContextualSmallFamilyUniverse.restrict (ContextualSmallFamilyUniverse.futureElement point.1 point.2)
      (w domain body)) (ContextualWTypes.family (futureDomain domain point) (futureBody domain body point)) :=
  Nat.inverse (coneReadout domain body point) (coneEquiv domain body point) (fun _ _ => rfl)

noncomputable def prefixEquiv {first second : base.Elements} (step : first ⟶ second) (future : Future.Objects second.1) :
    ContextualWReindexing.Tree (signature domain body first) ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future) ≃
      ContextualWReindexing.Tree (signature domain body second) future :=
  (ContextualWLocalChange.naturalEquiv (ContextualWLocalChange.prefixChange step.1)
    (futureDomain domain first) (futureBody domain body first) future).trans
    (ContextualWReindexing.signatureEquiv (signature_prefix domain body step) future)

theorem prefixEquiv_raw {first second : base.Elements} (step : first ⟶ second) (future : Future.Objects second.1)
    (tree : ContextualWReindexing.Tree (signature domain body first) ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future)) :
    HEq (prefixEquiv domain body step future tree).val
      (ContextualWReindexing.pull (ContextualSmallFamilyUniverse.futurePrefix step.1) (signature domain body first) future tree.val) :=
  ContextualWReindexing.signatureEquiv_raw _ _ _

theorem prefix_readout {first second : base.Elements} (step : first ⟶ second) (future : Future.Objects second.1)
    (tree : ContextualWReindexing.Tree (signature domain body first) ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future)) :
    HEq (coneEquiv domain body first ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future) tree).val
      (coneEquiv domain body second future (prefixEquiv domain body step future tree)).val := by
  let oldSignature := signature domain body first
  let firstPrefix := ContextualSmallFamilyUniverse.futurePrefix step.1
  let lastPrefix := ContextualSmallFamilyUniverse.futurePrefix future.2
  let root := ContextualSmallFamilyUniverse.root future.1
  have signatureEq := signature_prefix domain body step
  have afterCast := ContextualWReindexing.pullData_congr (first := lastPrefix) rfl signatureEq.symm rfl
    (prefixEquiv domain body step future tree).val
    (ContextualWReindexing.pull firstPrefix oldSignature future tree.val)
    (prefixEquiv_raw domain body step future tree) (nativeRoot_eq second future) (nativeRoot_eq second future)
  have afterComposition := ContextualWReindexing.pull_comp_data lastPrefix firstPrefix oldSignature tree.val
    future rfl root (nativeRoot_eq second future)
  have compareCombined := ContextualWReindexing.pullData_congr
    (ContextualSmallFamilyUniverse.prefix_comp step.1 future.2).symm (leftSignature := oldSignature) rfl
    (leftPoint := root) rfl tree.val tree.val HEq.rfl
    (congrArg firstPrefix.obj (nativeRoot_eq second future))
    (nativeRoot_eq first (firstPrefix.obj future))
  exact (coneEquiv_raw domain body first (firstPrefix.obj future) tree).trans
    ((coneEquiv_raw domain body second future (prefixEquiv domain body step future tree)).trans
      (afterCast.trans (afterComposition.trans compareCombined))).symm

theorem wAt_heq {first second : base.Elements} (points : first = second)
    (left : WAt domain body first) (right : WAt domain body second) (raw : HEq left.val right.val) : HEq left right := by
  cases points
  exact heq_of_eq (Subtype.ext (eq_of_heq raw))

theorem coneEquiv_root_heq (point : base.Elements) (tree : WAt domain body point) :
    HEq (coneEquiv domain body point (ContextualSmallFamilyUniverse.root point.1) tree) tree :=
  wAt_heq domain body (ContextualSmallFamilyUniverse.evaluationPoint_eq point.1 point.2) _ _
    (coneEquiv_root_raw domain body point tree)

theorem prefix_readout_whole {first second : base.Elements} (step : first ⟶ second) (future : Future.Objects second.1)
    (tree : ContextualWReindexing.Tree (signature domain body first) ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future)) :
    HEq (coneEquiv domain body first ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future) tree)
      (coneEquiv domain body second future (prefixEquiv domain body step future tree)) :=
  wAt_heq domain body (prefixPoint_eq step future) _ _ (prefix_readout domain body step future tree)

end Mettapedia.TypeTheory.ContextualSmallFamilyWCone
