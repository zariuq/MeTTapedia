import Mettapedia.TypeTheory.ContextualWReindexing

/-!
# Original-bound contextual W families over wider parameters

At each parameter, trees are built on the small category of complete
future context arrows. The transported parameter and the dependent
position family remain in every local signature. Context restriction
uses actual tree recursion and the constructed future-prefix functor.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWTypes

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers
open PowerClassPresheafBaseChange
open Mettapedia.GSLT.Topos.ConstructivePresheaf

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

def signature (point : base.Elements) : ContextualWReindexing.Signature (Future.Objects point.1) :=
  ⟨futureDomain domain point, futureBody domain body point⟩

abbrev WAt (point : base.Elements) : Type u :=
  ContextualWReindexing.Tree (signature domain body point) (ContextualSmallFamilyUniverse.root point.1)

theorem signature_prefix {first second : base.Elements} (step : first ⟶ second) :
    ContextualWReindexing.under (ContextualSmallFamilyUniverse.futurePrefix step.1)
      (signature domain body first) = signature domain body second := by
  apply Sigma.ext (futureDomain_prefix domain step)
  apply ContextualWReindexing.position_transport_heq (futureDomain_prefix domain step)
  exact futureBody_prefix domain body step

noncomputable def wMap {first second : base.Elements} (step : first ⟶ second)
    (tree : WAt domain body first) : WAt domain body second :=
  ContextualWReindexing.castTree (signature_prefix domain body step) (ContextualSmallFamilyUniverse.root second.1)
    (ContextualWReindexing.pullTree (ContextualSmallFamilyUniverse.futurePrefix step.1)
      (signature domain body first) (ContextualSmallFamilyUniverse.root second.1)
      ((ContextualWTypes.family (futureDomain domain first) (futureBody domain body first)).map
        (ContextualSmallFamilyUniverse.rootArrow step.1) tree))

theorem wMap_raw {first second : base.Elements} (step : first ⟶ second) (tree : WAt domain body first) :
    HEq (wMap domain body step tree).val
      (ContextualWReindexing.pull (ContextualSmallFamilyUniverse.futurePrefix step.1)
        (signature domain body first) (ContextualSmallFamilyUniverse.root second.1)
        (ContextualWTypes.restrict (futureDomain domain first) (futureBody domain body first)
          (ContextualSmallFamilyUniverse.rootArrow step.1) tree.val)) :=
  ContextualWReindexing.castTree_raw _ _ _

theorem wMap_id (point : base.Elements) (tree : WAt domain body point) :
    wMap domain body (𝟙 point) tree = tree := by
  apply Subtype.ext
  apply eq_of_heq
  refine (wMap_raw domain body (𝟙 point) tree).trans ?_
  have target : (ContextualSmallFamilyUniverse.futurePrefix (𝟙 point.1)).obj
      (ContextualSmallFamilyUniverse.root point.1) = ContextualSmallFamilyUniverse.root point.1 :=
    congrArg (fun operation => operation.obj (ContextualSmallFamilyUniverse.root point.1))
      (ContextualSmallFamilyUniverse.prefix_id point.1)
  have rawMoved : HEq
      (ContextualWTypes.restrict (futureDomain domain point) (futureBody domain body point)
        (ContextualSmallFamilyUniverse.rootArrow (𝟙 point.1)) tree.val) tree.val := by
    exact (ContextualWBaseChange.restrict_heq (futureDomain domain point) (futureBody domain body point)
      rfl target (ContextualSmallFamilyUniverse.rootArrow (𝟙 point.1))
      (𝟙 (ContextualSmallFamilyUniverse.root point.1))
      (ContextualSmallFamilyUniverse.futureArrow_heq rfl target _ _ HEq.rfl)
      tree.val tree.val HEq.rfl).trans
        (heq_of_eq (ContextualWTypes.restrict_id _ _ tree.val))
  exact (ContextualWReindexing.pull_congr (ContextualSmallFamilyUniverse.prefix_id point.1)
    rfl rfl _ _ rawMoved).trans (ContextualWReindexing.pull_identity (signature domain body point) _ tree.val)

theorem wMap_comp {first middle last : base.Elements} (earlier : first ⟶ middle) (later : middle ⟶ last)
    (tree : WAt domain body first) :
    wMap domain body (earlier ≫ later) tree = wMap domain body later (wMap domain body earlier tree) := by
  apply Subtype.ext
  apply eq_of_heq
  let oldSignature := signature domain body first
  let firstPrefix := ContextualSmallFamilyUniverse.futurePrefix earlier.1
  let lastPrefix := ContextualSmallFamilyUniverse.futurePrefix later.1
  let firstRoot := ContextualSmallFamilyUniverse.root first.1
  let middleRoot := ContextualSmallFamilyUniverse.root middle.1
  let lastRoot := ContextualSmallFamilyUniverse.root last.1
  let moved := ContextualWTypes.restrict oldSignature.1 oldSignature.2
    (ContextualSmallFamilyUniverse.rootArrow earlier.1) tree.val
  let doubleMoved := ContextualWTypes.restrict oldSignature.1 oldSignature.2
    (firstPrefix.map (ContextualSmallFamilyUniverse.rootArrow later.1)) moved
  have signatureEq := signature_prefix domain body earlier
  have restrictEq := ContextualWReindexing.restrict_signature_heq signatureEq.symm
    (ContextualSmallFamilyUniverse.rootArrow later.1)
    (wMap domain body earlier tree).val
    (ContextualWReindexing.pull firstPrefix oldSignature middleRoot moved)
    (wMap_raw domain body earlier tree)
  have afterCast := ContextualWReindexing.pull_congr (first := lastPrefix) rfl signatureEq.symm rfl _ _ restrictEq
  have afterRestriction := ContextualWReindexing.pull_restrict firstPrefix oldSignature
    (ContextualSmallFamilyUniverse.rootArrow later.1) moved
  have afterPull := ContextualWReindexing.pull_congr (first := lastPrefix) rfl
    (leftSignature := ContextualWReindexing.under firstPrefix oldSignature) rfl rfl _ _
    (heq_of_eq afterRestriction.symm)
  have combinedTarget : (ContextualSmallFamilyUniverse.futurePrefix (earlier.1 ≫ later.1)).obj lastRoot =
      firstPrefix.obj (lastPrefix.obj lastRoot) :=
    congrArg (fun operation => operation.obj lastRoot) (ContextualSmallFamilyUniverse.prefix_comp earlier.1 later.1)
  have combinedArrow := ContextualSmallFamilyUniverse.futureArrow_heq rfl combinedTarget
    (ContextualSmallFamilyUniverse.rootArrow (earlier.1 ≫ later.1))
    (ContextualSmallFamilyUniverse.rootArrow earlier.1 ≫ firstPrefix.map (ContextualSmallFamilyUniverse.rootArrow later.1))
    HEq.rfl
  have combinedMoved := (ContextualWBaseChange.restrict_heq oldSignature.1 oldSignature.2
    rfl combinedTarget _ _ combinedArrow tree.val tree.val HEq.rfl).trans
      (heq_of_eq (ContextualWTypes.restrict_comp oldSignature.1 oldSignature.2
        (ContextualSmallFamilyUniverse.rootArrow earlier.1)
        (firstPrefix.map (ContextualSmallFamilyUniverse.rootArrow later.1)) tree.val).symm)
  have afterComposition := ContextualWReindexing.pull_comp lastPrefix firstPrefix oldSignature lastRoot doubleMoved
  have compareCombined := ContextualWReindexing.pull_congr
    (ContextualSmallFamilyUniverse.prefix_comp earlier.1 later.1).symm
    (leftSignature := oldSignature) rfl rfl doubleMoved _ combinedMoved.symm
  exact (wMap_raw domain body (earlier ≫ later) tree).trans
    ((wMap_raw domain body later (wMap domain body earlier tree)).trans
      (afterCast.trans (afterPull.trans (afterComposition.trans compareCombined)))).symm

noncomputable def w : base.Elements ⥤ Type u where
  obj := WAt domain body
  map step := TypeCat.ofHom (wMap domain body step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact wMap_id domain body point
  map_comp first later := by
    apply ConcreteCategory.hom_ext
    exact wMap_comp domain body first later

end Mettapedia.TypeTheory.ContextualSmallFamilyWTypes
