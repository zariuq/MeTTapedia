import Mettapedia.TypeTheory.ContextualWPolynomialReindexing

/-!
# Original-bound full future polynomial families

The branch carrier retains every actual future arrow and dependent
position. Shapes and whole compatible branch tables are reindexed
constructively over wider parameters, within the original small bound.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWPolynomial

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers
open PowerClassPresheafBaseChange

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u) (target : base.Elements ⥤ Type u)

def signature (point : base.Elements) : ContextualWPolynomialReindexing.Signature (Future.Objects point.1) :=
  ⟨ContextualSmallFamilyWTypes.signature domain body point, futureDomain target point⟩

abbrev At (point : base.Elements) : Type u :=
  ContextualWPolynomialReindexing.At (signature domain body target point) (ContextualSmallFamilyUniverse.root point.1)

theorem signature_prefix {first second : base.Elements} (step : first ⟶ second) :
    ContextualWPolynomialReindexing.under (ContextualSmallFamilyUniverse.futurePrefix step.1)
      (signature domain body target first) = signature domain body target second :=
  Prod.ext (ContextualSmallFamilyWTypes.signature_prefix domain body step) (futureDomain_prefix target step)

def pMap {first second : base.Elements} (step : first ⟶ second) (node : At domain body target first) : At domain body target second :=
  ContextualWPolynomialReindexing.castAt (signature_prefix domain body target step) (ContextualSmallFamilyUniverse.root second.1)
    (ContextualWPolynomialReindexing.pull (ContextualSmallFamilyUniverse.futurePrefix step.1)
      (signature domain body target first) (ContextualSmallFamilyUniverse.root second.1)
      ((ContextualWPolynomialReindexing.family (signature domain body target first)).map
        (ContextualSmallFamilyUniverse.rootArrow step.1) node))

theorem pMap_value {first second : base.Elements} (step : first ⟶ second) (node : At domain body target first) :
    HEq (pMap domain body target step node)
      (ContextualWPolynomialReindexing.pull (ContextualSmallFamilyUniverse.futurePrefix step.1)
        (signature domain body target first) (ContextualSmallFamilyUniverse.root second.1)
        ((ContextualWPolynomialReindexing.family (signature domain body target first)).map
          (ContextualSmallFamilyUniverse.rootArrow step.1) node)) :=
  ContextualWPolynomialReindexing.castAt_heq _ _ _

theorem pMap_id (point : base.Elements) (node : At domain body target point) : pMap domain body target (𝟙 point) node = node := by
  apply eq_of_heq
  refine (pMap_value domain body target (𝟙 point) node).trans ?_
  have moved := ContextualSmallFamilyUniverse.decodeMap_id_heq point.1
    (ContextualWPolynomialReindexing.family (signature domain body target point)) node
  exact (ContextualWPolynomialReindexing.pull_congr (ContextualSmallFamilyUniverse.prefix_id point.1)
    rfl rfl _ _ moved).trans (ContextualWPolynomialReindexing.pull_identity (signature domain body target point) _ node)

theorem pMap_comp {first middle last : base.Elements} (earlier : first ⟶ middle) (later : middle ⟶ last)
    (tree : At domain body target first) :
    pMap domain body target (earlier ≫ later) tree = pMap domain body target later (pMap domain body target earlier tree) := by
  apply eq_of_heq
  let oldSignature := signature domain body target first
  let firstPrefix := ContextualSmallFamilyUniverse.futurePrefix earlier.1
  let lastPrefix := ContextualSmallFamilyUniverse.futurePrefix later.1
  let firstRoot := ContextualSmallFamilyUniverse.root first.1
  let middleRoot := ContextualSmallFamilyUniverse.root middle.1
  let lastRoot := ContextualSmallFamilyUniverse.root last.1
  let moved := (ContextualWPolynomialReindexing.family oldSignature).map
    (ContextualSmallFamilyUniverse.rootArrow earlier.1) tree
  let doubleMoved := (ContextualWPolynomialReindexing.family oldSignature).map
    (firstPrefix.map (ContextualSmallFamilyUniverse.rootArrow later.1)) moved
  have signatureEq := signature_prefix domain body target earlier
  have restrictEq := ContextualWPolynomialReindexing.restrict_signature_heq signatureEq.symm
    (ContextualSmallFamilyUniverse.rootArrow later.1)
    (pMap domain body target earlier tree)
    (ContextualWPolynomialReindexing.pull firstPrefix oldSignature middleRoot moved)
    (pMap_value domain body target earlier tree)
  have afterCast := ContextualWPolynomialReindexing.pull_congr (first := lastPrefix) rfl signatureEq.symm rfl _ _ restrictEq
  have afterRestriction := ContextualWPolynomialReindexing.pull_restrict firstPrefix oldSignature
    (ContextualSmallFamilyUniverse.rootArrow later.1) moved
  have afterPull := ContextualWPolynomialReindexing.pull_congr (first := lastPrefix) rfl
    (leftSignature := ContextualWPolynomialReindexing.under firstPrefix oldSignature) rfl rfl _ _
    (heq_of_eq afterRestriction.symm)
  have combinedMoved := ContextualSmallFamilyUniverse.decodeMap_comp_heq earlier.1 later.1
    (ContextualWPolynomialReindexing.family oldSignature) tree
  have afterComposition := ContextualWPolynomialReindexing.pull_comp lastPrefix firstPrefix oldSignature lastRoot doubleMoved
  have compareCombined := ContextualWPolynomialReindexing.pull_congr
    (ContextualSmallFamilyUniverse.prefix_comp earlier.1 later.1).symm
    (leftSignature := oldSignature) rfl rfl doubleMoved _ combinedMoved.symm
  exact (pMap_value domain body target (earlier ≫ later) tree).trans
    ((pMap_value domain body target later (pMap domain body target earlier tree)).trans
      (afterCast.trans (afterPull.trans (afterComposition.trans compareCombined)))).symm

def polynomial : base.Elements ⥤ Type u where
  obj := At domain body target
  map step := TypeCat.ofHom (pMap domain body target step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact pMap_id domain body target point
  map_comp first later := by
    apply ConcreteCategory.hom_ext
    exact pMap_comp domain body target first later

end Mettapedia.TypeTheory.ContextualSmallFamilyWPolynomial
