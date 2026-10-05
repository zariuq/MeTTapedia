import Mettapedia.TypeTheory.WiderContextualWPolynomialReindexing

/-!
# Contextual W polynomial with arbitrary wider algebra values

The parameter family may be wider; shapes and positions remain small.
The complete future polynomial's results occupy their own universe,
independently of the original-bound tree carrier.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWiderPolynomial

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers
open PowerClassPresheafBaseChange

universe u v h
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u) (target : base.Elements ⥤ Type h)

abbrev futureTarget (point : base.Elements) : Future.Objects point.1 ⥤ Type h :=
  ContextualSmallFamilyUniverse.restrict (ContextualSmallFamilyUniverse.futureElement point.1 point.2) target

theorem familyArrow_heq {E : Type v} [Category.{u} E] (family : E ⥤ Type h)
    {first otherFirst second otherSecond : E}
    (source : first = otherFirst) (destination : second = otherSecond)
    (left : first ⟶ second) (right : otherFirst ⟶ otherSecond) (arrows : HEq left right) :
    HEq (family.map left) (family.map right) := by
  cases source
  cases destination
  cases eq_of_heq arrows
  rfl

theorem futureTarget_prefix {first second : base.Elements} (step : first ⟶ second) :
    ContextualSmallFamilyUniverse.restrict (ContextualSmallFamilyUniverse.futurePrefix step.1)
      (futureTarget target first) = futureTarget target second := by
  refine Functor.hext (fun future => congrArg target.obj (prefixPoint_eq step future)) ?_
  intro source destination arrow
  exact familyArrow_heq target (prefixPoint_eq step source) (prefixPoint_eq step destination)
    ((ContextualSmallFamilyUniverse.futureElement first.1 first.2).map
      ((ContextualSmallFamilyUniverse.futurePrefix step.1).map arrow))
    ((ContextualSmallFamilyUniverse.futureElement second.1 second.2).map arrow)
    (ContextualSmallFamilyUniverse.elementsArrow_heq
      (prefixPoint_eq step source) (prefixPoint_eq step destination) _ _ HEq.rfl)

theorem rootMap_id_heq (point : D) (family : Future.Objects point ⥤ Type h)
    (value : family.obj (ContextualSmallFamilyUniverse.root point)) :
    HEq (family.map (ContextualSmallFamilyUniverse.rootArrow (𝟙 point)) value) value := by
  have destination : (ContextualSmallFamilyUniverse.futurePrefix (𝟙 point)).obj
      (ContextualSmallFamilyUniverse.root point) = ContextualSmallFamilyUniverse.root point :=
    congrArg (fun change : Future.Objects point ⥤ Future.Objects point =>
      change.obj (ContextualSmallFamilyUniverse.root point)) (ContextualSmallFamilyUniverse.prefix_id point)
  exact (ContextualSmallFamilyUniverse.familyMap_heq family rfl destination
    (ContextualSmallFamilyUniverse.rootArrow (𝟙 point)) (𝟙 (ContextualSmallFamilyUniverse.root point))
    (ContextualSmallFamilyUniverse.futureArrow_heq rfl destination _ _ (heq_of_eq rfl))
    value value HEq.rfl).trans
      (heq_of_eq (family.map_id_apply (ContextualSmallFamilyUniverse.root point) value))

theorem rootMap_comp_heq {first middle last : D} (earlier : first ⟶ middle) (later : middle ⟶ last)
    (family : Future.Objects first ⥤ Type h)
    (value : family.obj (ContextualSmallFamilyUniverse.root first)) :
    HEq (family.map (ContextualSmallFamilyUniverse.rootArrow (earlier ≫ later)) value)
      (family.map ((ContextualSmallFamilyUniverse.futurePrefix earlier).map
        (ContextualSmallFamilyUniverse.rootArrow later))
        (family.map (ContextualSmallFamilyUniverse.rootArrow earlier) value)) := by
  have destination : (ContextualSmallFamilyUniverse.futurePrefix (earlier ≫ later)).obj
      (ContextualSmallFamilyUniverse.root last) =
    (ContextualSmallFamilyUniverse.futurePrefix earlier).obj
      ((ContextualSmallFamilyUniverse.futurePrefix later).obj (ContextualSmallFamilyUniverse.root last)) :=
    congrArg (fun change : Future.Objects last ⥤ Future.Objects first =>
      change.obj (ContextualSmallFamilyUniverse.root last)) (ContextualSmallFamilyUniverse.prefix_comp earlier later)
  exact (ContextualSmallFamilyUniverse.familyMap_heq family rfl destination
    (ContextualSmallFamilyUniverse.rootArrow (earlier ≫ later))
    (ContextualSmallFamilyUniverse.rootArrow earlier ≫
      (ContextualSmallFamilyUniverse.futurePrefix earlier).map (ContextualSmallFamilyUniverse.rootArrow later))
    (ContextualSmallFamilyUniverse.futureArrow_heq rfl destination _ _ (heq_of_eq rfl)) value value HEq.rfl).trans
      (heq_of_eq (family.map_comp_apply _ _ value))

def signature (point : base.Elements) : WiderContextualWPolynomialReindexing.Signature (Future.Objects point.1) :=
  ⟨ContextualSmallFamilyWTypes.signature domain body point, futureTarget target point⟩

abbrev At (point : base.Elements) : Type (max u h) :=
  WiderContextualWPolynomialReindexing.At (signature domain body target point) (ContextualSmallFamilyUniverse.root point.1)

theorem signature_prefix {first second : base.Elements} (step : first ⟶ second) :
    WiderContextualWPolynomialReindexing.under (ContextualSmallFamilyUniverse.futurePrefix step.1)
      (signature domain body target first) = signature domain body target second :=
  Prod.ext (ContextualSmallFamilyWTypes.signature_prefix domain body step) (futureTarget_prefix target step)

def pMap {first second : base.Elements} (step : first ⟶ second) (node : At domain body target first) : At domain body target second :=
  WiderContextualWPolynomialReindexing.castAt (signature_prefix domain body target step) (ContextualSmallFamilyUniverse.root second.1)
    (WiderContextualWPolynomialReindexing.pull (ContextualSmallFamilyUniverse.futurePrefix step.1)
      (signature domain body target first) (ContextualSmallFamilyUniverse.root second.1)
      ((WiderContextualWPolynomialReindexing.family (signature domain body target first)).map
        (ContextualSmallFamilyUniverse.rootArrow step.1) node))

theorem pMap_value {first second : base.Elements} (step : first ⟶ second) (node : At domain body target first) :
    HEq (pMap domain body target step node)
      (WiderContextualWPolynomialReindexing.pull (ContextualSmallFamilyUniverse.futurePrefix step.1)
        (signature domain body target first) (ContextualSmallFamilyUniverse.root second.1)
        ((WiderContextualWPolynomialReindexing.family (signature domain body target first)).map
          (ContextualSmallFamilyUniverse.rootArrow step.1) node)) :=
  WiderContextualWPolynomialReindexing.castAt_heq _ _ _

theorem pMap_id (point : base.Elements) (node : At domain body target point) : pMap domain body target (𝟙 point) node = node := by
  apply eq_of_heq
  refine (pMap_value domain body target (𝟙 point) node).trans ?_
  have moved := rootMap_id_heq point.1
    (WiderContextualWPolynomialReindexing.family (signature domain body target point)) node
  exact (WiderContextualWPolynomialReindexing.pull_congr (ContextualSmallFamilyUniverse.prefix_id point.1)
    rfl rfl _ _ moved).trans (WiderContextualWPolynomialReindexing.pull_identity (signature domain body target point) _ node)

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
  let moved := (WiderContextualWPolynomialReindexing.family oldSignature).map
    (ContextualSmallFamilyUniverse.rootArrow earlier.1) tree
  let doubleMoved := (WiderContextualWPolynomialReindexing.family oldSignature).map
    (firstPrefix.map (ContextualSmallFamilyUniverse.rootArrow later.1)) moved
  have signatureEq := signature_prefix domain body target earlier
  have restrictEq := WiderContextualWPolynomialReindexing.restrict_signature_heq signatureEq.symm
    (ContextualSmallFamilyUniverse.rootArrow later.1)
    (pMap domain body target earlier tree)
    (WiderContextualWPolynomialReindexing.pull firstPrefix oldSignature middleRoot moved)
    (pMap_value domain body target earlier tree)
  have afterCast := WiderContextualWPolynomialReindexing.pull_congr (first := lastPrefix) rfl signatureEq.symm rfl _ _ restrictEq
  have afterRestriction := WiderContextualWPolynomialReindexing.pull_restrict firstPrefix oldSignature
    (ContextualSmallFamilyUniverse.rootArrow later.1) moved
  have afterPull := WiderContextualWPolynomialReindexing.pull_congr (first := lastPrefix) rfl
    (leftSignature := WiderContextualWPolynomialReindexing.under firstPrefix oldSignature) rfl rfl _ _
    (heq_of_eq afterRestriction.symm)
  have combinedMoved := rootMap_comp_heq earlier.1 later.1
    (WiderContextualWPolynomialReindexing.family oldSignature) tree
  have afterComposition := WiderContextualWPolynomialReindexing.pull_comp lastPrefix firstPrefix oldSignature lastRoot doubleMoved
  have compareCombined := WiderContextualWPolynomialReindexing.pull_congr
    (ContextualSmallFamilyUniverse.prefix_comp earlier.1 later.1).symm
    (leftSignature := oldSignature) rfl rfl doubleMoved _ combinedMoved.symm
  exact (pMap_value domain body target (earlier ≫ later) tree).trans
    ((pMap_value domain body target later (pMap domain body target earlier tree)).trans
      (afterCast.trans (afterPull.trans (afterComposition.trans compareCombined)))).symm

def polynomial : base.Elements ⥤ Type (max u h) where
  obj := At domain body target
  map step := TypeCat.ofHom (pMap domain body target step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact pMap_id domain body target point
  map_comp first later := by
    apply ConcreteCategory.hom_ext
    exact pMap_comp domain body target first later


end Mettapedia.TypeTheory.ContextualSmallFamilyWiderPolynomial
