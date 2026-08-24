import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
import Mettapedia.GSLT.LanguageDef.Cost.Elaboration.Total

/-!
# The complete-decoration waist for lawful one-step Cost elaborations

Checked Cost elaborations retain dependent typing and region-tree evidence.
Their complete nondependent decorations already have a strict covariant
action along conservative lawful Cost arrows.  This module packages that
action as a functor and takes its category of elements.

The resulting total category is an intermediate proof-erasure boundary.  It
retains every computational choice recorded by `CostTreeDecoration`; it is
not an occurrence-only quotient and does not claim to be a minimal event
format.  The checked-tree total category maps fully faithfully into it by
erasing the dependent fibre indices, typing witnesses, and proof tree while
retaining the complete computational decoration.
-/

namespace Mettapedia.GSLT.LanguageDef

open CategoryTheory
open scoped CategoryTheory

namespace CostElaborationBase

/-- Complete computational decorations form a covariant family over the
conservative lawful Cost base. -/
def decorationFunctor : CategoryTheory.Functor CostElaborationBase Type where
  obj base := CostTreeDecoration base.toLayer.source.toCIGSLT
  map morphism := TypeCat.ofHom fun decoration =>
    decoration.map morphism.underlying.underlying.underlying
  map_id base := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro decoration
    exact CostTreeDecoration.map_id _ decoration
  map_comp first second := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro decoration
    exact CostTreeDecoration.map_comp
      first.underlying.underlying.underlying
      second.underlying.underlying.underlying decoration

end CostElaborationBase

/-- Total category of a lawful Cost base together with one complete
computational decoration. -/
abbrev Cost.Decoration.Total :=
  (CostElaborationBase.decorationFunctor).Elements

namespace Cost.Decoration.Total

/-- Forget a complete decoration while retaining its lawful Cost base. -/
def projection :
    CategoryTheory.Functor Cost.Decoration.Total CostElaborationBase :=
  CategoryTheory.CategoryOfElements.π CostElaborationBase.decorationFunctor

/-- Package a lawful base and one complete decoration as an object of the
decoration total category. -/
def ofDecoration (base : CostElaborationBase)
    (decoration : CostTreeDecoration base.toLayer.source.toCIGSLT) :
    Cost.Decoration.Total :=
  ⟨base, decoration⟩

/-- Push a complete decoration forward along a conservative lawful Cost
arrow. -/
def pushforwardObject (object : Cost.Decoration.Total)
    {target : CostElaborationBase} (morphism : object.1 ⟶ target) :
    Cost.Decoration.Total :=
  ⟨target, CostElaborationBase.decorationFunctor.map morphism object.2⟩

/-- The canonical arrow from a decoration to its strict push-forward. -/
def pushforwardLift (object : Cost.Decoration.Total)
    {target : CostElaborationBase} (morphism : object.1 ⟶ target) :
    object ⟶ pushforwardObject object morphism :=
  CategoryTheory.CategoryOfElements.homMk _ _ morphism rfl

@[simp]
theorem projection_map_pushforwardLift (object : Cost.Decoration.Total)
    {target : CostElaborationBase} (morphism : object.1 ⟶ target) :
    projection.map (pushforwardLift object morphism) = morphism :=
  rfl

/-- Strict decoration transport is the strongly cocartesian lift supplied by
the category of elements. -/
instance pushforwardLift_isStronglyCocartesian
    (object : Cost.Decoration.Total) {target : CostElaborationBase}
    (morphism : object.1 ⟶ target) :
    projection.IsStronglyCocartesian morphism
      (pushforwardLift object morphism) where
  toIsHomLift := by
    change projection.IsHomLift
      (projection.map (pushforwardLift object morphism))
      (pushforwardLift object morphism)
    infer_instance
  universal_property' := by
    intro destination next composite compositeLift
    letI : projection.IsHomLift
        (CategoryTheory.CategoryStruct.comp morphism next) composite :=
      compositeLift
    have baseEquality :
        CategoryTheory.CategoryStruct.comp morphism next = composite.val :=
      @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
        projection object destination
        (CategoryTheory.CategoryStruct.comp morphism next) composite
        compositeLift
    let factor : pushforwardObject object morphism ⟶ destination :=
      CategoryTheory.CategoryOfElements.homMk _ _ next (by
        change CostElaborationBase.decorationFunctor.map next
            (CostElaborationBase.decorationFunctor.map morphism object.2) =
          destination.2
        calc
          _ = CostElaborationBase.decorationFunctor.map
                (CategoryTheory.CategoryStruct.comp morphism next) object.2 :=
              (CategoryTheory.Functor.map_comp_apply
                CostElaborationBase.decorationFunctor morphism next
                object.2).symm
          _ = CostElaborationBase.decorationFunctor.map composite.val
                object.2 := by
              exact congrArg
                (fun arrow =>
                  CostElaborationBase.decorationFunctor.map arrow object.2)
                baseEquality
          _ = destination.2 := composite.property)
    have factorLift : projection.IsHomLift next factor := by
      change projection.IsHomLift (projection.map factor) factor
      infer_instance
    have factorization : CategoryTheory.CategoryStruct.comp
        (pushforwardLift object morphism) factor = composite := by
      apply CategoryTheory.CategoryOfElements.ext
      exact baseEquality
    refine ⟨factor, ⟨factorLift, factorization⟩, ?_⟩
    intro other properties
    letI : projection.IsHomLift next other := properties.1
    have otherBase : next = projection.map other :=
      @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
        projection (pushforwardObject object morphism) destination next other
        properties.1
    apply CategoryTheory.CategoryOfElements.ext
    exact otherBase.symm

/-- Negative canary: an identity base arrow cannot connect unequal complete
decorations. -/
theorem noIdentityArrowOfDecorationNe (base : CostElaborationBase)
    (source target : CostTreeDecoration base.toLayer.source.toCIGSLT)
    (different : source ≠ target) :
    ¬ ∃ arrow : (ofDecoration base source) ⟶ (ofDecoration base target),
      arrow.val = CostElaborationBase.Morphism.id base := by
  rintro ⟨arrow, baseIdentity⟩
  have natural := arrow.property
  rw [baseIdentity] at natural
  change source.map
      (CIGSLT.Morphism.id base.toLayer.source.toCIGSLT) = target at natural
  rw [CostTreeDecoration.map_id] at natural
  exact different natural

/-- Positive control: equal complete decorations over one lawful base are
connected by the identity base arrow. -/
def identityArrowOfDecorationEq (base : CostElaborationBase)
    (source target : CostTreeDecoration base.toLayer.source.toCIGSLT)
    (equal : source = target) :
    (ofDecoration base source) ⟶ (ofDecoration base target) :=
  CategoryTheory.CategoryOfElements.homMk _ _
    (CostElaborationBase.Morphism.id base)
    ((CostTreeDecoration.map_id _ source).trans equal)

@[simp]
theorem identityArrowOfDecorationEq_val (base : CostElaborationBase)
    (source target : CostTreeDecoration base.toLayer.source.toCIGSLT)
    (equal : source = target) :
    (identityArrowOfDecorationEq base source target equal).val =
      CostElaborationBase.Morphism.id base :=
  rfl

end Cost.Decoration.Total

namespace Cost.Elaboration.Total

/-- Forget the dependent checked tree while retaining its complete
computational decoration. -/
def forgetToDecoration :
    CategoryTheory.Functor Cost.Elaboration.Total Cost.Decoration.Total where
  obj object := ⟨object.base, object.decoration⟩
  map morphism :=
    CategoryTheory.CategoryOfElements.homMk _ _ morphism.base
      morphism.decoration_natural
  map_id _ := by
    apply CategoryTheory.CategoryOfElements.ext
    rfl
  map_comp _ _ := by
    apply CategoryTheory.CategoryOfElements.ext
    rfl

@[simp]
theorem forgetToDecoration_obj_base (object : Cost.Elaboration.Total) :
    (forgetToDecoration.obj object).1 = object.base :=
  rfl

@[simp]
theorem forgetToDecoration_obj_decoration (object : Cost.Elaboration.Total) :
    (forgetToDecoration.obj object).2 = object.decoration :=
  rfl

/-- Forgetting the proof tree and then the decoration is exactly the original
projection to the lawful Cost base. -/
theorem forgetToDecoration_comp_projection :
    forgetToDecoration.comp Cost.Decoration.Total.projection = projection :=
  rfl

/-- Checked-tree transport erases to the canonical push-forward of the
complete decoration.  This is the commuting square between the two
cocartesian constructions. -/
theorem forgetToDecoration_obj_transportObject
    {source target : CostElaborationBase} (morphism : source ⟶ target)
    (fiber : CostElaborationFiber source.toLayer.source.toCIGSLT) :
    forgetToDecoration.obj (transportObject morphism fiber) =
      Cost.Decoration.Total.pushforwardObject
        (forgetToDecoration.obj (⟨source, fiber⟩ : Cost.Elaboration.Total))
        morphism := by
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (mapCostElaborationFiber_decoration
        morphism.underlying.underlying.underlying
        (Cost.Layer.Hom.CompactMapLaws.preservesGeneratedReflectiveScope
          morphism.underlying.compactMapLaws)
        morphism.reindexLaws fiber)

/-- The chosen checked-tree lift maps to the canonical decoration lift, up
to the object equality supplied by exact decoration transport. -/
theorem forgetToDecoration_map_transportLift
    {source target : CostElaborationBase} (morphism : source ⟶ target)
    (fiber : CostElaborationFiber source.toLayer.source.toCIGSLT) :
    CategoryTheory.CategoryStruct.comp
        (forgetToDecoration.map (transportLift morphism fiber))
        (CategoryTheory.eqToHom
          (forgetToDecoration_obj_transportObject morphism fiber)) =
      Cost.Decoration.Total.pushforwardLift
        (forgetToDecoration.obj (⟨source, fiber⟩ : Cost.Elaboration.Total))
        morphism := by
  apply CategoryTheory.CategoryOfElements.ext
  let objectEquality := forgetToDecoration_obj_transportObject morphism fiber
  have projectedEqToHom :
      Cost.Decoration.Total.projection.map
          (CategoryTheory.eqToHom objectEquality) =
        CostElaborationBase.Morphism.id target := by
    rw [CategoryTheory.eqToHom_map]
    exact CategoryTheory.eqToHom_refl target _
  change CostElaborationBase.Morphism.comp morphism
      (Cost.Decoration.Total.projection.map
        (CategoryTheory.eqToHom objectEquality)) = morphism
  rw [projectedEqToHom]
  exact CategoryTheory.Category.comp_id morphism

/-- Proof-tree erasure is faithful because arrows on both sides are
determined by their lawful base arrow. -/
instance forgetToDecoration_faithful : forgetToDecoration.Faithful where
  map_injective := by
    intro source target first second equality
    apply Morphism.ext
    have baseEquality := congrArg (fun arrow => arrow.val) equality
    exact baseEquality

/-- Between two realized decorations, every decoration arrow lifts to an
arrow of checked trees: the required equation is exactly the retained
decoration naturality field.  This does not assert that every decoration
object is realized by a checked tree. -/
instance forgetToDecoration_full : forgetToDecoration.Full where
  map_surjective := by
    intro source target arrow
    let lifted : source ⟶ target :=
      { base := arrow.val
        decoration_natural := arrow.property }
    refine ⟨lifted, ?_⟩
    apply CategoryTheory.CategoryOfElements.ext
    rfl

/-- Explicit fully faithful structure for the checked-tree refinement.  This
is full only between decorations already realized by checked trees; it does
not assert essential surjectivity onto arbitrary decorations. -/
noncomputable def forgetToDecorationFullyFaithful :
    forgetToDecoration.FullyFaithful :=
  CategoryTheory.Functor.FullyFaithful.ofFullyFaithful forgetToDecoration

end Cost.Elaboration.Total

end Mettapedia.GSLT.LanguageDef
