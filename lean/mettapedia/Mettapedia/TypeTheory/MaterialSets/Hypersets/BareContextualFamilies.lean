import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialEquivalence
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSiteLiftMaterial

/-!
# Constructed contextual models of arbitrary bare material families

An arbitrary material carrier at every context point and authored maps on
its actual member subtypes determine a contextual family. The member types
already live in the successor host universe. The actual raised site and
uniform membership-graph presentation therefore give a material family at
graph bound `u + 1`, without original-bound representatives or supplied
fibre dictionaries.

The member, section and substitution comparisons retain original material
values and all authored restrictions. This construction pays the explicit
successor cost; it does not assert a uniform original-bound graph selector
or a small ambient universe.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.BareContextualFamilies

open CategoryTheory ContextualGeneratedUniverse
open Mettapedia.TypeTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent (compose identity)

universe u v
variable {C : Type u} [Category.{u} C]

abbrev Members (X : HSet.{u}) := {value : HSet.{u} // value ∈ X}

structure Family {D : Type v} [Category.{v} D] (context : LabelledContext D) : Type (max v (u + 1)) where
  carrier : context.base.Elements → HSet.{u}
  restrict : ∀ {point next : context.base.Elements}, (point ⟶ next) → Members (carrier point) → Members (carrier next)
  restrict_id : ∀ (point : context.base.Elements) (member : Members (carrier point)), restrict (𝟙 point) member = member
  restrict_comp : ∀ {point next later : context.base.Elements} (first : point ⟶ next) (second : next ⟶ later)
    (member : Members (carrier point)), restrict (first ≫ second) member = restrict second (restrict first member)

private def graphMembers (X : HSet.{u}) :
    {value : HSet.{u + 1} // value ∈ HSet.mk (HSet.presentationUp X)} ≃
      {value : HSet.{u + 1} // value ∈ HSet.lift X} where
  toFun member := ⟨member.val, HSet.mk_presentationUp X ▸ member.property⟩
  invFun member := ⟨member.val, (HSet.mk_presentationUp X).symm ▸ member.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def memberModel (X : HSet.{u}) : PresentedType (Members X) where
  graph := HSet.presentationUp X
  decode := (graphMembers X).trans (HSet.liftedMembersEquiv X).symm

theorem memberModel_carrier (X : HSet.{u}) : (memberModel X).carrier = HSet.lift X :=
  HSet.mk_presentationUp X

theorem memberModel_value (X : HSet.{u}) (member : Members X) :
    (memberModel X).value member = HSet.lift member.val := rfl

namespace Family

section Source

variable {D : Type v} [Category.{v} D] {context : LabelledContext D} (family : Family.{u, v} context)

/-- The original actual member family has the larger fibre universe. -/
def source : context.base.Elements ⥤ Type (u + 1) where
  obj point := Members (family.carrier point)
  map step := TypeCat.ofHom (family.restrict step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact family.restrict_id point
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    exact family.restrict_comp first second

end Source

section Raised

variable {D : Type (u + 1)} [Category.{u + 1} D]
variable {context : LabelledContext D} (family : Family.{u, u + 1} context)

/-- At an already raised context, arbitrary bare carriers and their actual
member maps construct every fibre dictionary at the same raised bound. -/
def atRaised : MaterialFamily context where
  family := family.source
  model point := memberModel (family.carrier point)

theorem atRaised_carrier (point : context.base.Elements) :
    (family.atRaised.model point).carrier = HSet.lift (family.carrier point) := memberModel_carrier _

theorem atRaised_value (point : context.base.Elements) (member : family.atRaised.family.obj point) :
    (family.atRaised.model point).value member = HSet.lift member.val := rfl

def atRaised_reindex {other : LabelledContext D} (change : NatTrans other.base context.base) :
    Family.{u, u + 1} other where
  carrier point := family.carrier ((PowerClassPresheafProducts.elementMap change).obj point)
  restrict step := family.restrict ((PowerClassPresheafProducts.elementMap change).map step)
  restrict_id _point member := by
    rw [(PowerClassPresheafProducts.elementMap change).map_id]
    exact family.restrict_id _ member
  restrict_comp first second member := by
    rw [(PowerClassPresheafProducts.elementMap change).map_comp]
    exact family.restrict_comp _ _ member

theorem atRaised_reindex_material {other : LabelledContext D} (change : NatTrans other.base context.base) :
    (family.atRaised_reindex change).atRaised = family.atRaised.reindex change := by
  apply ContextualUniverseCodes.MaterialFamily.ext
  · refine Functor.hext (fun _ => rfl) ?_
    intro _ _ _
    rfl
  · exact heq_of_eq rfl

end Raised

variable {context : LabelledContext C} (family : Family.{u, u} context)

/-- This is built directly on the raised context; no small lower-fibre
presheaf-lifting operation is applied to the larger actual member types. -/
def displayed : (ContextualSiteLiftMaterial.context context).base.Elements ⥤ Type (u + 1) where
  obj point := Members (family.carrier ((PresheafSiteLift.elementsDown context.base).obj point))
  map step := TypeCat.ofHom (family.restrict ((PresheafSiteLift.elementsDown context.base).map step))
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro member
    rw [(PresheafSiteLift.elementsDown context.base).map_id]
    exact family.restrict_id _ member
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro member
    rw [(PresheafSiteLift.elementsDown context.base).map_comp]
    exact family.restrict_comp _ _ member

def raised : Family.{u, u + 1} (ContextualSiteLiftMaterial.context context) where
  carrier point := family.carrier ((PresheafSiteLift.elementsDown context.base).obj point)
  restrict step := family.restrict ((PresheafSiteLift.elementsDown context.base).map step)
  restrict_id _point member := by
    rw [(PresheafSiteLift.elementsDown context.base).map_id]
    exact family.restrict_id _ member
  restrict_comp first second member := by
    rw [(PresheafSiteLift.elementsDown context.base).map_comp]
    exact family.restrict_comp _ _ member

def material : MaterialFamily (ContextualSiteLiftMaterial.context context) where
  family := family.displayed
  model point := memberModel (family.carrier ((PresheafSiteLift.elementsDown context.base).obj point))

theorem raised_material : family.raised.atRaised = family.material := by
  apply ContextualUniverseCodes.MaterialFamily.ext
  · refine Functor.hext (fun _ => rfl) ?_
    intro _ _ _
    rfl
  · exact heq_of_eq rfl

theorem material_carrier (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    (family.material.model point).carrier =
      HSet.lift (family.carrier ((PresheafSiteLift.elementsDown context.base).obj point)) :=
  memberModel_carrier _

theorem material_value (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (member : family.material.family.obj point) :
    (family.material.model point).value member = HSet.lift member.val := rfl

def memberComparison (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    {value : HSet.{u + 1} // value ∈ (family.material.model point).carrier} ≃
      Members (family.carrier ((PresheafSiteLift.elementsDown context.base).obj point)) :=
  (family.material.model point).decode

theorem memberComparison_value (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (member : {value : HSet.{u + 1} // value ∈ (family.material.model point).carrier}) :
    HSet.lift (family.memberComparison point member).val = member.val :=
  (family.material.model point).value_decode member

theorem memberComparison_symm_value (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (member : Members (family.carrier ((PresheafSiteLift.elementsDown context.base).obj point))) :
    ((family.memberComparison point).symm member).val = HSet.lift member.val := rfl

theorem memberComparison_natural {point next : (ContextualSiteLiftMaterial.context context).base.Elements}
    (step : point ⟶ next) (member : {value : HSet.{u + 1} // value ∈ (family.material.model point).carrier}) :
    family.memberComparison next (family.material.memberRestriction step member) =
      family.restrict ((PresheafSiteLift.elementsDown context.base).map step) (family.memberComparison point member) :=
  family.material.memberRestriction_decode step member

theorem memberComparison_symm_natural {point next : (ContextualSiteLiftMaterial.context context).base.Elements}
    (step : point ⟶ next)
    (member : Members (family.carrier ((PresheafSiteLift.elementsDown context.base).obj point))) :
    family.material.memberRestriction step ((family.memberComparison point).symm member) =
      (family.memberComparison next).symm (family.restrict ((PresheafSiteLift.elementsDown context.base).map step) member) :=
  family.material.memberRestriction_encode step member

def raiseSection (term : family.source.sections) : family.material.family.sections :=
  ⟨fun point => term.val ((PresheafSiteLift.elementsDown context.base).obj point), by
    intro point next step
    exact term.property ((PresheafSiteLift.elementsDown context.base).map step)⟩

def lowerSection (term : family.material.family.sections) : family.source.sections :=
  ⟨fun point => term.val ((PresheafSiteLift.elementsUp context.base).obj point), by
    intro point next step
    exact term.property ((PresheafSiteLift.elementsUp context.base).map step)⟩

def sectionComparison : family.source.sections ≃ family.material.family.sections where
  toFun := family.raiseSection
  invFun := family.lowerSection
  left_inv _term := Subtype.ext (funext fun _ => rfl)
  right_inv _term := Subtype.ext (funext fun _ => rfl)

theorem section_value (term : family.source.sections)
    (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    (family.material.model point).value ((family.sectionComparison term).val point) =
      HSet.lift (term.val ((PresheafSiteLift.elementsDown context.base).obj point)).val := rfl

def reindex {other : LabelledContext C} (change : NatTrans other.base context.base) : Family.{u, u} other where
  carrier point := family.carrier ((PowerClassPresheafProducts.elementMap change).obj point)
  restrict step := family.restrict ((PowerClassPresheafProducts.elementMap change).map step)
  restrict_id point member := by
    rw [(PowerClassPresheafProducts.elementMap change).map_id]
    exact family.restrict_id _ member
  restrict_comp first second member := by
    rw [(PowerClassPresheafProducts.elementMap change).map_comp]
    exact family.restrict_comp _ _ member

theorem material_reindex {other : LabelledContext C} (change : NatTrans other.base context.base) :
    (family.reindex change).material = family.material.reindex (other := ContextualSiteLiftMaterial.context other)
      (PresheafSiteLift.raiseChange change) := by
  apply ContextualUniverseCodes.MaterialFamily.ext
  · refine Functor.hext (fun _ => rfl) ?_
    intro _ _ _
    rfl
  · exact heq_of_eq rfl

end Family

/-- Existing interpretations supply an actual bare carrier family and
actual member maps. Its new dictionary is built uniformly by membership. -/
def ofMaterial {context : LabelledContext C} (domain : MaterialFamily context) : Family.{u, u} context where
  carrier point := (domain.model point).carrier
  restrict step := domain.memberRestriction step
  restrict_id point member := congrArg (fun operation => operation member) (domain.members.map_id point)
  restrict_comp first second member := congrArg (fun operation => operation member) (domain.members.map_comp first second)

/-- Uniformly rebuilt bare members and the previous small native carrier
have a constructed natural comparison; its values are the same lifted sets. -/
def ofMaterialComparison {context : LabelledContext C} (domain : MaterialFamily context) :
    ContextualMaterialEquivalence.Equivalence (ofMaterial domain).material (ContextualSiteLiftMaterial.family domain) where
  fibre point := {
    toFun member := ⟨(domain.model ((PresheafSiteLift.elementsDown context.base).obj point)).decode member⟩
    invFun member := (domain.model ((PresheafSiteLift.elementsDown context.base).obj point)).decode.symm member.down
    left_inv member := (domain.model _).decode.symm_apply_apply member
    right_inv member := congrArg ULift.up ((domain.model _).decode.apply_symm_apply member.down) }
  naturality step member := congrArg ULift.up
    (domain.memberRestriction_decode ((PresheafSiteLift.elementsDown context.base).map step) member)
  value point member := congrArg HSet.lift
    ((domain.model ((PresheafSiteLift.elementsDown context.base).obj point)).value_decode member)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.BareContextualFamilies
