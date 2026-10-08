import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialProducts
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphUniverseLiftPairs
import Mathlib.CategoryTheory.Types.Basic

/-!
# Actual material families at the raised site and fibre bound

The parameter, native receipt and material graph are raised together.
Material body attachment is rebuilt at the upper bound, and its complete
future membership agrees with the lifted lower carrier, including members
whose presentations are arbitrary upper graphs.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLift

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphMaterialFamilies

universe u
variable {D : Type u} [Category.{u} D]

abbrev Upper := ContextualGraphUniverseLift.Raised (D := D)

/-- Raising values with explicit functor laws. -/
def valueRaise : Type u ⥤ Type (u+1) where
  obj carrier := ULift.{u+1,u} carrier
  map operation := TypeCat.ofHom fun value => ULift.up (operation value.down)
  map_id _ := rfl
  map_comp _ _ := rfl

def base (original : D ⥤ Type u) : Upper (D := D) ⥤ Type (u+1) :=
  PresheafSiteLift.compose PresheafSiteLift.Site.downFunctor
    (PresheafSiteLift.compose original valueRaise)

def elementsDown (original : D ⥤ Type u) : (base original).Elements ⥤ original.Elements where
  obj point := ⟨point.1.down, point.2.down⟩
  map step := ⟨step.1.down, congrArg ULift.down step.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def elementsUp (original : D ⥤ Type u) : original.Elements ⥤ (base original).Elements where
  obj point := ⟨PresheafSiteLift.Site.upFunctor.obj point.1, ULift.up point.2⟩
  map step := ⟨PresheafSiteLift.Site.upFunctor.map step.1, congrArg ULift.up step.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

variable {original : D ⥤ Type u} (family : Family original)

def native : (base original).Elements ⥤ Type (u+1) :=
  PresheafSiteLift.compose (elementsDown original) (PresheafSiteLift.compose family.native valueRaise)

def reading : NaturalHom (total (native family)) (values (Upper (D := D))) where
  app _ receipt := ContextualGraphUniverseLift.value
    (family.reading.app _ ⟨receipt.1.down, receipt.2.down⟩)
  naturality {_first _second} arrival receipt :=
    congrArg ContextualGraphUniverseLift.value
      (family.reading.naturality arrival.down ⟨receipt.1.down, receipt.2.down⟩)

def raise : Family (base original) where
  native := native family
  reading := reading family

theorem term_value (point : (base original).Elements) (term : (native family).obj point) :
    termValue (raise family) point term = ContextualGraphUniverseLift.value
      (termValue family ((elementsDown original).obj point) term.down) := rfl

section DependentBody

variable (domain : Family original) (body : Family (total domain.native))

/-- Flatten the two raised comprehension coordinates without erasing either. -/
def bodyBaseMap : NaturalHom (total (native domain)) (base (total domain.native)) where
  app _ receipt := ULift.up ⟨receipt.1.down, receipt.2.down⟩
  naturality _ _ := rfl

def raisedBody : Family (total (native domain)) :=
  substitute (raise body) (bodyBaseMap domain)

theorem body_value (point : (total (native domain)).Elements)
    (term : (raisedBody domain body).native.obj point) :
    termValue (raisedBody domain body) point term = ContextualGraphUniverseLift.value
      (termValue body ⟨point.1.down, ⟨point.2.1.down, point.2.2.down⟩⟩ term.down) := rfl

end DependentBody

def carrierForth (point : Upper (D := D)) (parameter : original.obj point.down)
    (element : Value (Upper (D := D)) point)
    (membership : Member element (ContextualGraphUniverseLift.value
      ((ContextualGraphMaterialProducts.carrier family).app point.down parameter))) :
    Member element ((ContextualGraphMaterialProducts.carrier (raise family)).app point (ULift.up parameter)) := by
  let parent := (ContextualGraphMaterialProducts.carrier family).app point.down parameter
  let child := ContextualGraphUniverseLift.childDecoder parent membership.1
  let decoded := ContextualGraphFamilyBodyComparison.memberDecode family.native family.reading
    ⟨point.down, parameter⟩ (childValue D parent child) (Member.atChild parent child)
  have atChild : Equal element (ContextualGraphUniverseLift.value (childValue D parent child)) := membership.2
  exact ContextualGraphFamilyBodyComparison.memberIntro (native family) (reading family)
    ⟨point, ULift.up parameter⟩ element (ULift.up decoded.1)
    (atChild.trans (ContextualGraphUniverseLift.preserve decoded.2))

def carrierBack (point : Upper (D := D)) (parameter : original.obj point.down)
    (element : Value (Upper (D := D)) point)
    (membership : Member element
      ((ContextualGraphMaterialProducts.carrier (raise family)).app point (ULift.up parameter))) :
    Member element (ContextualGraphUniverseLift.value
      ((ContextualGraphMaterialProducts.carrier family).app point.down parameter)) := by
  let decoded := ContextualGraphFamilyBodyComparison.memberDecode (native family) (reading family)
    ⟨point, ULift.up parameter⟩ element membership
  let member := ContextualGraphFamilyBodyComparison.memberIntro family.native family.reading
    ⟨point.down, parameter⟩ (termValue family ⟨point.down, parameter⟩ decoded.1.down)
    decoded.1.down (Equal.refl _)
  exact Member.transportChild decoded.2.symm (ContextualGraphUniverseLift.memberPreserve member)

/-- The fresh upper attachment and the lifted lower attachment have the
same members with complete matching data at every future context. -/
def carrierComparison (point : Upper (D := D)) (parameter : original.obj point.down) :
    Equal (ContextualGraphUniverseLift.value
      ((ContextualGraphMaterialProducts.carrier family).app point.down parameter))
      ((ContextualGraphMaterialProducts.carrier (raise family)).app point (ULift.up parameter)) :=
  extensionality
    (fun target arrival element membership =>
      Member.transportParent (Equal.ofEq
        ((ContextualGraphMaterialProducts.carrier (raise family)).naturality arrival (ULift.up parameter))).symm
        (carrierForth family target (original.map arrival.down parameter) element
          (Member.transportParent (Equal.ofEq (congrArg ContextualGraphUniverseLift.value
            ((ContextualGraphMaterialProducts.carrier family).naturality arrival.down parameter))) membership)))
    (fun target arrival element membership =>
      Member.transportParent (Equal.ofEq (congrArg ContextualGraphUniverseLift.value
          ((ContextualGraphMaterialProducts.carrier family).naturality arrival.down parameter))).symm
        (carrierBack family target (original.map arrival.down parameter) element
          (Member.transportParent (Equal.ofEq
            ((ContextualGraphMaterialProducts.carrier (raise family)).naturality arrival (ULift.up parameter))) membership)))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLift
