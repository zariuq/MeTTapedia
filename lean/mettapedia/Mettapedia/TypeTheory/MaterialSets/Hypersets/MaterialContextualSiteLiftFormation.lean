import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualSiteLiftTypeFormers
import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWSiteLift

/-!
# Whole interpretation coherence of independently raised type formation

The independently formed upper carriers and decoders coincide with the
ordinary contextual material type constructors on the raised domain and
comprehension-transported body. The equalities retain the complete material
dictionary, not only the underlying semantic functor. Their dependent body
transport is the proved actual-arrow comprehension comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualSiteLiftFormation

open CategoryTheory
open ContextualGeneratedUniverse

universe u v w a
variable {C : Type u} [Category.{u} C] {original : LabelledContext C}
variable (domain : MaterialFamily original) (codomain : MaterialFamily domain.extension)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

private theorem dependentFormationCongr {I : Sort v} {M : I → Sort w} {R : Sort a}
    (formation : (index : I) → M index → R) {first second : I} (indices : first = second)
    {left : M first} {right : M second} (dictionaries : HEq left right) :
    formation first left = formation second right := by
  cases indices
  cases eq_of_heq dictionaries
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem pi_formed_eq : MaterialContextualSiteLiftTypeFormers.Pi.formed domain codomain arrows =
    (ContextualSiteLiftMaterial.family domain).pi (ContextualSiteLiftMaterial.body domain codomain)
      (ContextualSiteLiftMaterial.arrows arrows) := by
  unfold MaterialContextualSiteLiftTypeFormers.Pi.formed MaterialFamily.pi
  exact dependentFormationCongr
    (fun (position : (ContextualSiteLiftMaterial.family domain).family.Elements ⥤ Type (u + 1))
      (models : (point : (ContextualSiteLiftMaterial.family domain).family.Elements) → PresentedType (position.obj point)) =>
      ({ family := Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.dependentFunctions
          (ContextualSiteLiftMaterial.family domain).family position
         model point := PowerClassContextualMaterialization.piModel
          (ContextualSiteLiftMaterial.family domain).family position point
          ((ContextualSiteLiftMaterial.family domain).futureCoding (ContextualSiteLiftMaterial.arrows arrows) point)
          (fun argument => models ⟨argument.1.1, argument.2⟩) } :
        MaterialFamily (ContextualSiteLiftMaterial.context original)))
    (left := fun point => (ContextualSiteLiftMaterial.body domain codomain).model
      ⟨point.1.1, ⟨point.1.2, point.2⟩⟩)
    (right := fun point => (ContextualSiteLiftMaterial.body domain codomain).model
      ⟨point.1.1, ⟨point.1.2, point.2⟩⟩)
    (ContextualSiteLiftMaterial.indexed_body domain codomain).symm HEq.rfl

set_option backward.isDefEq.respectTransparency false in
theorem sigma_formed_eq : MaterialContextualSiteLiftTypeFormers.Sigma.formed domain codomain =
    (ContextualSiteLiftMaterial.family domain).sigma (ContextualSiteLiftMaterial.body domain codomain) := by
  unfold MaterialContextualSiteLiftTypeFormers.Sigma.formed MaterialFamily.sigma PowerClassPresheafProducts.sigmaFamily
  exact dependentFormationCongr
    (fun (position : (ContextualSiteLiftMaterial.family domain).family.Elements ⥤ Type (u + 1))
      (models : (point : (ContextualSiteLiftMaterial.family domain).family.Elements) → PresentedType (position.obj point)) =>
      ({ family := PowerClassPresheafProducts.IndexedSigma.family (ContextualSiteLiftMaterial.family domain).family position
         model point := PowerClassContextualMaterialization.sigmaModel
          (ContextualSiteLiftMaterial.family domain).family position point
          ((ContextualSiteLiftMaterial.family domain).model point) (fun argument => models ⟨point, argument⟩) } :
        MaterialFamily (ContextualSiteLiftMaterial.context original)))
    (left := fun point => (ContextualSiteLiftMaterial.body domain codomain).model
      ⟨point.1.1, ⟨point.1.2, point.2⟩⟩)
    (right := fun point => (ContextualSiteLiftMaterial.body domain codomain).model
      ⟨point.1.1, ⟨point.1.2, point.2⟩⟩)
    (ContextualSiteLiftMaterial.indexed_body domain codomain).symm HEq.rfl

set_option backward.isDefEq.respectTransparency false in
theorem w_formed_eq : MaterialContextualWSiteLift.formed domain codomain arrows =
    (ContextualSiteLiftMaterial.family domain).w (ContextualSiteLiftMaterial.body domain codomain)
      (ContextualSiteLiftMaterial.arrows arrows) := by
  unfold MaterialContextualWSiteLift.formed MaterialFamily.w
  exact dependentFormationCongr
    (fun (position : (ContextualSiteLiftMaterial.family domain).family.Elements ⥤ Type (u + 1))
      (models : (point : (ContextualSiteLiftMaterial.family domain).family.Elements) → PresentedType (position.obj point)) =>
      ({ family := ContextualWTypes.family (ContextualSiteLiftMaterial.family domain).family position
         model point := MaterialContextualWTypes.naturalModel (ContextualSiteLiftMaterial.family domain).family position
          (ContextualSiteLiftMaterial.context original).labels
          (MaterialFamily.elementArrowCoding (ContextualSiteLiftMaterial.arrows arrows))
          (ContextualSiteLiftMaterial.family domain).model models point } :
        MaterialFamily (ContextualSiteLiftMaterial.context original)))
    (left := fun point => (ContextualSiteLiftMaterial.body domain codomain).model
      ⟨point.1.1, ⟨point.1.2, point.2⟩⟩)
    (right := fun point => (ContextualSiteLiftMaterial.body domain codomain).model
      ⟨point.1.1, ⟨point.1.2, point.2⟩⟩)
    (ContextualSiteLiftMaterial.indexed_body domain codomain).symm HEq.rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualSiteLiftFormation
