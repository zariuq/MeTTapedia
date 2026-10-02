import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mettapedia.OSLF.Syntax.SemanticAccountSignature
import Mettapedia.OSLF.Syntax.SecondOrderBindingModelRestriction
import Mettapedia.OSLF.Syntax.BindingFirstOrderFamilyTransport

/-!
# Full binding models with a semantic Mark operation

Both categories are full subcategories of the existing binding-clone
category. The accounted objects retain every original operator and all
mixed substitution environments. Forgetting removes only the additional
Mark operation and its laws; it does not remove marked carrier elements.

The original equation family has no metavariable declarations. Its full
contextual satisfaction is transported by the canonical-instance theorem,
not by assuming that arbitrary target values are generator images.

These are semantic model categories after a signature has been supplied.
They do not construct a language transformer, retained authority, or funding.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SemanticAccountBindingModels

open _root_.CategoryTheory FreeBindingClone SecondOrderContext

universe u

variable {S : Signature} {signatureSort baseSort wrappedSort : S.Srt}

def originalProperty (family : EqAxiom S [] → Prop) :
    ObjectProperty (BindingCloneAlgebra.Algebra.{u} S) :=
  fun algebra => BindingEquationFamilyModel.Satisfies algebra family

abbrev Original (family : EqAxiom S [] → Prop) :=
  (originalProperty.{u} family).FullSubcategory

abbrev markObject (signatureSort wrappedSort : S.Srt) : Object S :=
  ⟨SemanticAccountSignature.declarations signatureSort wrappedSort⟩

def accountedProperty (family : EqAxiom S [] → Prop)
    (apparatus : SemanticAccountSignature.Apparatus S signatureSort baseSort wrappedSort) :
    ObjectProperty
      (BindingCloneAlgebra.Algebra.{u}
        (SemanticAccountSignature.signature S signatureSort wrappedSort)) :=
  fun algebra =>
    BindingEquationFamilyModel.Satisfies
      (restrictAlgebra (markObject signatureSort wrappedSort) algebra) family ∧
    BindingEquationFamilyModel.Satisfies algebra
      (fun equation => equation ∈ SemanticAccountSignature.laws apparatus)

abbrev Accounted (family : EqAxiom S [] → Prop)
    (apparatus : SemanticAccountSignature.Apparatus S signatureSort baseSort wrappedSort) :=
  (accountedProperty.{u} family apparatus).FullSubcategory

/-- A genuine full clone that independently satisfies the two equation
families supplies an object. No free-extension claim is part of this map. -/
def ofAlgebra (family : EqAxiom S [] → Prop)
    (apparatus : SemanticAccountSignature.Apparatus S signatureSort baseSort wrappedSort)
    (algebra : BindingCloneAlgebra.Algebra.{u}
      (SemanticAccountSignature.signature S signatureSort wrappedSort))
    (original : BindingEquationFamilyModel.Satisfies
      (restrictAlgebra (markObject signatureSort wrappedSort) algebra) family)
    (accounts : BindingEquationFamilyModel.Satisfies algebra
      (fun equation => equation ∈ SemanticAccountSignature.laws apparatus)) :
    Accounted family apparatus := ⟨algebra, original, accounts⟩

/-- Restrict the existing clone morphism along the actual operator inclusion. -/
def forget (family : EqAxiom S [] → Prop)
    (apparatus : SemanticAccountSignature.Apparatus S signatureSort baseSort wrappedSort) :
    Accounted.{u} family apparatus ⥤ Original.{u} family where
  obj target := ⟨restrictAlgebra (markObject signatureSort wrappedSort) target.obj,
    target.property.1⟩
  map arrow := ObjectProperty.homMk
    (restrictHom (markObject signatureSort wrappedSort) arrow.hom)
  map_id := by
    intro target
    apply ObjectProperty.hom_ext
    apply FreeBindingClone.Hom.ext
    exact FreeBindingTerms.Hom.ext (fun _ => rfl)
  map_comp := by
    intro first second third left right
    apply ObjectProperty.hom_ext
    apply FreeBindingClone.Hom.ext
    exact FreeBindingTerms.Hom.ext (fun _ => rfl)

instance forget_faithful (family : EqAxiom S [] → Prop)
    (apparatus : SemanticAccountSignature.Apparatus S signatureSort baseSort wrappedSort) :
    (forget.{u} family apparatus).Faithful where
  map_injective := by
    intro first second left right same
    apply ObjectProperty.hom_ext
    apply FreeBindingClone.Hom.ext
    apply FreeBindingTerms.Hom.ext
    intro Γ sort value
    exact congrArg (fun arrow => arrow.hom.raw.map value) same

/-- A unit into an independently constructed accounted clone is enough
to establish the original family at all target ordinary environments. -/
theorem original_satisfaction_of_unit (family : EqAxiom S [] → Prop)
    (source : Original.{u} family)
    (target : BindingCloneAlgebra.Algebra.{u}
      (SemanticAccountSignature.signature S signatureSort wrappedSort))
    (unit : FreeBindingClone.Hom source.obj
      (restrictAlgebra (markObject signatureSort wrappedSort) target)) :
    BindingEquationFamilyModel.Satisfies
      (restrictAlgebra (markObject signatureSort wrappedSort) target) family :=
  BindingFirstOrderFamilyTransport.satisfies_map unit source.property

end Mettapedia.OSLF.Binding.SemanticAccountBindingModels
