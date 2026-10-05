import Mettapedia.TypeTheory.ContextualCoherentSmallMaps
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSmallMapClassification

/-!
# Covered-quotient descent of coherent small material maps

A cover of an actual material member presheaf maps the source decoder's
small receipts onto each target fibre. Coverage is proved propositionally;
no source occurrence or inverse of the cover is selected. The saturated
receipt predicates and bounded singleton-row union then construct an
actual target fibre decoder and its coherent contextual action.

The material carrier is the supplied bound for every decoded value. This
uses the hyperset model's proposition-valued powerset, bounded separation
and union operations. It is not a decoder theorem for an arbitrary host
type or a selection of coherent data from pointwise receipt-smallness.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialCoherentDescent

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover ContextualImageFactorization
open ContextualCoherentSmallMaps ContextualGeneratedUniverse

universe u v w
variable {C : Type u} [Category.{u} C] {context : LabelledContext C}
variable (domain : BareContextualFamilies.Family.{u, u} context)
variable {A : context.base.Elements ⥤ Type v} {X : context.base.Elements ⥤ Type w}
variable (operation : NaturalHom domain.source A) (cover : NaturalHom X domain.source)
variable (covered : Cover cover) (model : Data (cover.comp operation))

def enumeration (point : context.base.Elements) (parameter : A.obj point) :
    Enumeration.{u, u + 1} (Fibre operation point parameter) where
  Carrier := model.family.obj ⟨point, parameter⟩
  value code := ⟨cover.app point (model.decoder ⟨point, parameter⟩ code).val,
    (model.decoder ⟨point, parameter⟩ code).property⟩
  covered receipt := by
    obtain ⟨source, sourceLaw⟩ := covered point receipt.val
    let sourceReceipt : Fibre (cover.comp operation) point parameter :=
      ⟨source, (congrArg (operation.app point) sourceLaw).trans receipt.property⟩
    refine ⟨(model.decoder ⟨point, parameter⟩).symm sourceReceipt, ?_⟩
    apply Subtype.ext
    exact (congrArg (fun source : Fibre (cover.comp operation) point parameter => cover.app point source.val)
      ((model.decoder ⟨point, parameter⟩).apply_symm_apply sourceReceipt)).trans sourceLaw

def descendedData : Data operation where
  family := ContextualMaterialSmallMapClassification.smallFamily domain operation
    (ContextualSmallMapConstructions.identity A) (enumeration domain operation cover covered model)
  decoder := ContextualMaterialSmallMapClassification.fibreDecoder domain operation
    (ContextualSmallMapConstructions.identity A) (enumeration domain operation cover covered model)
  naturality step code := by
    apply Subtype.ext
    exact (ContextualMaterialSmallMapClassification.decode_restriction domain operation
      (ContextualSmallMapConstructions.identity A) (enumeration domain operation cover covered model) step code).symm

theorem decoder_restriction {first second : A.Elements} (step : first ⟶ second)
    (code : (descendedData domain operation cover covered model).family.obj first) :
    ((descendedData domain operation cover covered model).decoder second
      ((descendedData domain operation cover covered model).family.map step code)).val =
      domain.source.map step.1
        ((descendedData domain operation cover covered model).decoder first code).val :=
  congrArg Subtype.val ((descendedData domain operation cover covered model).naturality step code).symm

include covered in
theorem coherent_class_descent (presented : Nonempty (Data (cover.comp operation))) : Nonempty (Data operation) := by
  obtain ⟨sourceModel⟩ := presented
  exact ⟨descendedData domain operation cover covered sourceModel⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialCoherentDescent
