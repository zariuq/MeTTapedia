import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWMaterialLiftCoherence
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedWReadout

/-!
# Generated W enclosure decoding and actual upper material formation

An arbitrary original-small generated W code is decoded in the same
actual material family model. Its generated successor-enclosure receipt
and its independently formed upper W receipt recover the same native
future tree. Material observations commute through that decoder and the
constructed upper/lower W comparison; the enclosure's receipt-only graph
is not confused with the declared material body reading.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedWLift

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualAuthoredMaterialFamilies
open ContextualGraphDiagrams ContextualRealizedGraphs
universe u
variable {D : Type u} [Category.{u} D]
variable {worlds : ArgumentCoding D} {arrows : (first second : D) → ArgumentCoding (first ⟶ second)}
variable {seeds : (base : D ⥤ Type u) → Type (u+1)}
variable {seedModel : (base : D ⥤ Type u) → seeds base → Family.{u,u} base}
variable {base : D ⥤ Type u}
variable (domain : ContextualAuthoredGeneratedFamilies.Code worlds arrows seeds seedModel base)
variable (body : ContextualAuthoredGeneratedFamilies.Code worlds arrows seeds seedModel domain.decode.extension)
variable (domainReading : NaturalHom (total domain.decode.native) (values D))
variable (bodyReading : NaturalHom (total body.decode.native) (values D))

abbrev positions := ContextualGraphGeneratedWReadout.positionReading domain body bodyReading

abbrev upperFamily := ContextualGraphSmallWCarrierLift.upperFamily domain.decode.native
  (domain.decode.bodyNative body.decode) domainReading (positions domain body bodyReading)

abbrev upperLiteral := ContextualGraphSmallWCarrierLift.newLiteral domain.decode.native
  (domain.decode.bodyNative body.decode) domainReading (positions domain body bodyReading)

abbrev decoder (point : (ContextualGraphMaterialLift.base base).Elements) :=
  ContextualGraphSmallWCarrierLift.decoder domain.decode.native (domain.decode.bodyNative body.decode)
    domainReading (positions domain body bodyReading) point

def enclosureDecoder (point : D) (parameter : base.obj point) :
    Child ContextualGraphFamilyEnclosure.UpperSite
      (ContextualGraphFamilyEnclosure.representedCode (PresheafSiteLift.Site.upFunctor.obj point)
        (familyCode (domain.w body).decode.native point parameter)) ≃
      (upperLiteral domain body domainReading bodyReading).obj
        ((ContextualGraphMaterialLift.elementsUp base).obj ⟨point, parameter⟩) :=
  (ContextualGraphGeneratedFamilies.enclosedDecoder (domain.w body) point parameter).trans
    (decoder domain body domainReading bodyReading
      ((ContextualGraphMaterialLift.elementsUp base).obj ⟨point, parameter⟩)).symm

theorem enclosure_decoder_square (point : D) (parameter : base.obj point)
    (receipt : Child ContextualGraphFamilyEnclosure.UpperSite
      (ContextualGraphFamilyEnclosure.representedCode (PresheafSiteLift.Site.upFunctor.obj point)
        (familyCode (domain.w body).decode.native point parameter))) :
    decoder domain body domainReading bodyReading ((ContextualGraphMaterialLift.elementsUp base).obj ⟨point, parameter⟩)
      (enclosureDecoder domain body domainReading bodyReading point parameter receipt) =
        ContextualGraphGeneratedFamilies.enclosedDecoder (domain.w body) point parameter receipt :=
  (decoder domain body domainReading bodyReading
    ((ContextualGraphMaterialLift.elementsUp base).obj ⟨point, parameter⟩)).apply_symm_apply _

def sections : (ContextualGraphGeneratedWReadout.literal domain body domainReading bodyReading).sections ≃
    (upperLiteral domain body domainReading bodyReading).sections :=
  ContextualGraphSmallWCarrierLift.sections domain.decode.native (domain.decode.bodyNative body.decode)
    domainReading (positions domain body bodyReading)

theorem section_decoder_square
    (terms : (ContextualGraphGeneratedWReadout.literal domain body domainReading bodyReading).sections)
    (point : (ContextualGraphMaterialLift.base base).Elements) :
    decoder domain body domainReading bodyReading point ((sections domain body domainReading bodyReading terms).val point) =
      (ContextualGraphGeneratedWReadout.sectionDecoder domain body domainReading bodyReading terms).val
        (ContextualGraphSmallWSiteLift.originalPoint point) :=
  ContextualGraphSmallWCarrierLift.section_decoder_square domain.decode.native (domain.decode.bodyNative body.decode)
    domainReading (positions domain body bodyReading) terms point

def carrier_square (point : (ContextualGraphMaterialLift.base base).Elements) :
    Equal (ContextualGraphUniverseLift.value
      ((ContextualGraphGeneratedWReadout.parent domain body domainReading bodyReading).app point.1.down point.2.down))
      ((ContextualGraphMaterialProducts.carrier (upperFamily domain body domainReading bodyReading)).app point.1 point.2) :=
  ContextualGraphSmallWCarrierLift.carrierComparison domain.decode.native (domain.decode.bodyNative body.decode)
    domainReading (positions domain body bodyReading) point

def material_enclosure_square (point : D) (parameter : base.obj point)
    (receipt : Child ContextualGraphFamilyEnclosure.UpperSite
      (ContextualGraphFamilyEnclosure.representedCode (PresheafSiteLift.Site.upFunctor.obj point)
        (familyCode (domain.w body).decode.native point parameter))) :
    Equal (ContextualGraphUniverseLift.value ((ContextualGraphGeneratedWReadout.reading domain body domainReading bodyReading).app
      point ⟨parameter, ContextualGraphGeneratedFamilies.enclosedDecoder (domain.w body) point parameter receipt⟩))
      (childValue _ ((ContextualGraphMaterialProducts.carrier (upperFamily domain body domainReading bodyReading)).app
        (PresheafSiteLift.Site.upFunctor.obj point) (ULift.up parameter))
        (enclosureDecoder domain body domainReading bodyReading point parameter receipt)) :=
  (ContextualGraphSmallWCarrierLift.forwardComparison domain.decode.native (domain.decode.bodyNative body.decode)
    domainReading (positions domain body bodyReading)
    ((ContextualGraphMaterialLift.elementsUp base).obj ⟨point, parameter⟩)
    (ContextualGraphGeneratedFamilies.enclosedDecoder (domain.w body) point parameter receipt)).trans
      (ContextualGraphFamilyBodyComparison.childComparison (upperFamily domain body domainReading bodyReading).native
        (upperFamily domain body domainReading bodyReading).reading
        ((ContextualGraphMaterialLift.elementsUp base).obj ⟨point, parameter⟩) _)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedWLift
