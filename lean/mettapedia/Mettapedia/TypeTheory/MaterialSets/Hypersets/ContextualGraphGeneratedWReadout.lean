import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphSmallWReadout
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedFamilies

/-!
# Generated W codes with constructed future material bodies

Original-small generated domain and position codes have their actual
native decoding. Given their declared natural element readings, the W
reading is constructed from the native destructor and hereditary branches.
The literal decoder, whole sections and generated universe classification
refer to that same native W family. The older pointwise material dictionary
remains a separate readout and is compared through its native decoder.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedWReadout

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

/-- The dependent position graph is obtained from the actual body over
the domain's comprehension, with the proved flattening comparison. -/
def positionReading : NaturalHom
    (total (ContextualGraphSmallWBranchSpan.displayedBody domain.decode.native (domain.decode.bodyNative body.decode)))
    (values D) :=
  (totalCast (ContextualSmallFamilyComprehension.body_roundtrip domain.decode.native body.decode.native)).comp bodyReading

noncomputable def reading : NaturalHom (total (domain.w body).decode.native) (values D) :=
  ContextualGraphSmallWReadout.reading domain.decode.native (domain.decode.bodyNative body.decode)
    domainReading (positionReading domain body bodyReading)

noncomputable def parent : NaturalHom base (values D) :=
  ContextualGraphFamilyBodies.parent (domain.w body).decode.native (reading domain body domainReading bodyReading)

noncomputable def literal : base.Elements ⥤ Type u :=
  ContextualGraphFamilyBodies.literal (domain.w body).decode.native (reading domain body domainReading bodyReading)

noncomputable def toNative : NaturalHom (literal domain body domainReading bodyReading) (domain.w body).decode.native :=
  ContextualGraphFamilyBodies.toNative (domain.w body).decode.native (reading domain body domainReading bodyReading)

noncomputable def toLiteral : NaturalHom (domain.w body).decode.native (literal domain body domainReading bodyReading) :=
  ContextualGraphFamilyBodies.toLiteral (domain.w body).decode.native (reading domain body domainReading bodyReading)

theorem native_inverse : (toLiteral domain body domainReading bodyReading).comp
    (toNative domain body domainReading bodyReading) = ContextualSmallMapConstructions.identity (domain.w body).decode.native := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem literal_inverse : (toNative domain body domainReading bodyReading).comp
    (toLiteral domain body domainReading bodyReading) =
      ContextualSmallMapConstructions.identity (literal domain body domainReading bodyReading) := by
  apply NaturalHom.ext
  intro point receipt
  exact ContextualGraphFamilyBodies.encode_decode (domain.w body).decode.native
    (reading domain body domainReading bodyReading) point receipt

noncomputable def sectionDecoder : (literal domain body domainReading bodyReading).sections ≃
    (domain.w body).decode.native.sections :=
  ContextualGraphFamilyBodies.sectionDecoder (domain.w body).decode.native (reading domain body domainReading bodyReading)

/-- Both representations retain complete native sections. This does not
assert equality of the two deliberately different material readouts. -/
noncomputable def dictionarySections : (literal domain body domainReading bodyReading).sections ≃
    (domain.w body).memberSections :=
  (sectionDecoder domain body domainReading bodyReading).trans (domain.w body).sectionDecoder

noncomputable def unfold (point : base.Elements) (tree : (domain.w body).decode.native.obj point) :
    Equal ((reading domain body domainReading bodyReading).app point.1 ⟨point.2, tree⟩)
      (ContextualGraphOrderedPairs.orderedPair
        (domainReading.app point.1 ⟨point.2,
          (ContextualGraphSmallWBranchSpan.labelNative domain.decode.native (domain.decode.bodyNative body.decode)).app point tree⟩)
        ((ContextualGraphSmallWReadout.branchCollection domain.decode.native (domain.decode.bodyNative body.decode)
          domainReading (positionReading domain body bodyReading)).app point.1 ⟨point.2, tree⟩)) :=
  ContextualGraphSmallWReadout.unfold domain.decode.native (domain.decode.bodyNative body.decode)
    domainReading (positionReading domain body bodyReading) point tree

/-- The generated W's complete future classifier is an actual member of
the already constructed successor enclosure. Its decoding agrees with
the constructed body's literal decoder through the same native tree. -/
noncomputable def enclosureDecoder (point : D) (parameter : base.obj point) :
    Child ContextualGraphFamilyEnclosure.UpperSite
      (ContextualGraphFamilyEnclosure.representedCode (PresheafSiteLift.Site.upFunctor.obj point)
        (familyCode (domain.w body).decode.native point parameter)) ≃
      (literal domain body domainReading bodyReading).obj ⟨point, parameter⟩ :=
  (ContextualGraphGeneratedFamilies.enclosedDecoder (domain.w body) point parameter).trans
    (ContextualGraphFamilyBodies.decoder (domain.w body).decode.native
      (reading domain body domainReading bodyReading) ⟨point, parameter⟩).symm

theorem enclosure_decoder_square (point : D) (parameter : base.obj point)
    (receipt : Child ContextualGraphFamilyEnclosure.UpperSite
      (ContextualGraphFamilyEnclosure.representedCode (PresheafSiteLift.Site.upFunctor.obj point)
        (familyCode (domain.w body).decode.native point parameter))) :
    (toNative domain body domainReading bodyReading).app ⟨point, parameter⟩
      (enclosureDecoder domain body domainReading bodyReading point parameter receipt) =
        ContextualGraphGeneratedFamilies.enclosedDecoder (domain.w body) point parameter receipt := rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedWReadout
