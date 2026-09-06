import Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-!
# The heterogeneous category of consequence institutions

Bundling each Pi-institution with its native signature category turns the
signature-changing comorphisms already used by the little-theories layer into
one heterogeneous category.  This is the consequence-only projection of the
model-valued category of institutions; it deliberately does not reconstruct models
or proof identities from semantic consequence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PiInstitutionCategory

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

universe uSignature uHom uSentence

structure Object where
  Signature : CategoryTheory.Cat.{uHom, uSignature}
  logic : PiInstitution.{uSignature, uHom, uSentence} Signature

abbrev Hom
    (source target : Object.{uSignature, uHom, uSentence}) :=
  PiInstitution.Comorphism source.logic target.logic

namespace Hom

def identity (object : Object.{uSignature, uHom, uSentence}) :
    Hom object object :=
  PiInstitution.Comorphism.identity object.logic

def comp
    {first middle last : Object.{uSignature, uHom, uSentence}}
    (earlier : Hom first middle) (later : Hom middle last) :
    Hom first last :=
  PiInstitution.Comorphism.comp earlier later

end Hom

instance instQuiver : Quiver (Object.{uSignature, uHom, uSentence}) where
  Hom := Hom

instance instCategory : CategoryTheory.Category
    (Object.{uSignature, uHom, uSentence}) where
  id := Hom.identity
  comp := Hom.comp
  id_comp route := by
    apply PiInstitution.Comorphism.ext
    · exact CategoryTheory.Functor.id_comp route.mapSignature
    · rfl
  comp_id route := by
    apply PiInstitution.Comorphism.ext
    · exact CategoryTheory.Functor.comp_id route.mapSignature
    · rfl
  assoc earlier middle later := by
    apply PiInstitution.Comorphism.ext
    · exact CategoryTheory.Functor.assoc earlier.mapSignature
        middle.mapSignature later.mapSignature
    · rfl

#print axioms Hom.identity
#print axioms Hom.comp
#print axioms instCategory

end Mettapedia.GSLT.LanguageDef.PiInstitutionCategory
