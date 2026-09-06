import Mettapedia.Logic.Institution

/-!
# The heterogeneous category of model-valued institutions

An institution carries its own signature category, sentence functor, model
functor, and satisfaction relation.  Bundling the signature category makes
institutions with different native signatures objects of one category;
institution comorphisms are its arrows.

This is the outer atlas of mathematical logics.  It does not impose a common
syntax and it does not give a logic an artificial operational semantics.
GSLTs may be attached later as independently justified operational faces.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.InstitutionCategory

open CategoryTheory
open scoped CategoryTheory

universe uSignature uSignatureHom uSentence uModel uModelHom

/-- A model-valued institution bundled with its native signature category. -/
structure Object where
  Signature : CategoryTheory.Cat.{uSignatureHom, uSignature}
  logic : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
    Signature

/-- A heterogeneous arrow is an institution comorphism between the bundled
native logics. -/
abbrev Hom
    (source target : Object.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom}) :=
  Institution.Comorphism source.logic target.logic

namespace Hom

def identity
    (object : Object.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom}) : Hom object object :=
  Institution.Comorphism.identity object.logic

def comp
    {first middle last : Object.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom}}
    (earlier : Hom first middle) (later : Hom middle last) :
    Hom first last :=
  Institution.Comorphism.comp earlier later

end Hom

instance instQuiver : Quiver
    (Object.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}) where
  Hom := Hom

instance instCategory : CategoryTheory.Category
    (Object.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}) where
  id := Hom.identity
  comp := Hom.comp
  id_comp := by
    intro source target route
    apply Institution.Comorphism.ext
    · exact CategoryTheory.Functor.id_comp route.mapSignature
    · rfl
    · apply heq_of_eq
      apply CategoryTheory.NatTrans.ext
      funext signature
      simp [Hom.comp, Hom.identity, Institution.Comorphism.comp,
        Institution.Comorphism.identity, CategoryTheory.Functor.opId]
      change route.mapModel.app signature ≫
        source.logic.model.map (𝟙 signature) ≫ 𝟙 _ =
          route.mapModel.app signature
      rw [source.logic.model.map_id]
      simp
  comp_id := by
    intro source target route
    apply Institution.Comorphism.ext
    · exact CategoryTheory.Functor.comp_id route.mapSignature
    · rfl
    · apply heq_of_eq
      apply CategoryTheory.NatTrans.ext
      funext signature
      simp [Hom.comp, Hom.identity, Institution.Comorphism.comp,
        Institution.Comorphism.identity, CategoryTheory.Functor.opId]
      change (target.logic.model.map
        (𝟙 (route.mapSignature.op.obj signature)) ≫ 𝟙 _) ≫
          route.mapModel.app signature = route.mapModel.app signature
      rw [target.logic.model.map_id]
      simp
  assoc earlier middle later := by
    cases earlier
    cases middle
    cases later
    rfl

#print axioms Hom.identity
#print axioms Hom.comp
#print axioms instCategory

end Mettapedia.Logic.InstitutionCategory
