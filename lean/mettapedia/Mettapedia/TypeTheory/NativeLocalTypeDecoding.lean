import Mettapedia.TypeTheory.NativeLocalPiEta
import Mettapedia.TypeTheory.ContextualLocalUniversesDecoding

/-!
# Computational decoding of native local type formers

The local parameter-space product decodes to the existing native product
through its canonical base-change comparison. That comparison carries
the actual abstraction and evaluation sections. Dependent pairs decode
through the proved family equality without changing either witness.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NativeLocalTypeDecoding

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafCwf DisplayedPresheafPi DisplayedPresheafPiSubstitution
open DisplayedPresheafSigma ContextualLocalUniverses
open NativeLocalTypeFormers NativeLocalTypeOperations

universe u
variable {C : Type u} [Category.{u} C]
variable {X : Face.{u, u, u} C}

private theorem abstraction_family_cast (A : DisplayedFamily.{u, u, u, u} X)
    {B0 B : DisplayedFamily.{u, u, u, u} (totalSpace A)}
    (same : B0 = B) (body : B.sections) :
    (Functor.sectionsFunctor X.Elements).map
        (eqToIso (congrArg (piDisplayed A) same)).hom
        (piSectionEquiv A B0
          (cast (congrArg (fun family : DisplayedFamily.{u, u, u, u}
            (totalSpace A) => (family.sections : Type u)) same.symm) body)) =
      piSectionEquiv A B body := by
  cases same
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem abstraction_comparison (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) (body : B.decoded.sections) :
    (Functor.sectionsFunctor X.Elements).map (piDecodeIso A B).hom
        (lam (A := A) (B := B) body) = piSectionEquiv A.decoded B.decoded body := by
  let B0 := reindexDisplayed
    (totalReindexMap (formerName A B) (parameterDomain A B)) (parameterBody A B)
  let comparison := piSubstitutionIso (formerName A B) (parameterDomain A B)
    (parameterBody A B)
  let castBody : B0.sections :=
    cast (congrArg (fun family : DisplayedFamily.{u, u, u, u}
      (totalSpace A.decoded) => (family.sections : Type u))
      (parameterBody_decode A B).symm) body
  change (Functor.sectionsFunctor X.Elements).map
      (comparison.inv ≫ (eqToIso
        (congrArg (piDisplayed A.decoded) (parameterBody_decode A B))).hom)
      ((Functor.sectionsFunctor X.Elements).map comparison.hom
        (piSectionEquiv A.decoded B0 castBody)) = _
  rw [Functor.map_comp]
  change (Functor.sectionsFunctor X.Elements).map
      (eqToIso (congrArg (piDisplayed A.decoded) (parameterBody_decode A B))).hom
      (((Functor.sectionsFunctor X.Elements).map comparison.inv)
        (((Functor.sectionsFunctor X.Elements).map comparison.hom)
          (piSectionEquiv A.decoded B0 castBody))) = _
  have cancel := ConcreteCategory.congr_hom
    (((Functor.sectionsFunctor X.Elements).mapIso comparison).hom_inv_id)
    (piSectionEquiv A.decoded B0 castBody)
  simp only [types_comp_apply, types_id_apply] at cancel
  exact (congrArg (fun value : (piDisplayed A.decoded B0).sections =>
    (Functor.sectionsFunctor X.Elements).map
      (eqToIso (congrArg (piDisplayed A.decoded) (parameterBody_decode A B))).hom value)
    cancel).trans (abstraction_family_cast A.decoded (parameterBody_decode A B) body)

set_option backward.isDefEq.respectTransparency false in
theorem evaluation_comparison (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) (function : (pi A B).decoded.sections) :
    (piSectionEquiv A.decoded B.decoded).symm
      ((Functor.sectionsFunctor X.Elements).map (piDecodeIso A B).hom function) =
        (functionEquiv A B).symm function := by
  apply (piSectionEquiv A.decoded B.decoded).injective
  rw [Equiv.apply_symm_apply]
  have comparison := abstraction_comparison A B ((functionEquiv A B).symm function)
  rw [eta] at comparison
  exact comparison

theorem application_comparison (A : NativeType X)
    (B : NativeType (totalSpace A.decoded))
    (function : (pi A B).decoded.sections) (argument : A.decoded.sections) :
    app function argument = reindexDisplayedSection (sectionLift A.decoded argument)
      B.decoded ((piSectionEquiv A.decoded B.decoded).symm
        ((Functor.sectionsFunctor X.Elements).map (piDecodeIso A B).hom function)) := by
  rw [evaluation_comparison]
  rfl

theorem pair_comparison (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) (first : A.decoded.sections)
    (second : (reindexDisplayed (sectionLift A.decoded first) B.decoded).sections) :
    sumTermEquiv A B (pair first second) =
      sigmaDisplayedPair A.decoded B.decoded first second := by
  exact (sumTermEquiv A B).apply_symm_apply _

end Mettapedia.TypeTheory.NativeLocalTypeDecoding
