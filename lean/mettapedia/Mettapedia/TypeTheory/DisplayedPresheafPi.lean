import Mettapedia.TypeTheory.DisplayedPresheafSlicePi
import Mettapedia.TypeTheory.DisplayedPresheafCwf
import Mettapedia.TypeTheory.ContextualTypeOperations

/-!
# Dependent functions in the existing displayed-presheaf CwF

The existing indexed-family product supplies the type former. Its adjunction
along the total-presheaf projection gives an equivalence between body terms
and function terms. Application substitutes an argument into the evaluation
body. These operations inhabit the library's shared CwF interfaces and retain
proof-relevant values. Formation is stable up to canonical isomorphism;
strict equality of the chosen right-Kan representatives is not assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafPi

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafCwf DisplayedPresheafSlicePi
open DisplayedPresheafIndexedCwfBridge CategoryIndexedFamilyGeneralPi
open ContextualProductComparison ContextualTypeOperations

universe u
variable {C : Type u} [Category.{u} C]
variable {P : Face.{u, u, u} C}

/-- Dependent function formation uses the already constructed indexed
right-Kan product, with the existing total-element comparison. -/
noncomputable def piDisplayed (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A)) :
    DisplayedFamily.{u, u, u, u} P :=
  (displayedProductFunctor A).obj B

/-- A body term over context extension is exactly a dependent function
term over the original context. The equivalence uses the actual adjunction. -/
noncomputable def piSectionEquiv (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A)) :
    B.sections ≃ (piDisplayed A B).sections :=
  (B.sectionsEquivHom PUnit).trans
    (((displayedProductAdjunction A).homEquiv
      ((Functor.const P.Elements).obj PUnit) B).trans
        ((piDisplayed A B).sectionsEquivHom PUnit).symm)

/-- Dependent abstraction of an existing natural body section. -/
noncomputable def lamDisplayed {A : DisplayedFamily.{u, u, u, u} P}
    {B : DisplayedFamily.{u, u, u, u} (totalSpace A)}
    (body : B.sections) : (piDisplayed A B).sections :=
  piSectionEquiv A B body

set_option backward.isDefEq.respectTransparency false in
/-- Abstraction agrees with the existing indexed-family transpose after
the total-element regrouping, including the body transformation. -/
theorem lamDisplayed_asIndexed {A : DisplayedFamily.{u, u, u, u} P}
    {B : DisplayedFamily.{u, u, u, u} (totalSpace A)} (body : B.sections) :
    (piDisplayed A B).sectionsEquivHom PUnit (lamDisplayed body) =
      generalPiTranspose (context := Cat.of P.Elements) A
        (Functor.whiskerLeft (displayedToTotalElements A)
          (B.sectionsEquivHom PUnit body)) := by
  change (piDisplayed A B).sectionsEquivHom PUnit
      (((piDisplayed A B).sectionsEquivHom PUnit).symm
        ((displayedProductAdjunction A).homEquiv _ B
          (B.sectionsEquivHom PUnit body))) = _
  rw [Equiv.apply_symm_apply]
  unfold displayedProductAdjunction
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv]
  apply congrArg ((generalPiAdjunction (context := Cat.of P.Elements) A).homEquiv _ _)
  ext point value
  rfl

/-- Application evaluates the function body at its dependent argument. -/
noncomputable def appDisplayed {A : DisplayedFamily.{u, u, u, u} P}
    {B : DisplayedFamily.{u, u, u, u} (totalSpace A)}
    (function : (piDisplayed A B).sections) (argument : A.sections) :
    (reindexDisplayed (sectionLift A argument) B).sections :=
  reindexDisplayedSection (sectionLift A argument) B
    ((piSectionEquiv A B).symm function)

/-- The inverse of abstraction is application of the adjunction's
evaluation map at every element of the extended context. -/
theorem piSectionEquiv_inverse_value
    (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A))
    (function : (piDisplayed A B).sections) (point : (totalSpace A).Elements) :
    ((piSectionEquiv A B).symm function).val point =
      ((displayedProductAdjunction A).counit.app B).app point
        (function.val ((totalProjection A).mapElements.obj point)) := rfl

/-- Beta returns the original dependent body after argument substitution. -/
theorem pi_beta {A : DisplayedFamily.{u, u, u, u} P}
    {B : DisplayedFamily.{u, u, u, u} (totalSpace A)}
    (body : B.sections) (argument : A.sections) :
    appDisplayed (lamDisplayed body) argument =
      reindexDisplayedSection (sectionLift A argument) B body := by
  unfold appDisplayed lamDisplayed
  rw [Equiv.symm_apply_apply]

/-- Eta recovers the function from its full natural evaluation body. -/
theorem pi_eta {A : DisplayedFamily.{u, u, u, u} P}
    {B : DisplayedFamily.{u, u, u, u} (totalSpace A)}
    (function : (piDisplayed A B).sections) :
    lamDisplayed ((piSectionEquiv A B).symm function) = function :=
  (piSectionEquiv A B).apply_symm_apply function

/-- Dependent products with beta over the same CwF already used for
substitution, context comprehension and dependent sums. -/
noncomputable def presheafProducts (C : Type u) [Category.{u} C] :
    DependentProductBeta (presheafCwf C) where
  pi := piDisplayed
  lam := lamDisplayed
  app := appDisplayed
  beta := pi_beta

/-- The common raw type-operation interface uses these qualified products. -/
noncomputable def presheafPiOperations (C : Type u) [Category.{u} C] :
    PiOperations (presheafCwf C) :=
  PiOperations.ofQualified (presheafProducts C)

theorem presheafPiOperations_beta (C : Type u) [Category.{u} C] :
    PiBeta (presheafPiOperations C) :=
  PiOperations.ofQualified_beta (presheafProducts C)

end Mettapedia.TypeTheory.DisplayedPresheafPi
