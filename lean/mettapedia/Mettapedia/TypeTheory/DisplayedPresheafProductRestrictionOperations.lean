import Mettapedia.TypeTheory.DisplayedPresheafLogicalActionCoherence
import Mettapedia.TypeTheory.DependentProductRestrictionEvaluation

/-!
# Native function operations under theory restriction

The canonical colax product comparison acts on the supplied natural
function section. Its evaluation is compared at every dependent input;
invertibility of that comparison is not required for these operations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafProductRestrictionOperations

open _root_.CategoryTheory _root_.CategoryTheory.Functor
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafPi DisplayedPresheafSlicePi
open DisplayedPresheafIndexedCwfBridge CategoryIndexedFamilyGeneralPi
open DependentProductNativeComparison
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryRestrictionAction
open DisplayedPresheafLogicalActionCoherence

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]

noncomputable def restrictFunction (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (function : (piDisplayed A B).sections) :
    (piDisplayed (restrictFamily F P A) ((codomainFunctor F P A).obj B)).sections :=
  (Functor.sectionsFunctor _).map (productComparison F P A B)
    (restrictTerm F P (piDisplayed A B) function)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse native abstraction reads the very same future section
at its identity arrow and supplied dependent argument. -/
theorem abstraction_readout {P : Dᵒᵖ ⥤ Type u}
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (body : B.sections) (point future : P.Elements) (arrow : point ⟶ future)
    (argument : A.obj future) :
    ((((nativeIso A).hom.app (displayedToTotalElements A ⋙ B)).app point
        ((lamDisplayed body).val point)).app future arrow argument) =
      body.val ⟨future.1, ⟨future.2, argument⟩⟩ := by
  have square := nativeIso_abstraction A
    (H := (Functor.const P.Elements).obj PUnit)
    (B := displayedToTotalElements A ⋙ B)
    (Functor.whiskerLeft (displayedToTotalElements A) (B.sectionsEquivHom PUnit body))
  rw [← lamDisplayed_asIndexed body] at square
  have readout := congrArg (fun operation =>
    (operation.app point PUnit.unit).app future arrow argument) square
  exact readout

set_option backward.isDefEq.respectTransparency false in
theorem evaluation_readout {P : Dᵒᵖ ⥤ Type u}
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (function : (piDisplayed A B).sections) (point : P.Elements)
    (argument : A.obj point) :
    ((piSectionEquiv A B).symm function).val ⟨point.1, ⟨point.2, argument⟩⟩ =
      ((((nativeIso A).hom.app (displayedToTotalElements A ⋙ B)).app point
        (function.val point)).app point (𝟙 point) argument) := by
  have readout := abstraction_readout A B ((piSectionEquiv A B).symm function)
    point point (𝟙 point) argument
  rw [pi_eta] at readout
  exact readout.symm

set_option backward.isDefEq.respectTransparency false in
/-- The complete evaluation body of the restricted function is restriction
of its supplied body, including the actual comprehension comparison. -/
theorem evaluation_body (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (function : (piDisplayed A B).sections) :
    (piSectionEquiv (restrictFamily F P A) ((codomainFunctor F P A).obj B)).symm
        (restrictFunction F P A B function) =
      reindexDisplayedSection (totalComparison F P A).hom
        (restrictFamily F (totalSpace A) B)
        (restrictTerm F (totalSpace A) B ((piSectionEquiv A B).symm function)) := by
  apply (Functor.sections_ext_iff).2
  intro point
  let basePoint : (F.op ⋙ P).Elements := ⟨point.1, point.2.1⟩
  let argument : (restrictFamily F P A).obj basePoint := point.2.2
  have target := evaluation_readout (restrictFamily F P A)
    ((codomainFunctor F P A).obj B) (restrictFunction F P A B function) basePoint argument
  have comparison := productComparison_readout F P A B basePoint basePoint (𝟙 basePoint)
    (function.val ((Functor.Elements.precomp F.op P).obj basePoint)) argument
  have identityReadout := congrArg (fun arrow =>
    ((((nativeIso A).hom.app (displayedToTotalElements A ⋙ B)).app
      ((Functor.Elements.precomp F.op P).obj basePoint)
      (function.val ((Functor.Elements.precomp F.op P).obj basePoint))).app
      ((Functor.Elements.precomp F.op P).obj basePoint) arrow argument))
    ((Functor.Elements.precomp F.op P).map_id basePoint)
  have source := evaluation_readout A B function
    ((Functor.Elements.precomp F.op P).obj basePoint) argument
  exact target.trans (comparison.trans (identityReadout.trans source.symm))

set_option backward.isDefEq.respectTransparency false in
/-- Restriction commutes with native abstraction through the canonical
colax comparison, without a coverage or invertibility assumption. -/
theorem abstraction (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (body : B.sections) :
    restrictFunction F P A B (lamDisplayed body) =
      lamDisplayed (reindexDisplayedSection (totalComparison F P A).hom
        (restrictFamily F (totalSpace A) B) (restrictTerm F (totalSpace A) B body)) := by
  apply (piSectionEquiv (restrictFamily F P A) ((codomainFunctor F P A).obj B)).symm.injective
  rw [evaluation_body]
  change reindexDisplayedSection (totalComparison F P A).hom
      (restrictFamily F (totalSpace A) B)
      (restrictTerm F (totalSpace A) B ((piSectionEquiv A B).symm (piSectionEquiv A B body))) = _
  rw [Equiv.symm_apply_apply]
  exact ((piSectionEquiv (restrictFamily F P A) ((codomainFunctor F P A).obj B)).symm_apply_apply
    (reindexDisplayedSection (totalComparison F P A).hom
      (restrictFamily F (totalSpace A) B) (restrictTerm F (totalSpace A) B body))).symm

set_option backward.isDefEq.respectTransparency false in
/-- Applying the changed-theory function returns the original supplied
dependent result at the actual image world and argument. -/
theorem application_value (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (function : (piDisplayed A B).sections) (argument : A.sections)
    (point : (F.op ⋙ P).Elements) :
    (appDisplayed (restrictFunction F P A B function)
      (restrictTerm F P A argument)).val point =
      (appDisplayed function argument).val ((Functor.Elements.precomp F.op P).obj point) := by
  exact congrArg (fun body => body.val
    ⟨point.1, ⟨point.2, (restrictTerm F P A argument).val point⟩⟩)
    (evaluation_body F P A B function)

set_option backward.isDefEq.respectTransparency false in
/-- Restricting along the identity theory leaves every function section
unchanged, including its values at future arrows. -/
theorem identity (P : Cᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A)) (function : (piDisplayed A B).sections) :
    restrictFunction (𝟭 C) P A B function = function := by
  unfold restrictFunction
  rw [productComparison_identity, restrictTerm_id]
  exact ConcreteCategory.congr_hom
    ((Functor.sectionsFunctor P.Elements).map_id (piDisplayed A B)) function

/-- Two theory changes transport the entire supplied function by the
same natural map as their composite. -/
theorem composition {E : Type u} [Category.{u} E]
    (F : C ⥤ D) (G : D ⥤ E) (P : Eᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (function : (piDisplayed A B).sections) :
    restrictFunction (F ⋙ G) P A B function =
      (Functor.sectionsFunctor _).map
        ((whiskerRight (productMap G P A) (restrictionFunctor F (G.op ⋙ P)) ≫
          whiskerLeft (codomainFunctor G P A)
            (productMap F (G.op ⋙ P) (restrictFamily G P A))).app B)
        (restrictTerm (F ⋙ G) P (piDisplayed A B) function) := by
  unfold restrictFunction
  rw [← productMap_app, productMap_composition]
  rfl

/-- Applying the two canonical section transports successively is equal
to the transport along their composite, on the supplied whole function. -/
theorem composition_sections {E : Type u} [Category.{u} E]
    (F : C ⥤ D) (G : D ⥤ E) (P : Eᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (function : (piDisplayed A B).sections) :
    restrictFunction (F ⋙ G) P A B function =
      restrictFunction F (G.op ⋙ P) (restrictFamily G P A)
        ((codomainFunctor G P A).obj B) (restrictFunction G P A B function) := by
  unfold restrictFunction
  rw [← productMap_app (F ⋙ G), productMap_composition]
  apply Functor.sections_ext_iff.mpr
  intro point
  rfl

end Mettapedia.TypeTheory.DisplayedPresheafProductRestrictionOperations
