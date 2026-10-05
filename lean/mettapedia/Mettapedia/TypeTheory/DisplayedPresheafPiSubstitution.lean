import Mettapedia.TypeTheory.DisplayedPresheafPi
import Mettapedia.TypeTheory.DisplayedPresheafSigma
import Mettapedia.TypeTheory.PresheafPiIndexedCwfBridge

/-!
# Substitution for displayed-presheaf dependent functions

The natural-context base-change theorem for the existing indexed-family
Pi is transported to the same displayed families used by the presheaf CwF.
The codomain comparison is the already proved total-element substitution
square, retaining dependent witnesses and their contextual action.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafPiSubstitution

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafIndexedCwfBridge DisplayedPresheafPi
open CategoryOfElementsBaseChange CategoryIndexedFamilyGeneralPi
open PresheafPiIndexedCwfBridge

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q : Face.{u, u, u} C}

/-- The substituted displayed codomain is exactly the existing indexed
codomain after its evidence-retaining lift. -/
theorem codomainBaseChange (f : Q ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A)) :
    displayedToTotalElements (reindexDisplayed f A) ⋙
        reindexDisplayed (totalReindexMap f A) B =
      mapPrecompElements f.mapElements A ⋙ (displayedToTotalElements A ⋙ B) := by
  have square := DisplayedPresheafSigma.indexedLift_totalSquare f A
  exact congrArg (fun k => k ⋙ B) square.symm

set_option backward.isDefEq.respectTransparency false in
/-- The codomain regrouping transports only contextual indexing; at an
individual argument it leaves the evidence value untouched. -/
theorem codomainBaseChange_app (f : Q ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A))
    (point : (reindexDisplayed f A).Elements) :
    (eqToHom (codomainBaseChange f A B)).app point = 𝟙 _ := by
  rw [eqToHom_app]
  rfl

/-- Dependent function formation commutes with every natural context
substitution, via the existing indexed-family base-change isomorphism. -/
noncomputable def piSubstitutionIso (f : Q ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A)) :
    piDisplayed (reindexDisplayed f A)
        (reindexDisplayed (totalReindexMap f A) B) ≅
      reindexDisplayed f (piDisplayed A B) :=
  ((CategoryOfElements.π (reindexDisplayed f A)).ran).mapIso
      (eqToIso (codomainBaseChange f A B)) ≪≫
    presheafGeneralPi_formation_baseChangeIso f A (displayedToTotalElements A ⋙ B)

theorem piSubstitutionIso_hom (f : Q ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A)) :
    (piSubstitutionIso f A B).hom =
      ((CategoryOfElements.π (reindexDisplayed f A)).ran).map
          (eqToHom (codomainBaseChange f A B)) ≫
        (presheafGeneralPi_formation_baseChangeIso f A
          (displayedToTotalElements A ⋙ B)).hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Identity substitution gives the identity comparison, including its
inverse transport on dependent functions. -/
theorem piSubstitutionIso_id (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A)) :
    piSubstitutionIso (𝟙 P) A B = Iso.refl (piDisplayed A B) := by
  simp [piSubstitutionIso, presheafGeneralPi_baseChangeIso_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Lambda abstraction commutes with substitution in the presheaf CwF.
The formation comparison transports the resulting function section, and
the body is the original section reindexed through context extension. -/
theorem lam_substitution (f : Q ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A)) (body : B.sections) :
    (piDisplayed (reindexDisplayed f A)
        (reindexDisplayed (totalReindexMap f A) B)).sectionsEquivHom PUnit
        (lamDisplayed (reindexDisplayedSection (totalReindexMap f A) B body)) ≫
      (piSubstitutionIso f A B).hom =
    Functor.whiskerLeft f.mapElements
      ((piDisplayed A B).sectionsEquivHom PUnit (lamDisplayed body)) := by
  rw [lamDisplayed_asIndexed, lamDisplayed_asIndexed]
  let A' := reindexDisplayed f A
  let B' := reindexDisplayed (totalReindexMap f A) B
  let body' := Functor.whiskerLeft (displayedToTotalElements A')
    (B'.sectionsEquivHom PUnit
      (reindexDisplayedSection (totalReindexMap f A) B body))
  have bodyComparison : body' ≫ eqToHom (codomainBaseChange f A B) =
      Functor.whiskerLeft (mapPrecompElements f.mapElements A)
        (Functor.whiskerLeft (displayedToTotalElements A)
          (B.sectionsEquivHom PUnit body)) := by
    ext point
    rw [NatTrans.comp_app, codomainBaseChange_app, Category.comp_id]
    rfl
  have transposePost :=
    (generalPiAdjunction (context := Cat.of Q.Elements) A').homEquiv_naturality_right
      (X := (Functor.const Q.Elements).obj PUnit)
      body' (eqToHom (codomainBaseChange f A B))
  rw [piSubstitutionIso_hom, ← Category.assoc]
  refine (congrArg (fun k => k ≫
    (presheafGeneralPi_formation_baseChangeIso f A
      (displayedToTotalElements A ⋙ B)).hom) transposePost.symm).trans ?_
  rw [bodyComparison]
  exact presheafGeneralPi_transpose_baseChange f A
    (displayedToTotalElements A ⋙ B)
    (head := (Functor.const P.Elements).obj PUnit)
    (Functor.whiskerLeft (displayedToTotalElements A)
      (B.sectionsEquivHom PUnit body))

set_option backward.isDefEq.respectTransparency false in
/-- The abstraction-substitution law as equality of the actual CwF terms. -/
theorem lam_substitution_section (f : Q ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A)) (body : B.sections) :
    (Functor.sectionsFunctor Q.Elements).map (piSubstitutionIso f A B).hom
        (lamDisplayed (reindexDisplayedSection (totalReindexMap f A) B body)) =
      reindexDisplayedSection f (piDisplayed A B) (lamDisplayed body) := by
  apply ((reindexDisplayed f (piDisplayed A B)).sectionsEquivHom PUnit).injective
  rw [Functor.sectionsEquivHom_naturality]
  exact lam_substitution f A B body

/-- Reindex a function term through the canonical formation comparison. -/
noncomputable def reindexFunction (f : Q ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A))
    (function : (piDisplayed A B).sections) :
    (piDisplayed (reindexDisplayed f A)
      (reindexDisplayed (totalReindexMap f A) B)).sections :=
  (Functor.sectionsFunctor Q.Elements).map (piSubstitutionIso f A B).inv
    (reindexDisplayedSection f (piDisplayed A B) function)

set_option backward.isDefEq.respectTransparency false in
/-- Reindexing an abstraction gives the abstraction of its reindexed body. -/
theorem reindexFunction_lam (f : Q ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A)) (body : B.sections) :
    reindexFunction f A B (lamDisplayed body) =
      lamDisplayed (reindexDisplayedSection (totalReindexMap f A) B body) := by
  unfold reindexFunction
  rw [← lam_substitution_section f A B body]
  exact (ConcreteCategory.congr_hom
    ((Functor.sectionsFunctor Q.Elements).mapIso (piSubstitutionIso f A B)).hom_inv_id _)

/-- Application commutes with substitution, including the dependent
codomain transport already used by the CwF's sum operations. -/
theorem app_substitution (f : Q ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A))
    (function : (piDisplayed A B).sections) (argument : A.sections) :
    appDisplayed (reindexFunction f A B function)
        (reindexDisplayedSection f A argument) =
      DisplayedPresheafCwf.reindexDependentSection f A B argument
        (appDisplayed function argument) := by
  obtain ⟨body, rfl⟩ := (piSectionEquiv A B).surjective function
  change appDisplayed (reindexFunction f A B (lamDisplayed body)) _ =
    DisplayedPresheafCwf.reindexDependentSection f A B argument
      (appDisplayed (lamDisplayed body) argument)
  rw [reindexFunction_lam, pi_beta, pi_beta]
  apply (Functor.sections_ext_iff).2
  intro point
  exact eq_of_heq
    (DisplayedPresheafCwf.reindexDependentSection_value_heq f A B argument
      (reindexDisplayedSection (sectionLift A argument) B body) point).symm

end Mettapedia.TypeTheory.DisplayedPresheafPiSubstitution
