import Mettapedia.TypeTheory.DisplayedPresheafSlicePi
import Mettapedia.TypeTheory.DisplayedPresheafSliceSigma
import Mettapedia.TypeTheory.DisplayedPresheafPi
import Mettapedia.TypeTheory.DependentProductNativeComparison
import Mettapedia.TypeTheory.DependentProductRestrictionCoverage

/-!
# Theory change in the shared dependent native model

Precomposition acts on displayed families and their terms. Comprehension
and dependent sums retain both components. The dependent-product comparison
is induced by the already chosen indexed right adjoint. Context substitution
and changing the syntax category remain different operations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafTheoryRestriction

open CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSlicePi DisplayedPresheafSigma DisplayedPresheafPi
open DisplayedPresheafIndexedCwfBridge CategoryIndexedFamilyGeneralPi

universe u
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]

abbrev restrictFamily (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) : DisplayedFamily (F.op ⋙ P) :=
  Functor.Elements.precomp F.op P ⋙ A

def restrictTerm (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (term : A.sections) : (restrictFamily F P A).sections :=
  ⟨fun point => term.val ((Functor.Elements.precomp F.op P).obj point),
    fun arrow => term.property ((Functor.Elements.precomp F.op P).map arrow)⟩

def totalComparison (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) : totalSpace (restrictFamily F P A) ≅ F.op ⋙ totalSpace A :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y arrow
    ext receipt
    rfl)

theorem totalComparison_projection (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) :
    (totalComparison F P A).hom ≫ Functor.whiskerLeft F.op (totalProjection A) =
      totalProjection (restrictFamily F P A) := by
  ext X receipt
  rfl

theorem restrictTerm_id (P : Cᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    (term : A.sections) : restrictTerm (𝟭 C) P A term = term := rfl

theorem restrictTerm_comp (F : C ⥤ D) (G : D ⥤ E) (P : Eᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (term : A.sections) :
    restrictTerm (F ⋙ G) P A term =
      restrictTerm F (G.op ⋙ P) (restrictFamily G P A) (restrictTerm G P A term) := rfl

/-- Substitution of a context and restriction of its syntax commute on
the actual evidence-bearing families. -/
theorem restrict_substitution (F : C ⥤ D) {P Q : Dᵒᵖ ⥤ Type u}
    (substitution : Q ⟶ P) (A : DisplayedFamily P) :
    restrictFamily F Q (reindexDisplayed substitution A) =
      reindexDisplayed (Functor.whiskerLeft F.op substitution) (restrictFamily F P A) := rfl

theorem argumentComparison (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) :
    Functor.Elements.precomp (Functor.Elements.precomp F.op P) A ⋙
        displayedToTotalElements A =
      displayedToTotalElements (restrictFamily F P A) ⋙
        (totalComparison F P A).hom.mapElements ⋙
          Functor.Elements.precomp F.op (totalSpace A) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro first second arrow
  apply heq_of_eq
  apply CategoryOfElements.ext (totalSpace A)
  erw [displayedToTotalElements_underlying]
  change F.op.map arrow.val.val = F.op.map
    (((totalComparison F P A).hom.mapElements.map
      ((displayedToTotalElements (restrictFamily F P A)).map arrow)).val)
  apply congrArg F.op.map
  change arrow.val.val = ((displayedToTotalElements (restrictFamily F P A)).map arrow).val
  erw [displayedToTotalElements_underlying]

def codomainComparison (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    DependentProductRestriction.restrictedFamily (Functor.Elements.precomp F.op P) A
        (displayedToTotalElements A ⋙ B) ≅
      displayedToTotalElements (restrictFamily F P A) ⋙
        reindexDisplayed (totalComparison F P A).hom (restrictFamily F (totalSpace A) B) :=
  eqToIso (congrArg (fun projection => projection ⋙ B) (argumentComparison F P A))

set_option backward.isDefEq.respectTransparency false in
theorem codomainComparison_app (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (point : (restrictFamily F P A).Elements) :
    (codomainComparison F P A B).hom.app point = 𝟙 _ := by
  dsimp [codomainComparison]
  erw [eqToHom_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
def sumComparison (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    restrictFamily F P (sigmaDisplayed A B) ≅
      sigmaDisplayed (restrictFamily F P A)
        (reindexDisplayed (totalComparison F P A).hom (restrictFamily F (totalSpace A) B)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y arrow
    apply ConcreteCategory.hom_ext
    intro value
    change (sigmaDisplayed A B).map ((Functor.Elements.precomp F.op P).map arrow) value =
      (sigmaDisplayed (restrictFamily F P A)
        (reindexDisplayed (totalComparison F P A).hom (restrictFamily F (totalSpace A) B))).map
          arrow value
    change Sigma.mk ((restrictFamily F P A).map arrow value.1) _ =
      Sigma.mk ((restrictFamily F P A).map arrow value.1) _
    apply Sigma.ext (by rfl)
    apply heq_of_eq
    let first : (restrictFamily F P A).Elements := ⟨X, value.1⟩
    let second : (restrictFamily F P A).Elements :=
      ⟨Y, (restrictFamily F P A).map arrow value.1⟩
    let lifted : first ⟶ second := ⟨arrow, rfl⟩
    have square := ConcreteCategory.congr_hom
      ((codomainComparison F P A B).hom.naturality lifted) value.2
    erw [codomainComparison_app, codomainComparison_app] at square
    simp only [Category.comp_id, Category.id_comp] at square
    dsimp [first, second, lifted, CategoryIndexedFamilyTypeFormers.elementLift,
      CategoryOfElements.homMk, Functor.Elements.precomp] at square
    convert square using 1 <;> rfl)

/-- The comparison uses the native right-Kan product selected by the
displayed CwF, via its evaluation-preserving section presentation. -/
noncomputable def productComparison (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    restrictFamily F P (piDisplayed A B) ⟶
      piDisplayed (restrictFamily F P A)
        (reindexDisplayed (totalComparison F P A).hom (restrictFamily F (totalSpace A) B)) :=
  DependentProductNativeComparison.nativeRestriction
    (Functor.Elements.precomp F.op P) A (displayedToTotalElements A ⋙ B) ≫
      (CategoryOfElements.π (restrictFamily F P A)).ran.map
        (codomainComparison F P A B).hom

end Mettapedia.TypeTheory.DisplayedPresheafTheoryRestriction
