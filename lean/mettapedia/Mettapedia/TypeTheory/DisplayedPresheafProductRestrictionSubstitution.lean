import Mettapedia.TypeTheory.DependentProductPresheafSubstitution
import Mettapedia.TypeTheory.DisplayedPresheafProductRestrictionOperations
import Mettapedia.TypeTheory.DisplayedPresheafPiSubstitutionCoherence
import Mettapedia.TypeTheory.DependentProductArgumentTransport
import Mettapedia.TypeTheory.DisplayedPresheafProductTransformationCoherence

/-!
# Native products under program and theory substitution

Program substitution and change of theory use independent canonical
comparisons. Their mixed square retains the entire supplied dependent
function and the actual comprehension lift of its argument context.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafProductRestrictionSubstitution

open _root_.CategoryTheory _root_.CategoryTheory.Functor
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafPi DisplayedPresheafSlicePi DisplayedPresheafSliceSubstitution
open DisplayedPresheafIndexedCwfBridge CategoryIndexedFamilyGeneralPi
open DisplayedPresheafPiSubstitution DependentProductNativeComparison
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryRestrictionAction
open DisplayedPresheafLogicalActionCoherence
open DisplayedPresheafProductTransformationCoherence
open DisplayedPresheafProductRestrictionOperations
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {P Q : Dᵒᵖ ⥤ Type u}

/-- The actual argument-context lifts commute with theory restriction. -/
theorem total_interchange (F : C ⥤ D) (substitution : Q ⟶ P) (A : DisplayedFamily P) :
    (totalComparison F Q (reindexDisplayed substitution A)).hom ≫
        whiskerLeft F.op (totalReindexMap substitution A) =
      totalReindexMap (whiskerLeft F.op substitution) (restrictFamily F P A) ≫
        (totalComparison F P A).hom := by
  ext world receipt
  rfl

/-- The two independent codomain indexing routes retain the same total
receipt and the same contextual arrow action. -/
theorem codomain_interchange (F : C ⥤ D) (substitution : Q ⟶ P)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    (codomainFunctor F Q (reindexDisplayed substitution A)).obj
        (reindexDisplayed (totalReindexMap substitution A) B) =
      reindexDisplayed
        (totalReindexMap (whiskerLeft F.op substitution) (restrictFamily F P A))
        ((codomainFunctor F P A).obj B) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro source target arrow
  apply heq_of_eq
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem codomain_interchange_app (F : C ⥤ D) (substitution : Q ⟶ P)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (point : (totalSpace (restrictFamily F Q (reindexDisplayed substitution A))).Elements) :
    (eqToHom (codomain_interchange F substitution A B)).app point = 𝟙 _ := by
  rw [eqToHom_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse chosen formation comparison is the actual native
restriction along program elements, followed by its earned regrouping. -/
theorem substitution_inverse (substitution : Q ⟶ P) (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A)) :
    (piSubstitutionIso substitution A B).inv =
      nativeRestriction substitution.mapElements A (displayedToTotalElements A ⋙ B) ≫
        (CategoryOfElements.π (reindexDisplayed substitution A)).ran.map
          (eqToHom (codomainBaseChange substitution A B).symm) := by
  rw [DependentProductPresheafSubstitution.comparison_inverse]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem codomainBaseChange_inverse_app (substitution : Q ⟶ P) (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A)) (point : (reindexDisplayed substitution A).Elements) :
    (eqToHom (codomainBaseChange substitution A B).symm).app point = 𝟙 _ := by
  rw [eqToHom_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Substituting the complete native function preserves every future
argument readout through the actual map of program elements. -/
theorem substitution_readout (substitution : Q ⟶ P) (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A)) (point future : Q.Elements) (arrow : point ⟶ future)
    (function : (reindexDisplayed substitution (piDisplayed A B)).obj point)
    (argument : (reindexDisplayed substitution A).obj future) :
    ((((nativeIso (reindexDisplayed substitution A)).hom.app
        (displayedToTotalElements (reindexDisplayed substitution A) ⋙
          reindexDisplayed (totalReindexMap substitution A) B)).app point
        ((piSubstitutionIso substitution A B).inv.app point function)).app future arrow argument) =
      ((((nativeIso A).hom.app (displayedToTotalElements A ⋙ B)).app
        (substitution.mapElements.obj point) function).app
          (substitution.mapElements.obj future) (substitution.mapElements.map arrow) argument) := by
  let regroup := eqToHom (codomainBaseChange substitution A B).symm
  let restricted := nativeRestriction substitution.mapElements A (displayedToTotalElements A ⋙ B)
  have square := congrArg (fun operation => operation.app point (restricted.app point function))
    ((nativeIso (reindexDisplayed substitution A)).hom.naturality regroup)
  have readout := congrArg (fun functionValue :
      DependentSection (reindexDisplayed substitution A)
        (displayedToTotalElements (reindexDisplayed substitution A) ⋙
          reindexDisplayed (totalReindexMap substitution A) B) point =>
      functionValue.app future arrow argument) square
  change _ = regroup.app (⟨future, argument⟩ : (reindexDisplayed substitution A).Elements)
    (((((nativeIso (reindexDisplayed substitution A)).hom.app
      (CategoryOfElementsBaseChange.mapPrecompElements substitution.mapElements A ⋙
        displayedToTotalElements A ⋙ B)).app point
          (restricted.app point function)).app future arrow argument)) at readout
  erw [codomainBaseChange_inverse_app] at readout
  rw [substitution_inverse]
  exact readout.trans
    (DependentProductArgumentTransport.nativeRestriction_readout substitution.mapElements A
      (displayedToTotalElements A ⋙ B) function future arrow argument)

set_option backward.isDefEq.respectTransparency false in
/-- Every future readout of the program-first route is the original
function at the actual composite map of elements. -/
theorem program_then_theory_readout (F : C ⥤ D) (substitution : Q ⟶ P)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (point future : (F.op ⋙ Q).Elements) (arrow : point ⟶ future)
    (function : (restrictFamily F Q (reindexDisplayed substitution (piDisplayed A B))).obj point)
    (argument : (restrictFamily F Q (reindexDisplayed substitution A)).obj future) :
    ((((nativeIso (restrictFamily F Q (reindexDisplayed substitution A))).hom.app
        (displayedToTotalElements (restrictFamily F Q (reindexDisplayed substitution A)) ⋙
          reindexDisplayed
            (totalReindexMap (whiskerLeft F.op substitution) (restrictFamily F P A))
            ((codomainFunctor F P A).obj B))).app point
      (((displayedProductFunctor (restrictFamily F Q (reindexDisplayed substitution A))).map
        (eqToHom (codomain_interchange F substitution A B))).app point
          ((productComparison F Q (reindexDisplayed substitution A)
            (reindexDisplayed (totalReindexMap substitution A) B)).app point
              ((piSubstitutionIso substitution A B).inv.app
                ((Functor.Elements.precomp F.op Q).obj point) function)))).app
      future arrow argument) =
    ((((nativeIso A).hom.app (displayedToTotalElements A ⋙ B)).app
      (substitution.mapElements.obj ((Functor.Elements.precomp F.op Q).obj point)) function).app
        (substitution.mapElements.obj ((Functor.Elements.precomp F.op Q).obj future))
        (substitution.mapElements.map ((Functor.Elements.precomp F.op Q).map arrow)) argument) := by
  let substituted := (piSubstitutionIso substitution A B).inv.app
    ((Functor.Elements.precomp F.op Q).obj point) function
  have regroup := productBodyMap_readout
    (restrictFamily F Q (reindexDisplayed substitution A))
    (eqToHom (codomain_interchange F substitution A B)) point future arrow
    ((productComparison F Q (reindexDisplayed substitution A)
      (reindexDisplayed (totalReindexMap substitution A) B)).app point substituted) argument
  erw [codomain_interchange_app] at regroup
  have theory := productComparison_readout F Q (reindexDisplayed substitution A)
    (reindexDisplayed (totalReindexMap substitution A) B) point future arrow substituted argument
  have program := substitution_readout substitution A B
    ((Functor.Elements.precomp F.op Q).obj point)
    ((Functor.Elements.precomp F.op Q).obj future)
    ((Functor.Elements.precomp F.op Q).map arrow) function argument
  exact regroup.trans (theory.trans program)

set_option backward.isDefEq.respectTransparency false in
/-- Every future readout of the theory-first route retains the same
original supplied function, with its program map still explicit. -/
theorem theory_then_program_readout (F : C ⥤ D) (substitution : Q ⟶ P)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (point future : (F.op ⋙ Q).Elements) (arrow : point ⟶ future)
    (function : (restrictFamily F Q (reindexDisplayed substitution (piDisplayed A B))).obj point)
    (argument : (reindexDisplayed (whiskerLeft F.op substitution) (restrictFamily F P A)).obj future) :
    ((((nativeIso (reindexDisplayed (whiskerLeft F.op substitution) (restrictFamily F P A))).hom.app
        (displayedToTotalElements
            (reindexDisplayed (whiskerLeft F.op substitution) (restrictFamily F P A)) ⋙
          reindexDisplayed
            (totalReindexMap (whiskerLeft F.op substitution) (restrictFamily F P A))
            ((codomainFunctor F P A).obj B))).app point
      ((piSubstitutionIso (whiskerLeft F.op substitution) (restrictFamily F P A)
        ((codomainFunctor F P A).obj B)).inv.app point
          ((productComparison F P A B).app
            ((whiskerLeft F.op substitution).mapElements.obj point) function))).app
      future arrow argument) =
    ((((nativeIso A).hom.app (displayedToTotalElements A ⋙ B)).app
      ((Functor.Elements.precomp F.op P).obj ((whiskerLeft F.op substitution).mapElements.obj point))
        function).app
        ((Functor.Elements.precomp F.op P).obj ((whiskerLeft F.op substitution).mapElements.obj future))
        ((Functor.Elements.precomp F.op P).map ((whiskerLeft F.op substitution).mapElements.map arrow))
        argument) := by
  have program := substitution_readout (whiskerLeft F.op substitution) (restrictFamily F P A)
    ((codomainFunctor F P A).obj B) point future arrow
    ((productComparison F P A B).app ((whiskerLeft F.op substitution).mapElements.obj point) function)
    argument
  have theory := productComparison_readout F P A B
    ((whiskerLeft F.op substitution).mapElements.obj point)
    ((whiskerLeft F.op substitution).mapElements.obj future)
    ((whiskerLeft F.op substitution).mapElements.map arrow) function argument
  exact program.trans theory

set_option backward.isDefEq.respectTransparency false in
/-- Program substitution and theory restriction commute on the complete
chosen native product. The program comparison is invertible; the theory
comparison is used only in its genuine colax direction. -/
theorem comparison_substitution (F : C ⥤ D) (substitution : Q ⟶ P)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A)) :
    (restrictionFunctor F Q).map (piSubstitutionIso substitution A B).inv ≫
        productComparison F Q (reindexDisplayed substitution A)
          (reindexDisplayed (totalReindexMap substitution A) B) ≫
        (displayedProductFunctor (restrictFamily F Q (reindexDisplayed substitution A))).map
          (eqToHom (codomain_interchange F substitution A B)) =
      (reindexFunctor (whiskerLeft F.op substitution)).map (productComparison F P A B) ≫
        (piSubstitutionIso (whiskerLeft F.op substitution) (restrictFamily F P A)
          ((codomainFunctor F P A).obj B)).inv := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro function
  let domain := restrictFamily F Q (reindexDisplayed substitution A)
  let body := reindexDisplayed
    (totalReindexMap (whiskerLeft F.op substitution) (restrictFamily F P A))
    ((codomainFunctor F P A).obj B)
  apply (((nativeIso domain).app (displayedToTotalElements domain ⋙ body)).app
    point).toEquiv.injective
  apply DependentSection.ext
  intro future arrow argument
  change ((((nativeIso domain).hom.app (displayedToTotalElements domain ⋙ body)).app point
      (((displayedProductFunctor domain).map
        (eqToHom (codomain_interchange F substitution A B))).app point
          ((productComparison F Q (reindexDisplayed substitution A)
            (reindexDisplayed (totalReindexMap substitution A) B)).app point
              ((piSubstitutionIso substitution A B).inv.app
                ((Functor.Elements.precomp F.op Q).obj point) function)))).app
      future arrow argument) =
    ((((nativeIso domain).hom.app (displayedToTotalElements domain ⋙ body)).app point
      ((piSubstitutionIso (whiskerLeft F.op substitution) (restrictFamily F P A)
        ((codomainFunctor F P A).obj B)).inv.app point
          ((productComparison F P A B).app
            ((whiskerLeft F.op substitution).mapElements.obj point) function))).app
      future arrow argument)
  exact (program_then_theory_readout F substitution A B point future arrow function argument).trans
    (theory_then_program_readout F substitution A B point future arrow function argument).symm

set_option backward.isDefEq.respectTransparency false in
/-- The full mixed square acts on every supplied natural function term,
rather than merely asserting that its target family is inhabited. -/
theorem function_substitution (F : C ⥤ D) (substitution : Q ⟶ P)
    (A : DisplayedFamily P) (B : DisplayedFamily (totalSpace A))
    (function : (piDisplayed A B).sections) :
    (Functor.sectionsFunctor _).map
      ((displayedProductFunctor (restrictFamily F Q (reindexDisplayed substitution A))).map
        (eqToHom (codomain_interchange F substitution A B)))
      (restrictFunction F Q (reindexDisplayed substitution A)
        (reindexDisplayed (totalReindexMap substitution A) B)
        (reindexFunction substitution A B function)) =
      reindexFunction (whiskerLeft F.op substitution) (restrictFamily F P A)
        ((codomainFunctor F P A).obj B) (restrictFunction F P A B function) := by
  apply Functor.sections_ext_iff.mpr
  intro point
  exact ConcreteCategory.congr_hom (C := Type u)
    (congrArg (fun operation => operation.app point)
      (comparison_substitution F substitution A B))
    (function.val (substitution.mapElements.obj ((Functor.Elements.precomp F.op Q).obj point)))

end Mettapedia.TypeTheory.DisplayedPresheafProductRestrictionSubstitution
