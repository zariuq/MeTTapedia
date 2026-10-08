import Mettapedia.TypeTheory.DisplayedPresheafTheoryRestriction
import Mettapedia.GSLT.Topos.ClassifierRestriction

/-!
# Invertible dependent native comparisons under equivalence of theories

The already constructed product and classifier comparisons are invertible
for an equivalence of syntax categories. The product comparison passes
through the evidence-bearing element category and its future arguments.
This is a sufficient preservation contract, not an assertion that every
syntax translation is an equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafTheoryRestrictionIso

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafPi
open DisplayedPresheafTheoryRestriction

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]

noncomputable def productIso (F : C ⥤ D) [F.IsEquivalence]
    (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A)) :
    restrictFamily F P (piDisplayed A B) ≅
      piDisplayed (restrictFamily F P A)
        (reindexDisplayed (totalComparison F P A).hom (restrictFamily F (totalSpace A) B)) := by
  let changed := CategoryOfElementsBaseChange.precompElementsEquivalence F.op.asEquivalence P
  letI : (Functor.Elements.precomp F.op P).IsEquivalence := by
    change changed.functor.IsEquivalence
    infer_instance
  exact DependentProductNativeComparison.nativeRestrictionIso
    (Functor.Elements.precomp F.op P) A
      (DisplayedPresheafIndexedCwfBridge.displayedToTotalElements A ⋙ B) ≪≫
        (CategoryOfElements.π (restrictFamily F P A)).ran.mapIso (codomainComparison F P A B)

theorem productIso_hom (F : C ⥤ D) [F.IsEquivalence]
    (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A)) :
    (productIso F P A B).hom = productComparison F P A B := rfl

noncomputable def classifierIso (F : C ⥤ D) [F.IsEquivalence] :
    F.op ⋙ Mettapedia.GSLT.Topos.omegaFunctor (C := D) ≅
      Mettapedia.GSLT.Topos.omegaFunctor (C := C) :=
  Mettapedia.GSLT.Topos.ClassifierRestriction.comparisonIso F

end Mettapedia.TypeTheory.DisplayedPresheafTheoryRestrictionIso
