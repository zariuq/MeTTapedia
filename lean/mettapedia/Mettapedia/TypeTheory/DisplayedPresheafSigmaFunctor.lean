import Mettapedia.TypeTheory.DisplayedPresheafSliceSigma
import Mettapedia.TypeTheory.DisplayedPresheafEvidenceTransport

/-!
# Dependent sums as functors of native evidence families

The existing displayed dependent sum acts on maps of its dependent codomain.
Under comprehension this action is composition of slice projections. Its
comparison with dependent transport is natural in the codomain, so the
sum's adjunction uses the same evidence-bearing objects as the shared CwF.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafSigmaFunctor

open CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSlice DisplayedPresheafSliceSubstitution
open DisplayedPresheafSigma DisplayedPresheafSliceSigma
open DisplayedPresheafIndexedCwfBridge

universe u
variable {C : Type u} [Category.{u} C]
variable {P : Cᵒᵖ ⥤ Type u}

set_option backward.isDefEq.respectTransparency false in
/-- A dependent-sum map preserves the first witness and maps the evidence
depending on that very witness. -/
def sumMap (A : DisplayedFamily P)
    {B B' : DisplayedFamily (totalSpace A)} (operation : B ⟶ B') :
    sigmaDisplayed A B ⟶ sigmaDisplayed A B' where
  app point := TypeCat.ofHom fun value =>
    ⟨value.1, operation.app ⟨point.1, ⟨point.2, value.1⟩⟩ value.2⟩
  naturality X Y arrow := by
    ext value
    apply Sigma.ext (by rfl)
    apply heq_of_eq
    exact operation.naturality_apply
      ((displayedToTotalElements A).map
        (CategoryIndexedFamilyTypeFormers.elementLift
          (context := Cat.of P.Elements) A arrow value.1)) value.2

/-- The dependent sum already used by the displayed CwF, now on its full
category of proof-valued codomains. -/
def sumFunctor (A : DisplayedFamily P) :
    DisplayedFamily (totalSpace A) ⥤ DisplayedFamily P where
  obj B := sigmaDisplayed A B
  map operation := sumMap A operation
  map_id _ := by
    ext point value
    rfl
  map_comp _ _ := by
    ext point value
    rfl

/-- The family--slice comparison commutes with arbitrary evidence maps. -/
def sliceComparison (A : DisplayedFamily P) :
    sumFunctor A ⋙ totalFunctor P ≅
      totalFunctor (totalSpace A) ⋙ Over.map (totalProjection A) :=
  NatIso.ofComponents (sigmaSliceIso A) (by
    intro B B' operation
    ext point value
    rfl)

/-- Both sum constructions retain the same dependent witnesses. -/
def transportComparison (A : DisplayedFamily P) :
    sumFunctor A ≅ DisplayedPresheafEvidenceTransport.transportFunctor (totalProjection A) :=
  (Functor.rightUnitor (sumFunctor A)).symm ≪≫
    Functor.isoWhiskerLeft (sumFunctor A) (unitIso P) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sliceComparison A) (fibreFunctor P) ≪≫
    Functor.associator _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Native substitution is right adjoint to this very displayed sum. -/
noncomputable def sumAdjunction (A : DisplayedFamily P) :
    sumFunctor A ⊣ reindexFunctor (totalProjection A) :=
  (DisplayedPresheafEvidenceTransport.adjunction (totalProjection A)).ofNatIsoLeft
    (transportComparison A).symm

/-- The canonical comparison includes a dependent pair without replacing
either of its supplied values. -/
theorem transportComparison_value (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A)) (point : P.Elements)
    (value : (sigmaDisplayed A B).obj point) :
    ((transportComparison A).hom.app B).app point value =
      (⟨⟨⟨point.2, value.1⟩, value.2⟩, rfl⟩ :
        (DisplayedPresheafEvidenceTransport.transport (totalProjection A) B).obj point) := rfl

end Mettapedia.TypeTheory.DisplayedPresheafSigmaFunctor
