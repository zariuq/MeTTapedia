import Mettapedia.TypeTheory.PresheafEventCertificates

/-!
# Complete event readouts under source substitution

The chosen dependent-sum base-change comparison preserves the original
total certificate, not merely its support. For an event span this gives
both the actual pullback occurrence and the same dependent target witness.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSlice DisplayedPresheafSliceSubstitution
open DisplayedPresheafEvidenceTransport DisplayedPresheafEvidenceBaseChange

universe u
variable {C : Type u} [Category.{u} C]

namespace DisplayedPresheafSliceSubstitution

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the chosen comprehension pullback reads the same
original total element through its actual first projection. -/
@[reassoc] theorem reindexTotalIso_inv_readout
    {P Q : Cᵒᵖ ⥤ Type u} (f : Q ⟶ P) (A : DisplayedFamily P) :
    (reindexTotalIso f A).inv.left ≫ totalReindexMap f A =
      pullback.fst (totalProjection A) f := by
  calc
    _ = (reindexTotalIso f A).inv.left ≫
        (reindexTotalIso f A).hom.left ≫ pullback.fst (totalProjection A) f := by
      rw [reindexTotalIso_hom_fst]
    _ = _ := by
      rw [← Category.assoc]
      have inverse := congrArg Over.Hom.left (reindexTotalIso f A).inv_hom_id
      change (reindexTotalIso f A).inv.left ≫ (reindexTotalIso f A).hom.left = 𝟙 _ at inverse
      rw [inverse]
      exact Category.id_comp _

end DisplayedPresheafSliceSubstitution

namespace DisplayedPresheafEvidenceBaseChange

variable {P Q S T : Cᵒᵖ ⥤ Type u}
variable {top : S ⟶ P} {left : S ⟶ T} {right : P ⟶ Q} {bottom : T ⟶ Q}

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back the inverse sum-comprehension comparison keeps its
complete original value through the actual first pullback projection. -/
@[reassoc] theorem transportSliceComparison_pullback_readout
    (right : P ⟶ Q) (bottom : T ⟶ Q) (A : DisplayedFamily P) :
    ((Over.pullback bottom).map ((transportSliceComparison right).inv.app A)).left ≫
        pullback.fst (totalProjection (transport right A)) bottom =
      pullback.fst (totalProjection A ≫ right) bottom ≫ (totalIso right A).inv := by
  change pullback.lift
      (pullback.fst (totalProjection A ≫ right) bottom ≫ (totalIso right A).inv)
      (pullback.snd (totalProjection A ≫ right) bottom) _ ≫
      pullback.fst (totalProjection (transport right A)) bottom = _
  exact pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The family comparison is read through the independently constructed
slice-pasting comparison and the same chosen comprehension isomorphisms. -/
theorem sumBaseChange_total_factorization
    (square : IsPullback top left right bottom) (A : DisplayedFamily P) :
    totalHom ((sumBaseChange square).hom.app A) =
      (totalIso left (reindexDisplayed top A)).hom ≫
        (reindexTotalIso top A).hom.left ≫
        (SliceBeckChevalley.sigmaBaseChangeComponent square ((totalFunctor P).obj A)).hom.left ≫
        ((Over.pullback bottom).map ((transportSliceComparison right).inv.app A)).left ≫
        (reindexTotalIso bottom (transport right A)).inv.left := by
  have comparison := congrArg Over.Hom.left (sumBaseChange_comprehension square A)
  change totalHom ((sumBaseChange square).hom.app A) = _ at comparison
  rw [comparison]
  simp [sumBaseChangeOver, transportSliceComparison, substitutionIso,
    SliceBeckChevalley.sigmaBaseChange]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Complete dependent-sum base change retains the original supplied
total value through its original context map. -/
theorem sumBaseChange_total_readout
    (square : IsPullback top left right bottom) (A : DisplayedFamily P) :
    totalHom ((sumBaseChange square).hom.app A) ≫
        totalReindexMap bottom (transport right A) ≫ (totalIso right A).hom =
      (totalIso left (reindexDisplayed top A)).hom ≫ totalReindexMap top A := by
  rw [sumBaseChange_total_factorization]
  simp only [Category.assoc, reindexTotalIso_inv_readout_assoc]
  rw [transportSliceComparison_pullback_readout_assoc]
  rw [Iso.inv_hom_id, Category.comp_id]
  have pasted := SliceBeckChevalley.sigmaBaseChangeComponent_fst square ((totalFunctor P).obj A)
  change (SliceBeckChevalley.sigmaBaseChangeComponent square ((totalFunctor P).obj A)).hom.left ≫
      pullback.fst (totalProjection A ≫ right) bottom = pullback.fst (totalProjection A) top at pasted
  have full : (reindexTotalIso top A).hom.left ≫
      (SliceBeckChevalley.sigmaBaseChangeComponent square ((totalFunctor P).obj A)).hom.left ≫
      pullback.fst (totalProjection A ≫ right) bottom = totalReindexMap top A :=
    (congrArg (fun readout => (reindexTotalIso top A).hom.left ≫ readout) pasted).trans
      (reindexTotalIso_hom_fst top A)
  exact congrArg (fun readout => (totalIso left (reindexDisplayed top A)).hom ≫ readout) full

end DisplayedPresheafEvidenceBaseChange

namespace PresheafEventCertificates.EventSpan

variable {P Q R : Cᵒᵖ ⥤ Type u} (span : EventSpan P Q)

set_option backward.isDefEq.respectTransparency false in
/-- Source substitution retains the exact original event from the actual
chosen pullback occurrence. -/
theorem sourceSubstitution_eventReadout (change : R ⟶ P) (A : DisplayedFamily Q) :
    totalHom (span.sourceSubstitution change A).hom ≫
        totalReindexMap change (span.certificates A) ≫ span.eventReadout A =
      (span.restrictSource change).eventReadout A ≫ pullback.fst span.source change := by
  have complete := sumBaseChange_total_readout
    (IsPullback.of_hasPullback span.source change) (reindexDisplayed span.target A)
  change totalHom (span.sourceSubstitution change A).hom ≫
      totalReindexMap change (span.certificates A) ≫
      (span.certificateTotalIso A).hom =
    ((span.restrictSource change).certificateTotalIso A).hom ≫
      totalReindexMap (pullback.fst span.source change) (reindexDisplayed span.target A) at complete
  have readout := congrArg
    (fun mapping => mapping ≫ totalProjection (reindexDisplayed span.target A)) complete
  have projected := totalReindexMap_square (pullback.fst span.source change)
    (reindexDisplayed span.target A)
  change totalReindexMap (pullback.fst span.source change) (reindexDisplayed span.target A) ≫
      totalProjection (reindexDisplayed span.target A) =
    totalProjection (reindexDisplayed (span.restrictSource change).target A) ≫
      pullback.fst span.source change at projected
  have finalReadout := congrArg
    (fun mapping => ((span.restrictSource change).certificateTotalIso A).hom ≫ mapping) projected
  simpa only [eventReadout, Category.assoc] using readout.trans finalReadout

set_option backward.isDefEq.respectTransparency false in
/-- The same comparison retains the complete dependent target witness,
including its original actual endpoint. -/
theorem sourceSubstitution_resultReadout (change : R ⟶ P) (A : DisplayedFamily Q) :
    totalHom (span.sourceSubstitution change A).hom ≫
        totalReindexMap change (span.certificates A) ≫ span.resultReadout A =
      (span.restrictSource change).resultReadout A := by
  have complete := sumBaseChange_total_readout
    (IsPullback.of_hasPullback span.source change) (reindexDisplayed span.target A)
  change totalHom (span.sourceSubstitution change A).hom ≫
      totalReindexMap change (span.certificates A) ≫
      (span.certificateTotalIso A).hom =
    ((span.restrictSource change).certificateTotalIso A).hom ≫
      totalReindexMap (pullback.fst span.source change) (reindexDisplayed span.target A) at complete
  have readout := congrArg (fun mapping => mapping ≫ totalReindexMap span.target A) complete
  simpa only [resultReadout, Category.assoc, totalReindexMap_comp, restrictSource] using readout

end PresheafEventCertificates.EventSpan

end Mettapedia.TypeTheory
