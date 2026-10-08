import Mettapedia.TypeTheory.DisplayedPresheafEvidenceUniversal

/-!
# Comparing computational and slice-derived native sum adjunctions

The same family functors have an adjunction obtained from slice semantics
and a computational adjunction obtained by eliminating retained receipts.
Adjoint uniqueness compares these presentations canonically. The comparison
respects their units and arbitrary target readouts; equality of chosen
units is not assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafEvidenceAdjunctionComparison

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution DisplayedPresheafEvidenceTransport
open DisplayedPresheafEvidenceUniversal

universe u
variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}

noncomputable def comparison (f : P ⟶ Q) : transportFunctor f ≅ transportFunctor f :=
  Adjunction.leftAdjointUniq (adjunction f) (receiptAdjunction f)

theorem comparison_unit (f : P ⟶ Q) (A : DisplayedFamily P) :
    (adjunction f).unit.app A ≫ (reindexFunctor f).map ((comparison f).hom.app A) =
      unit f A :=
  (Adjunction.unit_leftAdjointUniq_hom_app (adjunction f) (receiptAdjunction f) A).trans
    (receiptAdjunction_unit f A)

/-- The canonical comparison sends the slice-derived unit witness to the
literal supplied certificate of the computational presentation. -/
theorem comparison_supplied_certificate (f : P ⟶ Q) (A : DisplayedFamily P)
    (point : P.Elements) (evidence : A.obj point) :
    ((comparison f).hom.app A).app (f.mapElements.obj point)
        (((adjunction f).unit.app A).app point evidence) =
      (unit f A).app point evidence :=
  congrArg (fun result : A ⟶ reindexDisplayed f (transport f A) =>
    result.app point evidence) (comparison_unit f A)

set_option backward.isDefEq.respectTransparency false in
/-- Any readout constructed by the original slice adjunction is the same
readout as receipt elimination, after its canonical presentation change. -/
theorem comparison_elimination (f : P ⟶ Q)
    {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B) :
    ((adjunction f).homEquiv A B).symm body =
      (comparison f).hom.app A ≫ descend f body := by
  apply ((adjunction f).homEquiv A B).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit,
    Functor.map_comp, ← Category.assoc, comparison_unit]
  exact (beta f body).symm

theorem comparison_readout_computes (f : P ⟶ Q)
    {A : DisplayedFamily P} {B : DisplayedFamily Q}
    (body : A ⟶ reindexDisplayed f B) (point : P.Elements) (evidence : A.obj point) :
    (((comparison f).hom.app A ≫ descend f body).app (f.mapElements.obj point))
        (((adjunction f).unit.app A).app point evidence) = body.app point evidence := by
  change (descend f body).app _
    (((comparison f).hom.app A).app _ (((adjunction f).unit.app A).app point evidence)) = _
  rw [comparison_supplied_certificate, descend_unit]

end Mettapedia.TypeTheory.DisplayedPresheafEvidenceAdjunctionComparison
