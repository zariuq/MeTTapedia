import Mettapedia.TypeTheory.DisplayedPresheafEvidenceUniversal
import Mettapedia.TypeTheory.SliceBeckChevalley

/-!
# Substitution of proof-retaining native sums

The arbitrary-map dependent sum agrees naturally with actual slice
composition. Pullback pasting then supplies Beck--Chevalley for these
same evidence families. The comparison is a map of complete certificates,
not merely an equivalence of their support predicates.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafEvidenceBaseChange

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafSliceSubstitution DisplayedPresheafEvidenceTransport

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q S T : Cᵒᵖ ⥤ Type u}

/-- Comprehension of the retained sum is the original total, projected
through the given program map, naturally in all evidence maps. -/
def transportSliceComparison (f : P ⟶ Q) :
    transportFunctor f ⋙ totalFunctor Q ≅ totalFunctor P ⋙ Over.map f :=
  NatIso.ofComponents
    (fun A => Over.isoMk (totalIso f A) (totalIso_projection f A))
    (by
      intro A B evidenceMap
      ext world receipt
      rfl)

variable {top : S ⟶ P} {left : S ⟶ T} {right : P ⟶ Q} {bottom : T ⟶ Q}

set_option backward.isDefEq.respectTransparency false in
/-- The actual family-level sum comparison, after comprehension, is
exactly the slice pullback-pasting comparison. -/
noncomputable def sumBaseChangeOver (square : IsPullback top left right bottom) :
    (reindexFunctor top ⋙ transportFunctor left) ⋙ totalFunctor T ≅
      (transportFunctor right ⋙ reindexFunctor bottom) ⋙ totalFunctor T :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (reindexFunctor top) (transportSliceComparison left) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (substitutionIso top) (Over.map left) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (totalFunctor P) (SliceBeckChevalley.sigmaBaseChange square) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (transportSliceComparison right).symm (Over.pullback bottom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (transportFunctor right) (substitutionIso bottom).symm ≪≫
    (Functor.associator _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Dependent evidence transport commutes with context substitution
around a pullback square. Full faithfulness of comprehension recovers
the comparison on families from its already constructed total map. -/
noncomputable def sumBaseChange (square : IsPullback top left right bottom) :
    reindexFunctor top ⋙ transportFunctor left ≅
      transportFunctor right ⋙ reindexFunctor bottom := by
  have : (totalFunctor T).Full := (equivalence T).fullyFaithfulFunctor.full
  have : (totalFunctor T).Faithful := (equivalence T).fullyFaithfulFunctor.faithful
  exact Functor.fullyFaithfulCancelRight (totalFunctor T) (sumBaseChangeOver square)

theorem sumBaseChange_comprehension (square : IsPullback top left right bottom)
    (A : DisplayedFamily P) :
    (totalFunctor T).map ((sumBaseChange square).hom.app A) =
      (sumBaseChangeOver square).hom.app A := by
  have : (totalFunctor T).Full := (equivalence T).fullyFaithfulFunctor.full
  have : (totalFunctor T).Faithful := (equivalence T).fullyFaithfulFunctor.faithful
  exact (totalFunctor T).map_preimage _

end Mettapedia.TypeTheory.DisplayedPresheafEvidenceBaseChange
