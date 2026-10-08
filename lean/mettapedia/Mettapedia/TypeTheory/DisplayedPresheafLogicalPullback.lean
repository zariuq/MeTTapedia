import Mettapedia.TypeTheory.DisplayedPresheafEvidenceUniversal
import Mathlib.CategoryTheory.Monoidal.Closed.Functor
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# Logical pullback inside one presheaf category

Substitution along a natural map is cartesian closed. Its Frobenius
comparison is an isomorphism: an external target witness and a retained
source receipt regroup into the receipt of their dependent pair. Both
directions keep the same source index and witness. This applies to maps
inside one presheaf category, independently of the future-arrow conditions
needed when changing the indexing category itself.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafLogicalPullback

open _root_.CategoryTheory CartesianMonoidalCategory MonoidalCategory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution DisplayedPresheafEvidenceTransport
open DisplayedPresheafEvidenceUniversal

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q : Cᵒᵖ ⥤ Type u}

noncomputable def frobenius (f : P ⟶ Q) (A : DisplayedFamily Q) :=
  frobeniusMorphism (reindexFunctor f) (receiptAdjunction f) A

instance substitution_preservesLimits (f : P ⟶ Q) :
    Limits.PreservesLimitsOfSize.{u, u} (reindexFunctor f) :=
  (receiptAdjunction f).rightAdjoint_preservesLimits

def regroup (f : P ⟶ Q) (A : DisplayedFamily Q) (B : DisplayedFamily P)
    (point : Q.Elements) :
    A.obj point × (transport f B).obj point →
      (transport f (reindexDisplayed f A ⊗ B)).obj point := by
  intro value
  rcases point with ⟨world, target⟩
  rcases value with ⟨external, ⟨⟨source, witness⟩, emitted⟩⟩
  change f.app world source = target at emitted
  change P.obj world at source
  subst target
  exact ⟨⟨source, ⟨external, witness⟩⟩, rfl⟩

theorem supplied_readout (f : P ⟶ Q) (A : DisplayedFamily Q)
    (B : DisplayedFamily P) (point : P.Elements)
    (external : (reindexDisplayed f A).obj point) (witness : B.obj point) :
    ((frobenius f A).natTrans.app B).app (f.mapElements.obj point)
        ((unit f (reindexDisplayed f A ⊗ B)).app point ⟨external, witness⟩) =
      ⟨external, (unit f B).app point witness⟩ := by
  cases point
  rfl

theorem regroup_after_comparison (f : P ⟶ Q) (A : DisplayedFamily Q)
    (B : DisplayedFamily P) (point : Q.Elements)
    (receipt : (transport f (reindexDisplayed f A ⊗ B)).obj point) :
    regroup f A B point (((frobenius f A).natTrans.app B).app point receipt) =
      receipt := by
  rcases point with ⟨world, target⟩
  rcases receipt with ⟨⟨source, ⟨external, witness⟩⟩, emitted⟩
  change f.app world source = target at emitted
  change P.obj world at source
  subst target
  rfl

theorem comparison_after_regroup (f : P ⟶ Q) (A : DisplayedFamily Q)
    (B : DisplayedFamily P) (point : Q.Elements)
    (value : A.obj point × (transport f B).obj point) :
    ((frobenius f A).natTrans.app B).app point (regroup f A B point value) = value := by
  rcases point with ⟨world, target⟩
  rcases value with ⟨external, ⟨⟨source, witness⟩, emitted⟩⟩
  change f.app world source = target at emitted
  change P.obj world at source
  subst target
  rfl

noncomputable def pointEquiv (f : P ⟶ Q) (A : DisplayedFamily Q)
    (B : DisplayedFamily P) (point : Q.Elements) :
    (transport f (reindexDisplayed f A ⊗ B)).obj point ≃
      A.obj point × (transport f B).obj point where
  toFun := ((frobenius f A).natTrans.app B).app point
  invFun := regroup f A B point
  left_inv := regroup_after_comparison f A B point
  right_inv := comparison_after_regroup f A B point

noncomputable instance frobenius_invertible (f : P ⟶ Q) (A : DisplayedFamily Q) :
    IsIso (frobenius f A).natTrans := by
  have (B : DisplayedFamily P) : IsIso ((frobenius f A).natTrans.app B) := by
    have (point : Q.Elements) : IsIso (((frobenius f A).natTrans.app B).app point) :=
      (pointEquiv f A B point).toIso.isIso_hom
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

noncomputable instance logical (f : P ⟶ Q) :
    MonoidalClosedFunctor (reindexFunctor f) where
  comparison_iso A := by
    have : IsIso (frobeniusMorphism (reindexFunctor f) (receiptAdjunction f) A).natTrans :=
      frobenius_invertible f A
    exact expComparison_iso_of_frobeniusMorphism_iso
      (reindexFunctor f) (receiptAdjunction f) A

end Mettapedia.TypeTheory.DisplayedPresheafLogicalPullback
