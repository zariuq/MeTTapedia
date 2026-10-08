import Mettapedia.TypeTheory.DisplayedPresheafSliceSubstitution
import Mathlib.Data.Subtype

/-!
# Proof-retaining dependent transport along a natural program map

A dependent sum along a program map retains the source program, its evidence
and the equality of the emitted target program. It is left adjoint to native
substitution. Sequential transport reassociates the retained data naturally;
it does not choose a certificate from predicate support.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafEvidenceTransport

open CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSlice DisplayedPresheafSliceSubstitution

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q R : Cᵒᵖ ⥤ Type u}

def transport (f : P ⟶ Q) (A : DisplayedFamily P) : DisplayedFamily Q :=
  observationFibreFamily (totalProjection A ≫ f)

set_option backward.isDefEq.respectTransparency false in
/-- The native dependent sum includes every supplied certificate, with
its original source index. -/
def unit (f : P ⟶ Q) (A : DisplayedFamily P) : A ⟶ reindexDisplayed f (transport f A) where
  app point := TypeCat.ofHom (fun evidence => ⟨⟨point.2, evidence⟩, rfl⟩)
  naturality X Y arrow := by
    ext evidence
    apply Subtype.ext
    rcases X with ⟨X, x⟩
    rcases Y with ⟨Y, y⟩
    rcases arrow with ⟨arrow, same⟩
    change P.obj Y at y
    change P.map arrow x = y at same
    change (⟨y, A.map ⟨arrow, same⟩ evidence⟩ : TotalAt A Y) =
      totalMap A arrow ⟨x, evidence⟩
    exact (totalMap_of_base_arrow A ⟨arrow, same⟩ evidence).symm

theorem unit_injective (f : P ⟶ Q) (A : DisplayedFamily P) (point : P.Elements) :
    Function.Injective ((unit f A).app point) := by
  intro first second same
  exact (Sigma.mk.inj_iff.mp (congrArg Subtype.val same)).2.eq

/-- Native comprehension of the transported family retains exactly the
original source total, with the target projection equal to compilation. -/
def totalIso (f : P ⟶ Q) (A : DisplayedFamily P) :
    totalSpace (transport f A) ≅ totalSpace A :=
  observationTotalIso (totalProjection A ≫ f)

theorem totalIso_projection (f : P ⟶ Q) (A : DisplayedFamily P) :
    (totalIso f A).hom ≫ totalProjection A ≫ f = totalProjection (transport f A) :=
  observationTotalIso_projection (totalProjection A ≫ f)

def transportFunctor (f : P ⟶ Q) : DisplayedFamily P ⥤ DisplayedFamily Q :=
  totalFunctor P ⋙ Over.map f ⋙ fibreFunctor Q

theorem transportFunctor_obj (f : P ⟶ Q) (A : DisplayedFamily P) :
    (transportFunctor f).obj A = transport f A := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The transport is the genuine dependent sum over the program map. -/
noncomputable def adjunction (f : P ⟶ Q) : transportFunctor f ⊣ reindexFunctor f :=
  (((equivalence P).toAdjunction.comp (Over.mapPullbackAdj f)).comp
    (equivalence Q).symm.toAdjunction).ofNatIsoRight
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (substitutionIso f).symm (fibreFunctor P) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (reindexFunctor f) (unitIso P).symm ≪≫
        Functor.rightUnitor _)

def compositionEquiv (f : P ⟶ Q) (g : Q ⟶ R) (A : DisplayedFamily P)
    (point : R.Elements) : (transport g (transport f A)).obj point ≃
      (transport (f ≫ g) A).obj point where
  toFun receipt :=
    ⟨receipt.val.2.val, by
      change g.app point.1 (f.app point.1 receipt.val.2.val.1) = point.2
      have middle := receipt.val.2.property
      change f.app point.1 receipt.val.2.val.1 = receipt.val.1 at middle
      rw [middle]
      exact receipt.property⟩
  invFun receipt :=
    ⟨⟨f.app point.1 receipt.val.1, ⟨receipt.val, rfl⟩⟩, receipt.property⟩
  left_inv receipt := by
    apply Subtype.ext
    rcases receipt with ⟨⟨middle, ⟨original, follows⟩⟩, final⟩
    change f.app point.1 original.1 = middle at follows
    apply Sigma.ext follows
    apply (Subtype.heq_iff_coe_eq (fun candidate => by
      change f.app point.1 candidate.1 = f.app point.1 original.1 ↔
        f.app point.1 candidate.1 = middle
      rw [follows])).mpr
    rfl
  right_inv receipt := by
    apply Subtype.ext
    rfl

def compositionIso (f : P ⟶ Q) (g : Q ⟶ R) (A : DisplayedFamily P) :
    transport g (transport f A) ≅ transport (f ≫ g) A :=
  NatIso.ofComponents (fun point => (compositionEquiv f g A point).toIso)
    (by
      intro first second arrow
      ext receipt
      apply Subtype.ext
      rfl)

theorem composition_unit (f : P ⟶ Q) (g : Q ⟶ R) (A : DisplayedFamily P)
    (point : P.Elements) (evidence : A.obj point) :
    (compositionIso f g A).hom.app ((f ≫ g).mapElements.obj point)
      ((unit g (transport f A)).app (f.mapElements.obj point)
        ((unit f A).app point evidence)) =
      (unit (f ≫ g) A).app point evidence := rfl

end Mettapedia.TypeTheory.DisplayedPresheafEvidenceTransport
