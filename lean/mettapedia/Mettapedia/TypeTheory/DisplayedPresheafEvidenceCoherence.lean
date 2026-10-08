import Mettapedia.TypeTheory.DisplayedPresheafEvidenceTransport

/-!
# Coherence of proof-retaining native dependent sums

The unit comparison removes an identity receipt. The composition comparison
flattens two receipts while retaining the original evidence. These operations
are natural in evidence maps and agree under reassociation of three routes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafEvidenceCoherence

open CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafEvidenceTransport

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q R S : Cᵒᵖ ⥤ Type u}

def identityEquiv (A : DisplayedFamily P) (point : P.Elements) :
    (transport (𝟙 P) A).obj point ≃ A.obj point where
  toFun receipt := by
    rcases point with ⟨X, x⟩
    rcases receipt with ⟨⟨y, evidence⟩, same⟩
    change y = x at same
    subst y
    exact evidence
  invFun evidence := ⟨⟨point.2, evidence⟩, rfl⟩
  left_inv receipt := by
    rcases point with ⟨X, x⟩
    rcases receipt with ⟨⟨y, evidence⟩, same⟩
    change y = x at same
    subst y
    rfl
  right_inv _ := rfl

set_option backward.isDefEq.respectTransparency false in
def identityIso (A : DisplayedFamily P) : transport (𝟙 P) A ≅ A :=
  (NatIso.ofComponents (fun point => (identityEquiv A point).symm.toIso)
    (by
      intro first second arrow
      exact (unit (𝟙 P) A).naturality arrow)).symm

theorem identity_unit (A : DisplayedFamily P) (point : P.Elements)
    (evidence : A.obj point) :
      (identityIso A).hom.app point ((unit (𝟙 P) A).app point evidence) = evidence := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Removing an identity receipt is natural in maps of evidence. -/
def identityFunctorIso (P : Cᵒᵖ ⥤ Type u) :
    transportFunctor (𝟙 P) ≅ 𝟭 (DisplayedFamily P) :=
  (NatIso.ofComponents (fun A => (identityIso A).symm) (by
    intro A B operation
    ext point evidence
    apply Subtype.ext
    rfl)).symm

def compositionFunctorIso (f : P ⟶ Q) (g : Q ⟶ R) :
    transportFunctor f ⋙ transportFunctor g ≅ transportFunctor (f ≫ g) :=
  NatIso.ofComponents (fun A => compositionIso f g A) (by
    intro A B operation
    ext point receipt
    apply Subtype.ext
    rfl)

set_option backward.isDefEq.respectTransparency false in
theorem composition_associativity (f : P ⟶ Q) (g : Q ⟶ R) (h : R ⟶ S)
    (A : DisplayedFamily P) :
    (compositionIso g h (transport f A)).hom ≫ (compositionIso f (g ≫ h) A).hom =
      (transportFunctor h).map (compositionIso f g A).hom ≫
        (compositionIso (f ≫ g) h A).hom := by
  ext point receipt
  apply Subtype.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Transport through an identity source route agrees with its unit
comparison, including the original dependent certificate. -/
theorem composition_left_unit (f : P ⟶ Q) (A : DisplayedFamily P) :
    (compositionIso (𝟙 P) f A).hom = (transportFunctor f).map (identityIso A).hom := by
  ext point receipt
  rcases point with ⟨X, x⟩
  rcases receipt with ⟨⟨middle, ⟨⟨original, evidence⟩, same⟩⟩, follows⟩
  change original = middle at same
  subst original
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- An identity target route has the same comparison as deleting its
outer receipt. -/
theorem composition_right_unit (f : P ⟶ Q) (A : DisplayedFamily P) :
    (compositionIso f (𝟙 Q) A).hom = (identityIso (transport f A)).hom := by
  ext point receipt
  rcases point with ⟨X, x⟩
  rcases receipt with ⟨⟨middle, evidence⟩, same⟩
  change middle = x at same
  subst middle
  apply Subtype.ext
  rfl

end Mettapedia.TypeTheory.DisplayedPresheafEvidenceCoherence
