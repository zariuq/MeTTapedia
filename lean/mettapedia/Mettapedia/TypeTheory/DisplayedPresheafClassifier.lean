import Mettapedia.TypeTheory.DisplayedPresheafSliceSubstitution
import Mettapedia.GSLT.Topos.SubobjectClassifier

/-!
# The native truth object in a presheaf slice

Truth values of a displayed family are the ambient sieves at its world.
Natural maps into this family classify subfunctors of the actual total
space. Substitution along a presheaf map retains the truth family exactly
and takes inverse images of its classified predicates.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafClassifier

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution
open Mettapedia.GSLT.Topos

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q : Cᵒᵖ ⥤ Type u}

/-- The slice truth object is the ambient sieve object, varying with the
world of the base value. -/
def propositions (P : Cᵒᵖ ⥤ Type u) : DisplayedFamily P :=
  CategoryOfElements.π P ⋙ omegaFunctor

def truth (P : Cᵒᵖ ⥤ Type u) :
    (Functor.const P.Elements).obj PUnit ⟶ propositions P where
  app point := TypeCat.ofHom (fun _ => (⊤ : Sieve point.1.unop))
  naturality _ _ arrow := by
    ext value
    exact (sievePullback_top arrow.val.unop).symm

def totalCharacteristic {A : DisplayedFamily P}
    (predicate : A ⟶ propositions P) : totalSpace A ⟶ omegaFunctor where
  app world := TypeCat.ofHom (fun value => predicate.app ⟨world, value.1⟩ value.2)
  naturality first second arrow := by
    ext value
    exact predicate.naturality_apply
      (CategoryOfElements.homMk (F := P) ⟨first, value.1⟩
        ⟨second, P.map arrow value.1⟩ arrow rfl) value.2

def familyCharacteristic {A : DisplayedFamily P}
    (predicate : totalSpace A ⟶ omegaFunctor) : A ⟶ propositions P where
  app point := TypeCat.ofHom (fun evidence => predicate.app point.1 ⟨point.2, evidence⟩)
  naturality first second arrow := by
    ext evidence
    have natural := predicate.naturality_apply arrow.val ⟨first.2, evidence⟩
    change predicate.app second.1 (totalMap A arrow.val ⟨first.2, evidence⟩) = _ at natural
    rw [totalMap_of_base_arrow A arrow evidence] at natural
    exact natural

def characteristicEquiv (A : DisplayedFamily P) :
    (A ⟶ propositions P) ≃ (totalSpace A ⟶ omegaFunctor (C := C)) where
  toFun := totalCharacteristic
  invFun := familyCharacteristic
  left_inv _ := by ext point evidence; rfl
  right_inv _ := by ext world value; rfl

/-- Every subobject of the dependent total space has a unique native
characteristic map, retaining its contextual sieve rather than a Boolean. -/
noncomputable def predicateEquiv (A : DisplayedFamily P) :
    (A ⟶ propositions P) ≃ Subfunctor (totalSpace A) :=
  (characteristicEquiv A).trans (natTransEquivSubfunctor (totalSpace A))

theorem propositions_substitution (f : P ⟶ Q) :
    reindexDisplayed f (propositions Q) = propositions P := rfl

theorem truth_substitution (f : P ⟶ Q) :
    Functor.whiskerLeft f.mapElements (truth Q) = truth P := rfl

/-- Characteristic maps commute with the actual map of dependent totals
used for native context substitution. -/
theorem characteristic_substitution (f : P ⟶ Q) (A : DisplayedFamily Q)
    (predicate : A ⟶ propositions Q) :
    totalCharacteristic ((reindexFunctor f).map predicate) =
      totalReindexMap f A ≫ totalCharacteristic predicate := by
  ext world value
  rfl

/-- Substituting a truth-valued family map takes the inverse image of the
same classified predicate, with no coverage hypothesis on observers. -/
theorem predicate_substitution (f : P ⟶ Q) (A : DisplayedFamily Q)
    (predicate : A ⟶ propositions Q) :
    predicateEquiv (reindexDisplayed f A) ((reindexFunctor f).map predicate) =
      (predicateEquiv A predicate).preimage (totalReindexMap f A) := by
  ext world value
  rfl

end Mettapedia.TypeTheory.DisplayedPresheafClassifier
