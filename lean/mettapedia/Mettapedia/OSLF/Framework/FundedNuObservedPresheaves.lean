import Mettapedia.OSLF.Framework.FundedNuObservationEvidence
import Mettapedia.TypeTheory.DisplayedPresheafTransport

/-!
# Native families on the resource-indexed actual observation image

The actual instruction answer-and-spending images at different purses form
a presheaf. Its restriction is derived through the earned complete class
comparison, and maps the observation of each supplied state to that state's
smaller-purse observation. The finite class presheaf and this independently
defined image presheaf are naturally isomorphic.

Consequently every displayed family on the finite classes transports with
its whole resource-substitution action to the actual observed profiles.
This preserves supplied witnesses and future restrictions, without making
hidden state families or original infinite predicates observable.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.FundedNuObservedPresheaves

open _root_.CategoryTheory _root_.Opposite
open FundedNuObservationClasses FundedNuBudgetDiagram FundedNuObservationEvidence
open Mettapedia.TypeTheory.DisplayedPresheafTransport

def actualRestriction (smaller larger : Nat) (within : smaller ≤ larger)
    (observed : ActualProfile larger) : ActualProfile smaller :=
  imageEquivalence smaller (restriction smaller larger within ((imageEquivalence larger).symm observed))

theorem actualRestriction_state (smaller larger : Nat) (within : smaller ≤ larger)
    (state : Option Nat) :
    actualRestriction smaller larger within (actualView larger state) = actualView smaller state := by
  unfold actualRestriction
  rw [observed_class_readout, restriction_state]
  exact (actualView_eq_realize smaller state).symm

theorem actualRestriction_identity (budget : Nat) (observed : ActualProfile budget) :
    actualRestriction budget budget le_rfl observed = observed := by
  unfold actualRestriction
  rw [restriction_identity]
  exact (imageEquivalence budget).apply_symm_apply observed

theorem actualRestriction_composition (first middle last : Nat)
    (before : first ≤ middle) (after : middle ≤ last) (observed : ActualProfile last) :
    actualRestriction first middle before (actualRestriction middle last after observed) =
      actualRestriction first last (le_trans before after) observed := by
  unfold actualRestriction
  rw [Equiv.symm_apply_apply, restriction_composition]

def actualProfiles : Natᵒᵖ ⥤ Type where
  obj budget := ActualProfile budget.unop
  map change := TypeCat.ofHom (actualRestriction _ _ (leOfHom change.unop))
  map_id budget := by
    apply ConcreteCategory.hom_ext
    intro observed
    exact actualRestriction_identity budget.unop observed
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro observed
    exact (actualRestriction_composition _ _ _ (leOfHom second.unop) (leOfHom first.unop) observed).symm

def actualClassifications : (Functor.const Natᵒᵖ).obj (Option Nat) ⟶ actualProfiles where
  app budget := TypeCat.ofHom (actualView budget.unop)
  naturality first second change := by
    apply ConcreteCategory.hom_ext
    intro state
    exact (actualRestriction_state second.unop first.unop (leOfHom change.unop) state).symm

def profileIso : observationClasses ≅ actualProfiles :=
  NatIso.ofComponents (fun budget => (imageEquivalence budget.unop).toIso) (by
    intro first second change
    apply ConcreteCategory.hom_ext
    intro code
    change imageEquivalence second.unop (restriction _ _ (leOfHom change.unop) code) =
      imageEquivalence second.unop (restriction _ _ (leOfHom change.unop)
        ((imageEquivalence first.unop).symm (imageEquivalence first.unop code)))
    rw [Equiv.symm_apply_apply])

theorem state_diagrams_agree : classifications ≫ profileIso.hom = actualClassifications := by
  ext budget state
  exact (actualView_eq_realize budget.unop state).symm

universe u

/-- Whole native families transport, including their action on every
resource-substitution arrow, along the proved actual profile comparison. -/
def nativeFamilyEquivalence :
    DisplayedFamily.{0,0,0,u} observationClasses ≌ DisplayedFamily.{0,0,0,u} actualProfiles :=
  displayedFamilyEquivalence profileIso

def nativeFamilyRecovery (family : DisplayedFamily.{0,0,0,u} observationClasses) :
    family ≅ nativeFamilyEquivalence.inverse.obj (nativeFamilyEquivalence.functor.obj family) :=
  nativeFamilyEquivalence.unitIso.app family

end Mettapedia.OSLF.Framework.FundedNuObservedPresheaves
