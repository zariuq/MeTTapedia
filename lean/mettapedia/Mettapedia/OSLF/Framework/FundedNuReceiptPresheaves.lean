import Mettapedia.OSLF.Framework.FundedNuObservedPresheaves

/-!
# Coherent retained origins over actual funded observations

The fibre of the natural state observation retains the supplied state and
its classification evidence. Resource restriction preserves that origin,
even when a finite visible class becomes indistinguishable from the loop.
These are genuinely varying displayed families, transported through the
earned isomorphism of complete observation images.

There is no natural choice of one state per observation at every resource
stage. Retaining a supplied receipt and recovering it after family transport
does not manufacture a coherent origin from observations alone.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.FundedNuReceiptPresheaves

open _root_.CategoryTheory _root_.Opposite
open FundedNuObservationClasses FundedNuBudgetDiagram FundedNuObservationEvidence
open FundedNuObservedPresheaves
open Mettapedia.TypeTheory.DisplayedPresheafTransport

def classOrigins : DisplayedFamily.{0,0,0,0} observationClasses :=
  observationFibreFamily classifications

def actualOrigins : DisplayedFamily.{0,0,0,0} actualProfiles :=
  observationFibreFamily actualClassifications

def classReceipt (budget : Nat) (state : Option Nat) :
    classOrigins.obj ⟨op budget, classify budget state⟩ := ⟨state, rfl⟩

def actualReceipt (budget : Nat) (state : Option Nat) :
    actualOrigins.obj ⟨op budget, actualView budget state⟩ := ⟨state, rfl⟩

def classStateArrow (smaller larger : Nat) (within : smaller ≤ larger) (state : Option Nat) :
    observationClasses.elementsMk (op larger) (classify larger state) ⟶
      observationClasses.elementsMk (op smaller) (classify smaller state) :=
  ⟨(homOfLE within).op, restriction_state smaller larger within state⟩

def actualStateArrow (smaller larger : Nat) (within : smaller ≤ larger) (state : Option Nat) :
    actualProfiles.elementsMk (op larger) (actualView larger state) ⟶
      actualProfiles.elementsMk (op smaller) (actualView smaller state) :=
  ⟨(homOfLE within).op, actualRestriction_state smaller larger within state⟩

theorem class_receipt_restriction (smaller larger : Nat) (within : smaller ≤ larger)
    (state : Option Nat) :
    classOrigins.map (classStateArrow smaller larger within state) (classReceipt larger state) =
      classReceipt smaller state := by
  apply Subtype.ext
  rfl

theorem actual_receipt_restriction (smaller larger : Nat) (within : smaller ≤ larger)
    (state : Option Nat) :
    actualOrigins.map (actualStateArrow smaller larger within state) (actualReceipt larger state) =
      actualReceipt smaller state := by
  apply Subtype.ext
  rfl

def originFamilyRecovery :
    classOrigins ≅ nativeFamilyEquivalence.inverse.obj
      (nativeFamilyEquivalence.functor.obj classOrigins) := nativeFamilyRecovery classOrigins

theorem supplied_origin_recovered (value : observationClasses.Elements)
    (receipt : classOrigins.obj value) :
    originFamilyRecovery.inv.app value (originFamilyRecovery.hom.app value receipt) = receipt := by
  have equality := congrArg (fun arrow => arrow receipt)
    (originFamilyRecovery.hom_inv_id_app value)
  exact equality

theorem finite_class_origin_unique (budget : Nat) (length : Fin budget) (state : Option Nat)
    (classified : classify budget state = some length) : state = some length.val := by
  cases state with
  | none => simp [classify] at classified
  | some actualLength =>
      by_cases visible : actualLength < budget
      · rw [classify, dif_pos visible] at classified
        have same := congrArg Fin.val (Option.some.inj classified)
        exact congrArg some same
      · simp only [classify, dif_neg visible] at classified
        cases classified

/-- A section would choose the same origin after every loss of information.
The zero-resource class is reached by two independently visible finite
origins, which makes such a choice impossible. -/
theorem classifications_no_natural_section :
    ¬ ∃ decoder : observationClasses ⟶ (Functor.const Natᵒᵖ).obj (Option Nat),
      decoder ≫ classifications = 𝟙 observationClasses := by
  rintro ⟨decoder, sectionLaw⟩
  have zeroClass := congrArg (fun transformation =>
    transformation.app (op 1) (some (⟨0, by decide⟩ : Fin 1))) sectionLaw
  have oneClass := congrArg (fun transformation =>
    transformation.app (op 2) (some (⟨1, by decide⟩ : Fin 2))) sectionLaw
  have zeroOrigin := finite_class_origin_unique 1 ⟨0, by decide⟩
    (decoder.app (op 1) (some ⟨0, by decide⟩)) zeroClass
  have oneOrigin := finite_class_origin_unique 2 ⟨1, by decide⟩
    (decoder.app (op 2) (some ⟨1, by decide⟩)) oneClass
  have zeroNatural := congrArg (fun arrow => arrow (some (⟨0, by decide⟩ : Fin 1)))
    (decoder.naturality (homOfLE (Nat.zero_le 1)).op)
  have oneNatural := congrArg (fun arrow => arrow (some (⟨1, by decide⟩ : Fin 2)))
    (decoder.naturality (homOfLE (Nat.zero_le 2)).op)
  change decoder.app (op 0) none = decoder.app (op 1) (some ⟨0, by decide⟩) at zeroNatural
  change decoder.app (op 0) none = decoder.app (op 2) (some ⟨1, by decide⟩) at oneNatural
  rw [zeroOrigin] at zeroNatural
  rw [oneOrigin] at oneNatural
  have impossible := Option.some.inj (zeroNatural.symm.trans oneNatural)
  change (0 : Nat) = 1 at impossible
  omega

theorem actual_observations_no_natural_section :
    ¬ ∃ decoder : actualProfiles ⟶ (Functor.const Natᵒᵖ).obj (Option Nat),
      decoder ≫ actualClassifications = 𝟙 actualProfiles := by
  rintro ⟨decoder, sectionLaw⟩
  apply classifications_no_natural_section
  refine ⟨profileIso.hom ≫ decoder, ?_⟩
  have back : actualClassifications ≫ profileIso.inv = classifications := by
    rw [← state_diagrams_agree]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← back, Category.assoc, ← Category.assoc decoder, sectionLaw]
  simp only [Category.id_comp, Iso.hom_inv_id]

end Mettapedia.OSLF.Framework.FundedNuReceiptPresheaves
