import Mettapedia.GSLT.Core.LooseRelationEquipment
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyReceiptNaturality

/-!
# Authored/native indexed-family receipts as equipment cells

The authored equation occurrences and native computation receipts of a
presented family are proof-relevant loose arrows between open terms.  Their
fibrewise equivalence therefore determines mutually inverse cells.  When the
presentation has earned `ReceiptNaturality`, renaming and simultaneous
substitution form commuting cell squares.

This is the exact two-dimensional interface needed by GSLT-IL: source
transport and native realization agree without quotienting receipt identity.
It is not a claim that the surrounding syntax already carries all bicategorical
or higher coherences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace AuthoredIndexedFamilyReceiptEquipment

open AuthoredDeclarationSignature
open AuthoredIndexedFamilyPresentation
open AuthoredIndexedFamilyReceiptNaturality
open Mettapedia.GSLT.LooseRelationEquipment
open Presentation

/-! ## Loose receipt relations and their comparison cells -/

/-- Authored equation occurrences as a proof-relevant loose arrow on open
Prime terms. -/
abbrev authoredReceipts (presented : PresentedCandidate) (n : Nat) :
    Loose (Tower.Tm n) (Tower.Tm n) :=
  EquationOccurrence (equationSchemas (elaborate presented.source))

/-- Native computation evidence as the corresponding proof-relevant loose
arrow. -/
abbrev nativeReceipts (presented : PresentedCandidate) (n : Nat) :
    Loose (Tower.Tm n) (Tower.Tm n) :=
  presented.candidate.computation.Evidence

/-- The forward authored-to-native receipt comparison. -/
def receiptCell (presented : PresentedCandidate) (n : Nat) :
    Cell (_root_.id : Tower.Tm n → Tower.Tm n) _root_.id
      (authoredReceipts presented n) (nativeReceipts presented n) where
  map occurrence := presented.receiptEquiv occurrence

/-- The inverse native-to-authored receipt comparison. -/
def receiptInverseCell (presented : PresentedCandidate) (n : Nat) :
    Cell (_root_.id : Tower.Tm n → Tower.Tm n) _root_.id
      (nativeReceipts presented n) (authoredReceipts presented n) where
  map receipt := presented.receiptEquiv.symm receipt

theorem receiptCell_vcomp_inverse
    (presented : PresentedCandidate) (n : Nat) :
    Cell.vcomp (receiptCell presented n) (receiptInverseCell presented n) =
      Cell.id (authoredReceipts presented n) := by
  apply Cell.ext
  intro left right occurrence
  exact presented.receiptEquiv.symm_apply_apply occurrence

theorem receiptInverseCell_vcomp_receiptCell
    (presented : PresentedCandidate) (n : Nat) :
    Cell.vcomp (receiptInverseCell presented n) (receiptCell presented n) =
      Cell.id (nativeReceipts presented n) := by
  apply Cell.ext
  intro left right receipt
  exact presented.receiptEquiv.apply_symm_apply receipt

/-! ## Context transport cells -/

/-- Ambient renaming acts on authored receipt evidence. -/
def authoredRenameCell (presented : PresentedCandidate)
    {n m : Nat} (renameMap : Ren n m) :
    Cell (Presentation.rename renameMap) (Presentation.rename renameMap)
      (authoredReceipts presented n) (authoredReceipts presented m) where
  map occurrence := occurrence.rename renameMap

/-- Ambient renaming acts independently on native receipt evidence. -/
def nativeRenameCell (presented : PresentedCandidate)
    {n m : Nat} (renameMap : Ren n m) :
    Cell (Presentation.rename renameMap) (Presentation.rename renameMap)
      (nativeReceipts presented n) (nativeReceipts presented m) where
  map receipt := presented.candidate.computation.rename renameMap receipt

/-- Simultaneous substitution acts on authored receipt evidence. -/
def authoredSubstitutionCell (presented : PresentedCandidate)
    {n m : Nat} (substitution : Sub Tower.Head n m) :
    Cell (Presentation.subst substitution) (Presentation.subst substitution)
      (authoredReceipts presented n) (authoredReceipts presented m) where
  map occurrence := occurrence.substitute substitution

/-- Simultaneous substitution acts independently on native receipt evidence. -/
def nativeSubstitutionCell (presented : PresentedCandidate)
    {n m : Nat} (substitution : Sub Tower.Head n m) :
    Cell (Presentation.subst substitution) (Presentation.subst substitution)
      (nativeReceipts presented n) (nativeReceipts presented m) where
  map receipt := presented.candidate.computation.substitute substitution receipt

/-! ## Naturality as cell equations -/

/-- Renaming before native realization equals native realization before
renaming as an equality of proof-relevant equipment cells. -/
theorem receiptCell_rename_naturality
    {presented : PresentedCandidate}
    (naturality : ReceiptNaturality presented)
    {n m : Nat} (renameMap : Ren n m) :
    Cell.vcomp (authoredRenameCell presented renameMap)
        (receiptCell presented m) =
      Cell.vcomp (receiptCell presented n)
        (nativeRenameCell presented renameMap) := by
  ext left right occurrence
  exact naturality.rename occurrence renameMap

/-- Simultaneous substitution before native realization equals native
realization before substitution as an equality of proof-relevant equipment
cells. -/
theorem receiptCell_substitution_naturality
    {presented : PresentedCandidate}
    (naturality : ReceiptNaturality presented)
    {n m : Nat} (substitution : Sub Tower.Head n m) :
    Cell.vcomp (authoredSubstitutionCell presented substitution)
        (receiptCell presented m) =
      Cell.vcomp (receiptCell presented n)
        (nativeSubstitutionCell presented substitution) := by
  ext left right occurrence
  exact naturality.substitute occurrence substitution

/-! ## Native-family instances and negative boundary -/

namespace Canaries

open AuthoredIndexedFamilyReceiptNaturality.NativeList
open AuthoredIndexedFamilyReceiptNaturality.NativeNatVec
open NativeIndexedFamilySource
open NativeNaturalVectorFamilySource

theorem nativeList_substitution_square
    {n m : Nat} (substitution : Sub Tower.Head n m) :
    Cell.vcomp
        (authoredSubstitutionCell nativeListPresentedCandidate substitution)
        (receiptCell nativeListPresentedCandidate m) =
      Cell.vcomp (receiptCell nativeListPresentedCandidate n)
        (nativeSubstitutionCell nativeListPresentedCandidate substitution) :=
  receiptCell_substitution_naturality nativeListReceiptNaturality substitution

theorem sharedNat_substitution_square
    {n m : Nat} (substitution : Sub Tower.Head n m) :
    Cell.vcomp (authoredSubstitutionCell natPresentedCandidate substitution)
        (receiptCell natPresentedCandidate m) =
      Cell.vcomp (receiptCell natPresentedCandidate n)
        (nativeSubstitutionCell natPresentedCandidate substitution) :=
  receiptCell_substitution_naturality natReceiptNaturality substitution

theorem sharedVec_substitution_square
    {n m : Nat} (substitution : Sub Tower.Head n m) :
    Cell.vcomp (authoredSubstitutionCell vecPresentedCandidate substitution)
        (receiptCell vecPresentedCandidate m) =
      Cell.vcomp (receiptCell vecPresentedCandidate n)
        (nativeSubstitutionCell vecPresentedCandidate substitution) :=
  receiptCell_substitution_naturality vecReceiptNaturality substitution

/-- Possessing the complete commuting equipment square still does not type a
raw ill-formed equation occurrence. -/
theorem equipment_cell_does_not_type_every_raw_occurrence :
    ∃ left right : Tower.Tm 0,
      Nonempty
          (EquationOccurrence NativeIndexedFamilySource.nativeSchemas
            left right) ∧
        ∀ type : Tower.Tm 0,
          IsEmpty
            (AuthoredIndexedFamilyTypedConversion.TypedOccurrence
              nativeListPresentedCandidate (.nil : Tower.Ctx 0)
              left right type) := by
  refine ⟨_, _, ⟨NativeIndexedFamilySource.untypedNilOccurrence⟩, ?_⟩
  intro type
  exact NativeIndexedFamilySource.untypedNil_has_no_typedOccurrence type

end Canaries

/-! ## Axiom audit -/

#print axioms receiptCell_vcomp_inverse
#print axioms receiptInverseCell_vcomp_receiptCell
#print axioms receiptCell_rename_naturality
#print axioms receiptCell_substitution_naturality
#print axioms Canaries.nativeList_substitution_square
#print axioms Canaries.sharedNat_substitution_square
#print axioms Canaries.sharedVec_substitution_square
#print axioms Canaries.equipment_cell_does_not_type_every_raw_occurrence

end AuthoredIndexedFamilyReceiptEquipment
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
