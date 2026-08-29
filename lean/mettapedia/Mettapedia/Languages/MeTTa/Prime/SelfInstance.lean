import Mettapedia.Languages.MeTTa.TypeTheory.StagedReflective.Presentation
import Mettapedia.Languages.MeTTa.Prime.DataFibration

/-!
# Prime's level-raised self-instance

The actual validated Prime language presentation is already an intrinsic value
of the native Tarski universe.  This module places that exact value under the
existing non-idempotent `Data` constructor, then connects the resulting held
value to the existing common quotation former.

Inspection is deliberately weaker than source-level authority.  Returning
from the quoted observer stage to the source stage would require a reverse
stage morphism, which the well-founded stage category forbids.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.SelfInstance

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.DataFibration

/-! ## The actual Prime language as held Data -/

/-- The Tarski base code whose inhabitants are validated five-field language
presentations. -/
def validatedLanguageDataType : DataType FamiliesCode :=
  .base .validatedLanguage

/-- One explicit Data layer over the validated-language carrier. -/
def heldValidatedLanguageDataType : DataType FamiliesCode :=
  .data validatedLanguageDataType

/-- Prime's actual validated presentation, held one Data level higher.  The
natural-number stamp records that single reflective step; it is not a second
copy of the presentation. -/
def currentPrimeSelfData :
    Data Nat FamiliesCode.decode validatedLanguageDataType :=
  quoteAt 1 currentPrimeLanguageUniverseValue

@[simp]
theorem currentPrimeSelfData_stamp : currentPrimeSelfData.1 = 1 :=
  rfl

@[simp]
theorem currentPrimeSelfData_payload :
    eval currentPrimeSelfData = currentPrimeLanguageUniverseValue :=
  rfl

theorem currentPrimeSelfData_is_actual_presentation :
    eval currentPrimeSelfData =
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation :=
  rfl

/-- The Data wrapper is a strict intensional level increase. -/
theorem currentPrimeSelfData_strictly_raises :
    validatedLanguageDataType.level < heldValidatedLanguageDataType.level :=
  DataType.data_strictly_raises validatedLanguageDataType

/-- The self-instance cannot collapse to its unheld language code. -/
theorem currentPrimeSelfData_level_does_not_collapse :
    heldValidatedLanguageDataType ≠ validatedLanguageDataType :=
  DataType.no_self_data validatedLanguageDataType

/-! ## Connection to the common native quotation former -/

/-- Observe a held validated-language value through the already existing
native quotation former. -/
def quoteHeldLanguage
    (value : Data Nat FamiliesCode.decode validatedLanguageDataType) :
    StagedReflectiveTm 0 0 :=
  nativeQuotedLanguage 0 (eval value)

/-- The Data self-instance and the previously selected quoted Prime language
are exactly the same native code, not merely extensionally related. -/
theorem quoteHeldLanguage_currentPrime :
    quoteHeldLanguage currentPrimeSelfData = quotedCurrentPrimeLanguage :=
  rfl

/-- The common quotation decoder recovers the exact validated presentation
stored in the Data self-instance. -/
theorem currentPrimeSelfData_roundtrip :
    (quoteHeldLanguage currentPrimeSelfData).quotedLanguage? =
      some Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation :=
  quotedCurrentPrimeLanguage_roundtrip

/-- The native quotation bridge also strictly raises reflective syntax depth. -/
theorem currentPrimeSelfData_strict_reflective_increase :
    (StagedReflectiveTm.language (eval currentPrimeSelfData) :
        StagedReflectiveTm 1 0).reflectiveDepth <
      (quoteHeldLanguage currentPrimeSelfData).reflectiveDepth := by
  simpa [quoteHeldLanguage, quotedCurrentPrimeLanguage] using
    quotedCurrentPrimeLanguage_strictly_raises

/-- Negative decoder control: ordinary quoted Pure syntax is not silently
accepted as a language self-instance. -/
theorem quoted_nonlanguage_is_not_self_instance :
    quotedPureUniverse.quotedLanguage? = none :=
  quotedPureUniverse_not_quotedLanguage

/-! ## Inspection is not same-source validation authority -/

/-- To turn code inspected at stage zero back into authority at its stage-one
source would require a reverse adjacent-stage morphism. -/
def SelfInspectionAuthorizesSourceValidation : Prop :=
  Nonempty (StageHom 0 1)

/-- The self-instance is inspectable, but inspection cannot manufacture a
same-source validation route. -/
theorem selfInspection_does_not_authorize_source_validation :
    ¬ SelfInspectionAuthorizesSourceValidation := by
  rintro ⟨reverse⟩
  exact (no_reverse_adjacent_stage 0).false reverse

/-- The completed witness packages the exact held value and both independent
strictness boundaries: Data level and native reflective depth. -/
structure Witness where
  value : Data Nat FamiliesCode.decode validatedLanguageDataType
  isCurrentPrime : eval value =
    Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation
  dataLevelStrict :
    validatedLanguageDataType.level < heldValidatedLanguageDataType.level
  quotationAgrees : quoteHeldLanguage value = quotedCurrentPrimeLanguage
  quotationRoundtrip : (quoteHeldLanguage value).quotedLanguage? =
    some Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation
  noSourceValidationFromInspection :
    ¬ SelfInspectionAuthorizesSourceValidation

def currentPrimeSelfInstance : Witness where
  value := currentPrimeSelfData
  isCurrentPrime := currentPrimeSelfData_is_actual_presentation
  dataLevelStrict := currentPrimeSelfData_strictly_raises
  quotationAgrees := quoteHeldLanguage_currentPrime
  quotationRoundtrip := currentPrimeSelfData_roundtrip
  noSourceValidationFromInspection :=
    selfInspection_does_not_authorize_source_validation

#print axioms currentPrimeSelfData_roundtrip
#print axioms currentPrimeSelfData_strict_reflective_increase
#print axioms selfInspection_does_not_authorize_source_validation

end Mettapedia.Languages.MeTTa.Prime.SelfInstance
