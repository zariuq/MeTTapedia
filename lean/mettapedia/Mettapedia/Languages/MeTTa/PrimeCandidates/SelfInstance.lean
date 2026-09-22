import Mettapedia.Languages.MeTTa.PrimeCandidates.StagedReflectiveInstances
import Mettapedia.Languages.MeTTa.PrimeCandidates.DataFibration

/-!
# candidate's level-raised self-instance

The actual validated candidate language presentation is already an intrinsic value
of the native Tarski universe.  This module places that exact value under the
existing non-idempotent `Data` constructor, then connects the resulting held
value to the existing common quotation former.

Inspection is deliberately weaker than source-level authority.  Returning
from the quoted observer stage to the source stage would require a reverse
stage morphism, which the well-founded stage category forbids.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SelfInstance

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.Experimental.StagedReflective
open Mettapedia.Languages.MeTTa.PrimeCandidates.StagedReflectiveInstances
open Mettapedia.Languages.MeTTa.PrimeCandidates.DataFibration

/-! ## The actual candidate language as held Data -/

/-- The Tarski base code whose inhabitants are validated five-field language
presentations. -/
def validatedLanguageDataType : DataType FamiliesCode :=
  .base .validatedLanguage

/-- One explicit Data layer over the validated-language carrier. -/
def heldValidatedLanguageDataType : DataType FamiliesCode :=
  .data validatedLanguageDataType

/-- candidate's actual validated presentation, held one Data level higher.  The
natural-number stamp records that single reflective step; it is not a second
copy of the presentation. -/
def queryFirstCandidateSelfData :
    Data Nat FamiliesCode.decode validatedLanguageDataType :=
  quoteAt 1 queryFirstCandidateLanguageUniverseValue

@[simp]
theorem queryFirstCandidateSelfData_stamp : queryFirstCandidateSelfData.1 = 1 :=
  rfl

@[simp]
theorem queryFirstCandidateSelfData_payload :
    eval queryFirstCandidateSelfData = queryFirstCandidateLanguageUniverseValue :=
  rfl

theorem queryFirstCandidateSelfData_is_actual_presentation :
    eval queryFirstCandidateSelfData =
      Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.queryFirstCandidatePresentation :=
  rfl

/-- The Data wrapper is a strict intensional level increase. -/
theorem queryFirstCandidateSelfData_strictly_raises :
    validatedLanguageDataType.level < heldValidatedLanguageDataType.level :=
  DataType.data_strictly_raises validatedLanguageDataType

/-- The self-instance cannot collapse to its unheld language code. -/
theorem queryFirstCandidateSelfData_level_does_not_collapse :
    heldValidatedLanguageDataType ≠ validatedLanguageDataType :=
  DataType.no_self_data validatedLanguageDataType

/-! ## Connection to the common native quotation former -/

/-- Observe a held validated-language value through the already existing
native quotation former. -/
def quoteHeldLanguage
    (value : Data Nat FamiliesCode.decode validatedLanguageDataType) :
    StagedReflectiveTm 0 0 :=
  nativeQuotedLanguage 0 (eval value)

/-- The Data self-instance and the previously selected quoted candidate language
are exactly the same native code, not merely extensionally related. -/
theorem quoteHeldLanguage_queryFirstCandidate :
    quoteHeldLanguage queryFirstCandidateSelfData = quotedQueryFirstCandidateLanguage :=
  rfl

/-- The common quotation decoder recovers the exact validated presentation
stored in the Data self-instance. -/
theorem queryFirstCandidateSelfData_roundtrip :
    (quoteHeldLanguage queryFirstCandidateSelfData).quotedLanguage? =
      some Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.queryFirstCandidatePresentation :=
  quotedQueryFirstCandidateLanguage_roundtrip

/-- The native quotation bridge also strictly raises reflective syntax depth. -/
theorem queryFirstCandidateSelfData_strict_reflective_increase :
    (StagedReflectiveTm.language (eval queryFirstCandidateSelfData) :
        StagedReflectiveTm 1 0).reflectiveDepth <
      (quoteHeldLanguage queryFirstCandidateSelfData).reflectiveDepth := by
  simpa [quoteHeldLanguage, quotedQueryFirstCandidateLanguage] using
    quotedQueryFirstCandidateLanguage_strictly_raises

/-- Negative decoder control: ordinary quoted Pure syntax is not silently
accepted as a language self-instance. -/
theorem quoted_nonlanguage_is_not_self_instance :
    quotedTwoSortUniverse.quotedLanguage? = none :=
  quotedTwoSortUniverse_not_quotedLanguage

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
  isQueryFirstCandidate : eval value =
    Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.queryFirstCandidatePresentation
  dataLevelStrict :
    validatedLanguageDataType.level < heldValidatedLanguageDataType.level
  quotationAgrees : quoteHeldLanguage value = quotedQueryFirstCandidateLanguage
  quotationRoundtrip : (quoteHeldLanguage value).quotedLanguage? =
    some Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.queryFirstCandidatePresentation
  noSourceValidationFromInspection :
    ¬ SelfInspectionAuthorizesSourceValidation

def queryFirstCandidateSelfInstance : Witness where
  value := queryFirstCandidateSelfData
  isQueryFirstCandidate := queryFirstCandidateSelfData_is_actual_presentation
  dataLevelStrict := queryFirstCandidateSelfData_strictly_raises
  quotationAgrees := quoteHeldLanguage_queryFirstCandidate
  quotationRoundtrip := queryFirstCandidateSelfData_roundtrip
  noSourceValidationFromInspection :=
    selfInspection_does_not_authorize_source_validation

#print axioms queryFirstCandidateSelfData_roundtrip
#print axioms queryFirstCandidateSelfData_strict_reflective_increase
#print axioms selfInspection_does_not_authorize_source_validation

end Mettapedia.Languages.MeTTa.PrimeCandidates.SelfInstance
