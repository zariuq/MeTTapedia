import Mettapedia.OSLF.Framework.WMCalculusEvidenceConversion
import Mettapedia.OSLF.Framework.WMCalculusSortedEncoding

/-!
# Native sorting of generated WM evidence conversion

The generated evidence conversion is complete for equality in all lawful WM
readings, but its terms still carry named State and Query atoms. This module
shows that every generator preserves the atom-sorting judgment in both
directions and hence preserves admission to the native open-pattern carrier.
The result concerns generated WM conversion, not arbitrary raw authored
equation instances.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusEvidenceConversionSorted

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.WMCalculusEvidenceConversion
open Mettapedia.OSLF.Framework.WMCalculusSortedEncoding
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Every generator of the complete evidence conversion preserves the
sorting of State and Query atoms, forwards and backwards. -/
theorem evidenceConversion_atomsTyped_iff (free : FreeTypeContext)
    {first second : WMTerm .evidence}
    (conversion : EvidenceConversion first second) :
    AtomsTyped free first ↔ AtomsTyped free second := by
  induction conversion with
  | refl => exact Iff.rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH
  | combine _ _ firstIH secondIH =>
      exact and_congr firstIH secondIH
  | comm => exact and_comm
  | assoc => exact and_assoc
  | zero => simp [AtomsTyped]
  | extract => simp [AtomsTyped, and_assoc, and_left_comm, and_comm]

/-- Complete generated evidence conversion stays within any exact native
open-pattern fiber in which its first endpoint is admitted. -/
theorem evidenceConversion_openPatternWellSorted_iff_bound
    (lang : LanguageDef) (declared : lang.terms = coreTerms)
    (free : FreeTypeContext) (bound : List TypeExpr)
    {first second : WMTerm .evidence}
    (conversion : EvidenceConversion first second) :
    OpenPatternWellSorted lang free bound (sortType .evidence)
      (encodeWM first) ↔
    OpenPatternWellSorted lang free bound (sortType .evidence)
      (encodeWM second) :=
  (encodeWM_openPatternWellSorted_iff_bound lang declared free bound first).trans
    ((evidenceConversion_atomsTyped_iff free conversion).trans
      (encodeWM_openPatternWellSorted_iff_bound lang declared free bound second).symm)

/-- Equality in every lawful WM reading transports native admission, once
one endpoint is admitted. The semantic hypothesis supplies conversion via the
existing syntactic quotient model; it does not define typing. -/
theorem allReadingsAgree_preserves_native_open
    (lang : LanguageDef) (declared : lang.terms = coreTerms)
    (free : FreeTypeContext) (bound : List TypeExpr)
    (first second : WMTerm .evidence)
    (agree : ∀ (State Query V : Type) (reading : WMReading State Query V),
      reading.CoreLaws → reading.denote first = reading.denote second)
    (admitted : OpenPatternWellSorted lang free bound (sortType .evidence)
      (encodeWM first)) :
    OpenPatternWellSorted lang free bound (sortType .evidence)
      (encodeWM second) :=
  (evidenceConversion_openPatternWellSorted_iff_bound lang declared free bound
    ((conversion_iff_allReadings first second).2 agree)).1 admitted

/-- Reflexive semantic agreement does not manufacture a typing context:
using one name at both State and Query sorts fails native admission. -/
theorem reflexive_agreement_does_not_admit_same_named_extract :
    let term : WMTerm .evidence :=
      .extract (.state "x") (.query "x")
    (∀ (State Query V : Type) (reading : WMReading State Query V),
      reading.CoreLaws → reading.denote term = reading.denote term) ∧
    ¬ OpenPatternWellSorted wmCoreLanguageDef FreeTypeContext.empty []
      (sortType .evidence) (encodeWM term) := by
  dsimp
  constructor
  · intro State Query V reading laws
    rfl
  · intro admitted
    exact extract_same_atom_not_sorted FreeTypeContext.empty "x" admitted.1

#print axioms evidenceConversion_atomsTyped_iff
#print axioms evidenceConversion_openPatternWellSorted_iff_bound
#print axioms allReadingsAgree_preserves_native_open
#print axioms reflexive_agreement_does_not_admit_same_named_extract

end Mettapedia.OSLF.Framework.WMCalculusEvidenceConversionSorted
