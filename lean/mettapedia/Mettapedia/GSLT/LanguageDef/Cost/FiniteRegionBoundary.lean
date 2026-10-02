import Mettapedia.GSLT.LanguageDef.Cost.RegionBoundaryEvidence
import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticScope

/-!
# Finite-profile specialization of retained boundary evidence

The actual finite generated language and reflection select the common
proof-relevant boundary carrier. Source type/support coordinates remain raw
key data; the region plan must establish their source-fibre coherence.
No second boundary identity or table traversal is introduced here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile
open Mettapedia.OSLF.MeTTaIL.Syntax

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

abbrev TypedCostRegionBoundary (profile : ContinuationDecorationProfile cut)
    (reflection : ReflectionExtension.AdmittedProfile theory.presentation.presentation.language)
    (color : CostStaticColor) (targetFree : WellSorted.FreeTypeContext) :=
  CostRegionBoundaryEvidence.TypedCostRegionBoundary profile.costWholeLanguage
    (profile.costWholeReflectionProfile reflection.1) color targetFree

namespace TypedCostRegionBoundary
export CostRegionBoundaryEvidence.TypedCostRegionBoundary (openPattern openPattern_pattern)
end TypedCostRegionBoundary

abbrev TypedCostRegionBoundaryTable (profile : ContinuationDecorationProfile cut)
    (reflection : ReflectionExtension.AdmittedProfile theory.presentation.presentation.language)
    (color : CostStaticColor) (targetFree : WellSorted.FreeTypeContext)
    (occurrences : List CostRegionOccurrence) :=
  CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable profile.costWholeLanguage
    (profile.costWholeReflectionProfile reflection.1) color targetFree occurrences

namespace TypedCostRegionBoundaryTable
export CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable
  (nil cons entries_length entries_content originalValues)

abbrev entries {profile : ContinuationDecorationProfile cut}
    {reflection : ReflectionExtension.AdmittedProfile theory.presentation.presentation.language}
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : profile.TypedCostRegionBoundaryTable reflection color targetFree occurrences) :=
  CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable.entries table

abbrev Values (profile : ContinuationDecorationProfile cut)
    (reflection : ReflectionExtension.AdmittedProfile theory.presentation.presentation.language)
    (color : CostStaticColor) (targetFree : WellSorted.FreeTypeContext)
    {occurrences : List CostRegionOccurrence}
    (table : profile.TypedCostRegionBoundaryTable reflection color targetFree occurrences) :=
  CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable.Values profile.costWholeLanguage
    (profile.costWholeReflectionProfile reflection.1) color targetFree table

namespace Values
export CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable.Values
  (nil cons Slot ValueAt get set get_set set_get get_set_other set_commute)
end Values
end TypedCostRegionBoundaryTable
end Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile
