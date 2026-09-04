import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesProvenancedAlignment

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The existing positional restriction theorem applies directly to a reached
plan retained by the stop callback. -/
theorem reached_normalizedRestoration_replaysRootForest
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {payload rootAbstract : Pattern}
    (reached : CostStaticPlanReached source color targetFree payload
      rootAbstract)
    (admission : reached.plan.RawAdmission)
    {rootOccurrences : List CostRegionOccurrence}
    (rootTable : TypedCostRegionBoundaryTable source color targetFree
      rootOccurrences)
    (embedding : CostStaticPlanEntryEmbedding source color targetFree
      reached.plan.boundaryTable.entries rootTable.entries)
    (rootTrees : CostRegionBoundaryTrees source targetFree color rootTable) :
    let mappedAbstract := reached.thinning.thickenAmbientBVars 0
      (mapPattern (color.symbols source) reached.plan.abstractPattern)
    ((CostRegionBoundaryTrees.restrictAlongEntryEmbedding
        reached.plan.boundaryTable rootTable embedding rootTrees
      ).normalizeValues
        (normalizeStatic := kernel.normalize)).restoreSupportedSkeleton
          reached.plan.boundaryTable reached.sourceAvailable mappedAbstract =
      (rootTrees.normalizeValues
        (normalizeStatic := kernel.normalize)).restoreSupportedSkeleton
          rootTable reached.sourceAvailable mappedAbstract := by
  exact reached.plan.normalizeValues_restoreMappedAbstract_restrict_eq
    unambiguous admission.object rootTable embedding rootTrees

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
