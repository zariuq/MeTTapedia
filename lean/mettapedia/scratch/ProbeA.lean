import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureBridge

namespace ProbeA

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

-- check names resolve
#check @rhoCIGSLT
#check @rhoProc
#check @RhoCollapsingApplyLeafBoundary
#check @CostStaticRegionNode.finiteBoundaryTable
#check @TypedCostRegionBoundaryTable.entries
#check @CostStaticPlanEntryEmbedding
#check @mem_costStaticCollectionTypingChoices_complete
#check @rho_costBaseParallelConstructor_params
#check @CostCollectionTypingChoice.bare
#check @CostStaticRegionNode.ofPlan

end ProbeA
