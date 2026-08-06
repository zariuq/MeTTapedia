import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageNameWitnessFixture

/-! # Boundary-content changed-site witness for breadth coverage -/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanPairCanary

/-- Localized continuation cell before restoration closure. -/
noncomputable def rhoCoverageContinuationSiteWitness :
    CostChangedSiteWitness rhoCIGSLT rhoCutOrderFree rhoBreadthLeftProcess
      rhoBreadthRightProcess :=
  rhoPairNameCell_continuationWitness

theorem rhoCoverageContinuationSite_declarationTie :
    rhoCoverageContinuationSiteWitness.cell.sourceDeclaration =
      rhoBreadthTypedOccurrence.sourceDeclaration := rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary
