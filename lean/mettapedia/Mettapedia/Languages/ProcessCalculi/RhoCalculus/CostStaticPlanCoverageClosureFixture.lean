import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageWitnessFixture
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRestorationClosureCanary

/-! # Semantic closures for the breadth coverage fixture -/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalCanary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary

/-- Site 1 closes by the retained semantic-atom alignment. -/
noncomputable def rhoCoverageNameSiteClosure :
    CostChangedSiteClosure (available := []) (outer := [])
      (leftArgument := rhoCutOrderRedex) (rightArgument := .fvar "0")
      (expected := .base (costBaseSortName "Name"))
      rhoCIGSLT rhoHereditaryNormalizationKernel
      rhoCutOrderFree rhoBreadthTypedOccurrence.sourceDeclaration
      rhoCutOrderBaseRedexTree rhoCutOrderZeroStructuralTree :=
  CostChangedSiteClosure.mk
    (source := rhoCIGSLT) (kernel := rhoHereditaryNormalizationKernel)
    (targetFree := rhoCutOrderFree)
    (occurrenceDeclaration := rhoBreadthTypedOccurrence.sourceDeclaration)
    (available := []) (outer := [])
    (leftArgument := rhoCutOrderRedex) (rightArgument := .fvar "0")
    (expected := .base (costBaseSortName "Name"))
    (leftTree := rhoCutOrderBaseRedexTree)
    (rightTree := rhoCutOrderZeroStructuralTree)
    rhoCoverageNameSiteWitness rhoCoverageNameSite_declarationTie
    rhoCutOrderBaseSelectedTreeNormalizationAlignment

/-- Site 2 closes at the restoration apex, not at its respelled skeleton. -/
noncomputable def rhoCoverageContinuationSiteClosure :
    CostChangedSiteClosure (available := []) (outer := [])
      (leftArgument := rhoBreadthLeftProcess)
      (rightArgument := rhoBreadthRightProcess)
      (expected := .base costWrappedSortName)
      rhoCIGSLT rhoHereditaryNormalizationKernel
      rhoCutOrderFree rhoBreadthTypedOccurrence.sourceDeclaration
      rhoBreadthLeftProcessTree rhoBreadthRightProcessTree :=
  CostChangedSiteClosure.mk
    (source := rhoCIGSLT) (kernel := rhoHereditaryNormalizationKernel)
    (targetFree := rhoCutOrderFree)
    (occurrenceDeclaration := rhoBreadthTypedOccurrence.sourceDeclaration)
    (available := []) (outer := [])
    (leftArgument := rhoBreadthLeftProcess)
    (rightArgument := rhoBreadthRightProcess)
    (expected := .base costWrappedSortName)
    (leftTree := rhoBreadthLeftProcessTree)
    (rightTree := rhoBreadthRightProcessTree)
    rhoCoverageContinuationSiteWitness
    rhoCoverageContinuationSite_declarationTie
    rhoBreadthProcessRootBridge_viaRestoredFvarAlignment.toTreeAlignment

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary
