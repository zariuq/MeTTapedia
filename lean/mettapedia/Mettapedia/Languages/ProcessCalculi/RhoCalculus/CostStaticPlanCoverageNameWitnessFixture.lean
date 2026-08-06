import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCellFixture
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageOccurrenceFixture

/-! # Skeleton-level changed-site witness for breadth coverage -/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample

/-- Localized zero-name cell before semantic closure. -/
noncomputable def rhoCoverageNameSiteWitness :
    CostChangedSiteWitness rhoCIGSLT rhoCutOrderFree rhoCutOrderRedex
      (.fvar "0") where
  cell := rhoCoverageZeroCell
  context := .hole
  leftLocal := by simp [rhoCoverageZeroCell_first_pattern, OneHoleContext.fill]
  rightLocal := by simp [rhoCoverageZeroCell_second_pattern, OneHoleContext.fill]

theorem rhoCoverageNameSite_declarationTie :
    rhoCoverageNameSiteWitness.cell.sourceDeclaration =
      rhoBreadthTypedOccurrence.sourceDeclaration := by
  rw [show rhoCoverageNameSiteWitness.cell = rhoCoverageZeroCell from rfl,
    rhoCoverageZeroCell_sourceDeclaration,
    rhoBreadthTypedOccurrence_sourceDeclaration]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary
