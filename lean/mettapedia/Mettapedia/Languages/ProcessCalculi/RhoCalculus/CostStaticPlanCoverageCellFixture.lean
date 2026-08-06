import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoveragePairFixture

/-! # Sibling cell for the zero-name coverage fixture -/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample

/-- The zero-name changed sibling as a candidate cell. -/
noncomputable def rhoCoverageZeroCell :
    CostStaticPlanSiblingPairCell rhoCIGSLT rhoCutOrderFree where
  color := .base
  first := rhoCoverageZeroRedexPlan.decoration
  second := rhoCoverageZeroFvarPlan.decoration
  sourceBoundaries := []
  targetBoundaries := []
  edge := rhoCoverageZeroCollapseEdge
  sourceDeclaration :=
    .reflective rhoReflectivePresentation.toReflectivePresentationDecl
  sourceDeclaration_eq := rfl
  leftPayload := rhoCutOrderRedex
  rightPayload := .fvar "0"
  leftRootAbstract := rhoCoverageZeroRedexPlan.abstractPattern
  rightRootAbstract := rhoCoverageZeroFvarPlan.abstractPattern
  leftEntries := rhoCoverageZeroRedexPlan.boundaryTable.entries
  rightEntries := rhoCoverageZeroFvarPlan.boundaryTable.entries
  pair := rhoCoverageZeroPair

@[simp] theorem rhoCoverageZeroCell_first_pattern :
    rhoCoverageZeroCell.first.pattern = rhoCutOrderRedex := rfl

@[simp] theorem rhoCoverageZeroCell_second_pattern :
    rhoCoverageZeroCell.second.pattern = (.fvar "0" : Pattern) := rfl

@[simp] theorem rhoCoverageZeroCell_sourceDeclaration :
    rhoCoverageZeroCell.sourceDeclaration =
      .reflective rhoReflectivePresentation.toReflectivePresentationDecl := rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary
