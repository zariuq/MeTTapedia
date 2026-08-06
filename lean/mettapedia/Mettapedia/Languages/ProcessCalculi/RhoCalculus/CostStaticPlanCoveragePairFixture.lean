import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageZeroFixture

/-! # Root context pair for the zero-name coverage fixture -/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample

/-- Paired reached views for the zero-name collapse.  The generic context-view
totality theorem is tested independently; this concrete fixture records its
two root views directly so elaboration does not replay the full plan induction. -/
noncomputable def rhoCoverageZeroPair :
    CostStaticPlanContextPair rhoCIGSLT .base rhoCutOrderFree
      rhoCoverageZeroCollapseEdge rhoCutOrderRedex (.fvar "0")
      rhoCoverageZeroRedexPlan.abstractPattern
      rhoCoverageZeroFvarPlan.abstractPattern
      rhoCoverageZeroRedexPlan.boundaryTable.entries
      rhoCoverageZeroFvarPlan.boundaryTable.entries where
  left :=
    { view := .reached
        { sourceBound := _, targetBound := _, thinning := _
          sourceAvailable := _, outer := _, sourceType := _
          plan := rhoCoverageZeroRedexPlan
          skeletonContext := .hole
          abstract_eq := rfl }
      entryEmbedding := CostStaticPlanEntryEmbedding.refl _ }
  right :=
    { view := .reached
        { sourceBound := _, targetBound := _, thinning := _
          sourceAvailable := _, outer := _, sourceType := _
          plan := rhoCoverageZeroFvarPlan
          skeletonContext := .hole
          abstract_eq := rfl }
      entryEmbedding := CostStaticPlanEntryEmbedding.refl _ }
  leftRoot_eq := rhoCoverageZeroRedexPlan.decoration_abstractPattern
  rightRoot_eq := rhoCoverageZeroFvarPlan.decoration_abstractPattern
  leftTable_eq := rfl
  rightTable_eq := rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary
