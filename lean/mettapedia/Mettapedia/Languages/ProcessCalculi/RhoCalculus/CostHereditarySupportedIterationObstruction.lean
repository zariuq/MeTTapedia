import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryObject
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationObstruction

/-!
# The exact cost-layer iteration boundary for rho's supported hereditary executor

The first rho Cost object selects the finite-support hereditary executor.
This module connects that exact executor to the normalizer-parameterized
second-layer obstruction.  The bridge is an explicit closed-fibre agreement
proof; no equality between arbitrary ambient-context executions is assumed.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationObstruction

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace RhoCostLayerConfiguration

/-- The finite-support hereditary executor together with its exact object
laws, as one point of the normalizer-indexed first Cost family. -/
def hereditarySupported
    (laws : Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported) : RhoCostLayerConfiguration where
  normalizeOpen := rhoCostNormalizeOpenHereditarySupported
  laws := laws

@[simp]
theorem hereditarySupported_normalizeOpen
    (laws : Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree targetBound targetSort) :
    (hereditarySupported laws).normalizeOpen term =
      rhoCostNormalizeOpenHereditarySupported term :=
  rfl

@[simp]
theorem hereditarySupported_source
    (laws : Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported) :
    (hereditarySupported laws).source =
      rhoCIGSLT.costCIGSLTWith rhoCostNormalizeOpenHereditarySupported laws :=
  rfl

end RhoCostLayerConfiguration

/-- Restricting a closed term to its finite free-name support leaves the
empty free context unchanged.  Consequently the supported and raw
hereditary executors have exactly the same raw normal form on closed fibres. -/
theorem rhoCostNormalizeOpenHereditarySupported_eq_hereditary_on_closed
    {bound : List TypeExpr}
    {sort : LangSort rhoCIGSLT.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      WellSorted.FreeTypeContext.empty bound sort) :
    (rhoCostNormalizeOpenHereditarySupported term).1 =
      (rhoCostNormalizeOpenHereditary term).1 := by
  let restricted := term.restrictFreeContext
  have contextEquality :
      WellSorted.FreeTypeContext.empty.restrictTo term.1.freeFvarNames =
        WellSorted.FreeTypeContext.empty := by
    funext name
    simp [WellSorted.FreeTypeContext.restrictTo,
      WellSorted.FreeTypeContext.empty]
  have termEquality :
      restricted.reindex contextEquality rfl rfl = term := by
    apply Subtype.ext
    exact (ReflectiveWellSorted.OpenTerm.reindex_pattern
      contextEquality rfl rfl restricted).trans
        (ReflectiveWellSorted.OpenTerm.restrictFreeContext_pattern term)
  rw [rhoCostNormalizeOpenHereditarySupported_pattern]
  calc
    (rhoCostNormalizeOpenHereditary restricted).1 =
        (rhoCostNormalizeOpenHereditary
          (restricted.reindex contextEquality rfl rfl)).1 :=
      (CostOpenNormalizer.reindexFree_pattern
        rhoCostNormalizeOpenHereditary contextEquality restricted).symm
    _ = (rhoCostNormalizeOpenHereditary term).1 :=
      congrArg (fun closed => (rhoCostNormalizeOpenHereditary closed).1)
        termEquality

/-- The finite-support hereditary executor satisfies the exact local
representative premise used by the parameterized cost-layer iteration obstruction. -/
theorem hereditarySupported_emptyParallelSourceRepresentative
    (laws : Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported) :
    RhoEmptyParallelSourceRepresentative
      (RhoCostLayerConfiguration.hereditarySupported laws) := by
  apply emptyParallelSourceRepresentative_of_baseEmptyRepresentative
  exact (rhoCostNormalizeOpenHereditarySupported_eq_hereditary_on_closed
    rhoBaseEmptyRepresentative).trans
      rhoCostNormalizeOpenHereditary_baseEmptyRepresentative

/-- Exact compact coherence is not closed by a second Cost application to
rho's actual finite-support hereditary first-layer executor. -/
theorem rhoHereditarySupportedCostLayer_not_compactCostNormalizationCoherent
    (laws : Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported) :
    ¬ CompactCostNormalizationCoherent
      (rhoCIGSLT.costCIGSLTWith rhoCostNormalizeOpenHereditarySupported
        laws) := by
  exact rhoCostLayerFor_not_compactCostNormalizationCoherent
    (RhoCostLayerConfiguration.hereditarySupported laws)
    (hereditarySupported_emptyParallelSourceRepresentative laws)

/-- The same obstruction stated at the exact compact output of rho's actual
normalizer-indexed cost layer object.  The hypotheses are precisely the two
remaining semantic closure witnesses used to construct that object. -/
theorem rhoHereditaryCostLayer_not_compactCostNormalizationCoherent_of
    (alignable : CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel)
    (preservesReflectiveSupport : RhoHereditaryReflectiveSupportPreserving) :
    ¬ CompactCostNormalizationCoherent
      (rhoHereditaryCostLayer_of alignable preservesReflectiveSupport
        ).compactOutput.toCIGSLT := by
  exact rhoHereditarySupportedCostLayer_not_compactCostNormalizationCoherent
    (rhoHereditaryCompactOpenNormalizerLaws_of alignable preservesReflectiveSupport)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationObstruction
