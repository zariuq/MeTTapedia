import Mettapedia.GSLT.LanguageDef.CostElaboratedSection
import Mettapedia.GSLT.LanguageDef.CostEndofunctor

/-!
# The proof-relevant object boundary for Cost₁

This file bundles the data carried by an object in the initial strict Cost₁
domain.  The compact output is a continued interactive GSLT with its ordered
canonical keys.  Above the same authored presentation sits an exact
proof-relevant Cost carrier and its checked split-epimorphic erasure.

Agreement of semantic normalization with one raw compact normalizer is an
optional stronger property, not part of Cost₁ closure: the rho Cost² overlap
proves that such factorization does not survive iteration in general.

No morphism category is declared here.  Decoration reindexing must be proved
before these object fibres are assembled into a total category.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- Data required to apply strict Cost₁ to one ordered continued
specification without identifying proof-relevant elaborations.

`compactLaws` constructs the checked raw continued output.  `semanticLaws`
prove the exact section for the fixed child-first normalizer on retained Cost
evidence. -/
structure CostOneDomainObject where
  source : OrderedCIGSLT
  compactLaws : CIGSLT.CostOneObjectLaws source.toCIGSLT
  semanticLaws : CostElaboratedNormalizationLaws source.toCIGSLT

namespace CostOneDomainObject

/-- Exact section data derived from the fixed proof-relevant Cost normalizer,
not chosen independently by the object. -/
def semanticSection (object : CostOneDomainObject) :
    CostElaboratedSectionData object.source.toCIGSLT :=
  object.semanticLaws.sectionData

/-- The checked compact continued specification produced by one Cost layer. -/
def compactOutput (object : CostOneDomainObject) : OrderedCIGSLT :=
  ⟨object.source.toCIGSLT.costCIGSLT object.compactLaws⟩

@[simp]
theorem compactOutput_theory (object : CostOneDomainObject) :
    object.compactOutput.toCIGSLT.theory =
      object.source.toCIGSLT.costIGSLT :=
  rfl

/-- The proof-relevant semantic output over the exact same generated authored
presentation as the compact continued object. -/
def elaboratedOutput (object : CostOneDomainObject) : ElaboratedOpenTheory where
  theory := object.compactOutput.toCIGSLT.theory
  carrier := object.source.toCIGSLT.costOpenElaborationCarrier
  semantics := object.semanticSection.semantics
  canonical := object.semanticSection.canonicalSection

/-- The semantic/compact normalization square commutes after erasure.

The upper computation normalizes retained declarations, colours, collection
choices, and boundary evidence.  The lower computation is the independently
defined checked compact executor installed as the output `ciGSLT` section. -/
theorem normalize_erase_commutes (object : CostOneDomainObject)
    (coherent : CompactCostNormalizationCoherent object.source.toCIGSLT)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort object.source.toCIGSLT.costWholeLanguage}
    (term : CostElabTerm object.source.toCIGSLT targetFree targetBound
      targetSort) :
    CostOpenElaboration.erase (object.semanticSection.normalize term) =
      object.compactOutput.toCIGSLT.openCanonical.normalize
        (CostOpenElaboration.erase term) :=
  (CostElaboratedCompactification.ofCompactCoherent object.semanticLaws
    coherent).erases_normalize term

/-- Compact execution may merge observations while the exact semantic output
retains distinct root fibres. -/
theorem sameCompact_but_distinctSemanticNormalForms
    (object : CostOneDomainObject)
    (coherent : CompactCostNormalizationCoherent object.source.toCIGSLT)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort object.source.toCIGSLT.costWholeLanguage}
    {left right : CostElabTerm object.source.toCIGSLT targetFree targetBound
      targetSort}
    (sameErasure : CostOpenElaboration.erase left =
      CostOpenElaboration.erase right)
    (different : left.decoration.rootIdentity ≠
      right.decoration.rootIdentity) :
    CostOpenElaboration.erase (object.semanticSection.normalize left) =
        CostOpenElaboration.erase (object.semanticSection.normalize right) ∧
      object.semanticSection.normalize left ≠
        object.semanticSection.normalize right :=
  (CostElaboratedCompactification.ofCompactCoherent object.semanticLaws
    coherent).sameCompact_but_distinctNormalForms sameErasure different

end CostOneDomainObject

end Mettapedia.GSLT.LanguageDef
