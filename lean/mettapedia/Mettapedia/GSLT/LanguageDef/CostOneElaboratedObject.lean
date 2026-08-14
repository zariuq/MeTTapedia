import Mettapedia.GSLT.LanguageDef.CostElaboratedSection
import Mettapedia.GSLT.LanguageDef.CostEndofunctor
import Mettapedia.GSLT.LanguageDef.CostSemanticErasure

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

The compact normalizer is explicit object data.  `compactLaws` proves that
this selected executor constructs the checked continued output;
`semanticLaws` separately constructs the exact in-place section on retained
semantic Cost trees.  Agreement with an erase-and-recompile implementation is
optional comparison data rather than an object prerequisite. -/
structure CostOneDomainObject where
  source : OrderedCIGSLT
  normalizeOpen : CostOpenNormalizer source.toCIGSLT
  compactLaws : CIGSLT.CostOneObjectLawsFor source.toCIGSLT normalizeOpen
  semanticLaws : CostTypedUnaryNormalizationLaws source.toCIGSLT

namespace CostOneDomainObject

/-- The checked compact continued specification produced by one Cost layer. -/
def compactOutput (object : CostOneDomainObject) : OrderedCIGSLT :=
  ⟨object.source.toCIGSLT.costCIGSLTWith object.normalizeOpen
    object.compactLaws⟩

/-- Embed the original raw Cost executor into the normalizer-indexed object
boundary.  This constructor is intentionally named: it cannot be confused
with a hereditary object whose selected executor differs from the raw one. -/
def ofRawNormalizer (source : OrderedCIGSLT)
    (compactLaws : CIGSLT.CostReferenceOneObjectLaws source.toCIGSLT)
    (semanticLaws : CostTypedUnaryNormalizationLaws source.toCIGSLT) :
    CostOneDomainObject where
  source := source
  normalizeOpen := source.toCIGSLT.costNormalizeOpen
  compactLaws := compactLaws.toCostOneObjectLawsFor
  semanticLaws := semanticLaws

@[simp]
theorem compactOutput_theory (object : CostOneDomainObject) :
    object.compactOutput.toCIGSLT.theory =
      object.source.toCIGSLT.costIGSLT :=
  rfl

/-- The proof-relevant semantic output over the exact same generated authored
presentation as the compact continued object. -/
def elaboratedOutput (object : CostOneDomainObject) :
    ReflectiveElaboratedOpenTheory :=
  object.source.toCIGSLT.costSemanticElaboratedOpenTheory
    object.semanticLaws

@[simp]
theorem elaboratedOutput_theory (object : CostOneDomainObject) :
    object.elaboratedOutput.theory =
      object.compactOutput.toCIGSLT.theory :=
  rfl

/-- Optional agreement between the erase-and-recompile implementation and the
selected compact normalizer.

This theorem is deliberately not an object field: the object semantic carrier
normalizes retained frames in place, while this comparison concerns the
separate executable `CostRegionTree` carrier. -/
theorem operationalNormalize_erase_commutes (object : CostOneDomainObject)
    (operationalLaws : CostElaboratedNormalizationLaws
      object.source.toCIGSLT)
    (compactification : CostElaboratedCompactificationFor
      operationalLaws.sectionData object.normalizeOpen)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort object.source.toCIGSLT.costWholeLanguage}
    (term : CostElabTerm object.source.toCIGSLT targetFree targetBound
      targetSort) :
    CostOpenElaboration.erase (operationalLaws.sectionData.normalize term) =
      object.compactOutput.toCIGSLT.openCanonical.normalize
        (CostOpenElaboration.erase term) :=
  compactification.erases_normalize term

/-- On the optional operational carrier, compact execution may merge
observations while exact normalization retains distinct root fibres. -/
theorem sameCompact_but_distinctOperationalNormalForms
    (object : CostOneDomainObject)
    (operationalLaws : CostElaboratedNormalizationLaws
      object.source.toCIGSLT)
    (compactification : CostElaboratedCompactificationFor
      operationalLaws.sectionData object.normalizeOpen)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort object.source.toCIGSLT.costWholeLanguage}
    {left right : CostElabTerm object.source.toCIGSLT targetFree targetBound
      targetSort}
    (sameErasure : CostOpenElaboration.erase left =
      CostOpenElaboration.erase right)
    (different : left.decoration.rootIdentity ≠
      right.decoration.rootIdentity) :
    CostOpenElaboration.erase
        (operationalLaws.sectionData.normalize left) =
        CostOpenElaboration.erase
          (operationalLaws.sectionData.normalize right) ∧
      operationalLaws.sectionData.normalize left ≠
        operationalLaws.sectionData.normalize right :=
  compactification.sameCompact_but_distinctNormalForms sameErasure different

end CostOneDomainObject

end Mettapedia.GSLT.LanguageDef
