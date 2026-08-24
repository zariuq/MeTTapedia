import Mettapedia.GSLT.LanguageDef.CostElaboratedSection
import Mettapedia.GSLT.LanguageDef.Cost.Construction
import Mettapedia.GSLT.LanguageDef.CostSemanticErasure

/-!
# The proof-relevant object boundary for cost layer

This file bundles the data carried by an object in the initial strict cost layer
domain.  The compact output is a continued interactive GSLT with its ordered
canonical keys.  Above the same authored presentation sits an exact
proof-relevant Cost carrier and its checked split-epimorphic erasure.

Agreement of semantic normalization with one raw compact normalizer is an
optional stronger property, not part of layer closure: the rho iteration
overlap proves that such factorization does not survive in general.

No morphism category is declared here.  Decoration reindexing must be proved
before these object fibres are assembled into a total category.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- Data required to apply strict cost layer to one ordered continued
specification without identifying proof-relevant elaborations.

The compact normalizer is explicit object data.  `compactLaws` proves that
this selected executor constructs the checked continued output;
`semanticLaws` separately constructs the exact in-place section on retained
semantic Cost trees.  Agreement with an erase-and-recompile implementation is
optional comparison data rather than an object prerequisite. -/
structure Cost.Layer where
  source : OrderedCIGSLT
  normalizeOpen : CostOpenNormalizer source.toCIGSLT
  compactLaws : Cost.CompactOpenNormalizer.Laws source.toCIGSLT normalizeOpen
  semanticLaws : Cost.SemanticSection.Laws source.toCIGSLT

/-- A cost layer whose source is fixed by its type.  This is the fibre of the
source projection; it is useful when a construction starts from a specified
continued authority rather than from the total space of all layers. -/
structure Cost.LayerOn (source : OrderedCIGSLT) where
  layer : Cost.Layer
  source_eq : layer.source = source

/-- A continued authority admits a cost layer when its source fibre is
inhabited.  The witness remains proof-relevant in `Cost.LayerOn`. -/
def Cost.HasLayer (source : OrderedCIGSLT) : Prop :=
  Nonempty (Cost.LayerOn source)

namespace Cost.Layer

/-- Every layer belongs to the fibre over its own source. -/
def onSource (layer : Cost.Layer) : Cost.LayerOn layer.source :=
  ⟨layer, rfl⟩

/-- The checked compact continued specification produced by one Cost layer. -/
def compactOutput (object : Cost.Layer) : OrderedCIGSLT :=
  ⟨object.source.toCIGSLT.costCIGSLTWith object.normalizeOpen
    object.compactLaws⟩

/-- Embed the original raw Cost executor into the normalizer-indexed object
boundary.  This constructor is intentionally named: it cannot be confused
with a hereditary object whose selected executor differs from the raw one. -/
def ofRawNormalizer (source : OrderedCIGSLT)
    (compactLaws : Cost.ReferenceCompactOpenNormalizer.Laws source.toCIGSLT)
    (semanticLaws : Cost.SemanticSection.Laws source.toCIGSLT) :
    Cost.Layer where
  source := source
  normalizeOpen := source.toCIGSLT.costNormalizeOpen
  compactLaws := compactLaws.toCompactOpenNormalizerLaws
  semanticLaws := semanticLaws

@[simp]
theorem compactOutput_theory (object : Cost.Layer) :
    object.compactOutput.toCIGSLT.theory =
      object.source.toCIGSLT.costIGSLT :=
  rfl

/-- The proof-relevant semantic output over the exact same generated authored
presentation as the compact continued object. -/
def elaboratedOutput (object : Cost.Layer) :
    ReflectiveElaboratedOpenTheory :=
  object.source.toCIGSLT.costSemanticElaboratedOpenTheory
    object.semanticLaws

@[simp]
theorem elaboratedOutput_theory (object : Cost.Layer) :
    object.elaboratedOutput.theory =
      object.compactOutput.toCIGSLT.theory :=
  rfl

/-- Optional agreement between the erase-and-recompile implementation and the
selected compact normalizer.

This theorem is deliberately not an object field: the object semantic carrier
normalizes retained frames in place, while this comparison concerns the
separate executable `CostRegionTree` carrier. -/
theorem operationalNormalize_erase_commutes (object : Cost.Layer)
    (operationalLaws : Cost.ElaboratedSection.Laws
      object.source.toCIGSLT)
    (compactification : Cost.SemanticSection.ErasureSemiconj
      operationalLaws.toElaboratedSection object.normalizeOpen)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort object.source.toCIGSLT.costWholeLanguage}
    (term : CostElabTerm object.source.toCIGSLT targetFree targetBound
      targetSort) :
    CostOpenElaboration.erase
        (operationalLaws.toElaboratedSection.normalize term) =
      object.compactOutput.toCIGSLT.openCanonical.normalize
        (CostOpenElaboration.erase term) :=
  compactification.erases_normalize term

/-- On the optional operational carrier, compact execution may merge
observations while exact normalization retains distinct root fibres. -/
theorem sameCompact_but_distinctOperationalNormalForms
    (object : Cost.Layer)
    (operationalLaws : Cost.ElaboratedSection.Laws
      object.source.toCIGSLT)
    (compactification : Cost.SemanticSection.ErasureSemiconj
      operationalLaws.toElaboratedSection object.normalizeOpen)
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
        (operationalLaws.toElaboratedSection.normalize left) =
        CostOpenElaboration.erase
          (operationalLaws.toElaboratedSection.normalize right) ∧
      operationalLaws.toElaboratedSection.normalize left ≠
        operationalLaws.toElaboratedSection.normalize right :=
  compactification.sameCompact_but_distinctNormalForms sameErasure different

end Cost.Layer

end Mettapedia.GSLT.LanguageDef
