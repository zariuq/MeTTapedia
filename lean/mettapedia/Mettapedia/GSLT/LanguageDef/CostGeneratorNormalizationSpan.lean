import Mettapedia.GSLT.LanguageDef.CostHereditaryTreeNormalization
import Mettapedia.GSLT.LanguageDef.EquationOccurrence

/-!
# Proof-relevant normalization spans for Cost generators

An authored equation may change the outer constructor of a compact term, so
an exact Cost proof cannot in general transport one region tree to another
while preserving its root.  A normalization span instead retains one
proof-relevant elaboration of each endpoint and exhibits a common typed normal
object reached by both hereditary evaluations.

The span is deliberately separate from compiler coherence.  Horizontal
normalization can therefore remain meaningful on an elaborated Cost carrier
even when erasure to one compact representative is not coherent at a later
Cost iteration.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

/-- A root-changing, proof-relevant join of two typed compact terms through
one common typed normal object.  The two elaborations retain all region,
declaration, colour, and boundary evidence; only their evaluated patterns are
identified at the apex. -/
structure CostNormalizationSpan
    (source : CIGSLT) (normalizeStatic : CostStaticRegionNormalizer source)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (left right : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort) where
  leftElaboration : CostOpenElaboration source left
  rightElaboration : CostOpenElaboration source right
  normal : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
    targetSort
  leftEvaluates :
    (leftElaboration.tree.normalize
      (normalizeStatic := normalizeStatic)).pattern = normal.1
  rightEvaluates :
    (rightElaboration.tree.normalize
      (normalizeStatic := normalizeStatic)).pattern = normal.1

namespace CostNormalizationSpan

/-- The two retained elaborations evaluate to exactly the same pattern. -/
theorem evaluations_eq
    {source : CIGSLT} {normalizeStatic : CostStaticRegionNormalizer source}
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort}
    (span : CostNormalizationSpan source normalizeStatic left right) :
    (span.leftElaboration.tree.normalize
        (normalizeStatic := normalizeStatic)).pattern =
      (span.rightElaboration.tree.normalize
        (normalizeStatic := normalizeStatic)).pattern :=
  span.leftEvaluates.trans span.rightEvaluates.symm

/-- Exact chooser coherence transports a semantic normalization span to the
two deterministic compiler elaborations.  This is the vertical composition
step; no authored-generator reasoning occurs here. -/
theorem compiledPatterns_eq
    {source : CIGSLT} {normalizeStatic : CostStaticRegionNormalizer source}
    (coherent : CostStaticRegionNormalizerCompactCoherent source
      normalizeStatic)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort}
    (span : CostNormalizationSpan source normalizeStatic left right) :
    ((CostOpenElaboration.compile source left).tree.normalize
        (normalizeStatic := normalizeStatic)).pattern =
      ((CostOpenElaboration.compile source right).tree.normalize
        (normalizeStatic := normalizeStatic)).pattern := by
  calc
    ((CostOpenElaboration.compile source left).tree.normalize
          (normalizeStatic := normalizeStatic)).pattern =
        (span.leftElaboration.tree.normalize
          (normalizeStatic := normalizeStatic)).pattern :=
      coherent left (CostOpenElaboration.compile source left)
        span.leftElaboration
    _ = (span.rightElaboration.tree.normalize
          (normalizeStatic := normalizeStatic)).pattern :=
      span.evaluations_eq
    _ = ((CostOpenElaboration.compile source right).tree.normalize
          (normalizeStatic := normalizeStatic)).pattern :=
      coherent right span.rightElaboration
        (CostOpenElaboration.compile source right)

end CostNormalizationSpan

/-- A normalization span tied to the exact proposition-valued generator that
it lifts.  The retained occurrence records equation versus reflection,
declaration identity, orientation, bindings, and redex context before
`erase` forgets them. -/
structure CostGeneratorNormalizationLift
    (source : CIGSLT) (normalizeStatic : CostStaticRegionNormalizer source)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort}
    (generator : openEquationGenerator source.costIGSLT targetFree targetBound
      targetSort left right) where
  occurrence : EquationSemantics.AuthoredGeneratorWitness
    defaultBasePremises source.costWholeLanguage left.1 right.1
  erasesTo : occurrence.erase = generator
  span : CostNormalizationSpan source normalizeStatic left right

/-- Every typed compact generator admits a proof-relevant root-aware
normalization span.  This is a semantic lifting obligation, not an equality
postulate for the deterministic executor. -/
def CostOpenGeneratorSpanLiftable
    (source : CIGSLT) (normalizeStatic : CostStaticRegionNormalizer source) :
    Prop :=
  ∀ {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort}
    (generator : openEquationGenerator source.costIGSLT targetFree targetBound
      targetSort left right),
    Nonempty (CostGeneratorNormalizationLift source normalizeStatic generator)

/-- A polymorphic checked compact normalizer over all exact open fibers. -/
abbrev CostOpenNormalizer (source : CIGSLT) :=
  {targetFree : FreeTypeContext} → {targetBound : List TypeExpr} →
    {targetSort : LangSort source.costWholeLanguage} →
    WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort →
      WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
        targetSort

/-- Exact generator invariance for a chosen checked Cost normalizer. -/
def CostOpenGeneratorInvariantFor (source : CIGSLT)
    (normalizeOpen : CostOpenNormalizer source) : Prop :=
  ∀ {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort},
    openEquationGenerator source.costIGSLT targetFree targetBound targetSort
        left right →
      @normalizeOpen targetFree targetBound targetSort left =
        @normalizeOpen targetFree targetBound targetSort right

/-- The checked executor erases the deterministic elaboration normalized by
the selected static kernel. -/
def CostOpenNormalizerAgreesWithStatic
    (source : CIGSLT) (normalizeStatic : CostStaticRegionNormalizer source)
    (normalizeOpen : CostOpenNormalizer source) : Prop :=
  ∀ {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort),
    (@normalizeOpen targetFree targetBound targetSort term).1 =
      ((CostOpenElaboration.compile source term).tree.normalize
        (normalizeStatic := normalizeStatic)).pattern

namespace CostOpenGeneratorInvariantFor

/-- Horizontal proof-relevant spans plus vertical compiler coherence imply
exact invariance of the checked compact executor.  Compact coherence appears
only in this erasure corollary, not in the span or its local normalization
proof. -/
theorem ofSpanLiftable
    {source : CIGSLT} {normalizeStatic : CostStaticRegionNormalizer source}
    {normalizeOpen : CostOpenNormalizer source}
    (liftable : CostOpenGeneratorSpanLiftable source normalizeStatic)
    (coherent : CostStaticRegionNormalizerCompactCoherent source
      normalizeStatic)
    (agrees : CostOpenNormalizerAgreesWithStatic source normalizeStatic
      normalizeOpen) :
    CostOpenGeneratorInvariantFor source normalizeOpen := by
  intro targetFree targetBound targetSort left right generator
  obtain ⟨lift⟩ := liftable generator
  apply Subtype.ext
  rw [agrees left, agrees right]
  exact lift.span.compiledPatterns_eq coherent

end CostOpenGeneratorInvariantFor

end Mettapedia.GSLT.LanguageDef
