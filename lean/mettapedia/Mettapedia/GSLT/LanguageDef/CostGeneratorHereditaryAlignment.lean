import Mettapedia.GSLT.LanguageDef.CostGeneratorNormalizationSpan
import Mettapedia.GSLT.LanguageDef.CostHereditaryAlignment

/-!
# Authored generators aligned by hereditary Cost trees

An exact generated occurrence and a root-aware alignment of two retained
Cost elaborations determine a normalization span.  This is the bridge from
the occurrence-local semantic-atom proof to the existing compact executor
invariance theorem.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

namespace EquationSemantics.AuthoredGeneratorWitness

/-- Restrict an exact contextual occurrence to its retained redex and
contractum while preserving equation/reflection identity and all local
evidence. -/
def atRedex
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern}
    (witness : EquationSemantics.AuthoredGeneratorWitness base language
      left right) :
    EquationSemantics.AuthoredGeneratorWitness base language witness.redex
      witness.contractum :=
  match witness with
  | .equation _ instanceWitness => .equation .hole instanceWitness
  | .reflective _ declaration representatives =>
      .reflective .hole declaration representatives

end EquationSemantics.AuthoredGeneratorWitness

namespace CostOpenElaboration

/-- Normalize one retained elaboration with an explicit static kernel and
repackage the result in the same checked open fibre. -/
def normalizeWithStaticErasure
    {source : CIGSLT} (normalizeStatic : CostStaticRegionNormalizer source)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {term : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort}
    (elaboration : CostOpenElaboration source term) :
    WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort := by
  let normalized := elaboration.tree.normalize
    (normalizeStatic := normalizeStatic)
  refine ⟨normalized.pattern, ?_⟩
  refine ⟨?_, normalized.canonicalBinderMetadata term.2.2.1,
    normalized.objectPattern term.2.2.2.1, ?_⟩
  · simpa using normalized.typed
  · intro presentation membership
    exact normalized.reflectiveScope presentation membership
      (Nat.le_refl targetBound.length) (term.2.2.2.2 presentation membership)

@[simp]
theorem normalizeWithStaticErasure_pattern
    {source : CIGSLT} (normalizeStatic : CostStaticRegionNormalizer source)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {term : WellSorted.OpenTerm source.costWholeLanguage targetFree targetBound
      targetSort}
    (elaboration : CostOpenElaboration source term) :
    (elaboration.normalizeWithStaticErasure normalizeStatic).1 =
      (elaboration.tree.normalize
        (normalizeStatic := normalizeStatic)).pattern :=
  rfl

end CostOpenElaboration

/-- An exact authored generator occurrence whose two retained elaborations
are related by the root-aware hereditary alignment.

The occurrence records authored equation or reflective identity and redex
position.  The tree relation separately records structural congruence and
the finite semantic-atom bridge at every root-changing step. -/
structure CostGeneratorTreeNormalizationAlignment
    (source : CIGSLT) (kernel : CostStaticNormalizationKernel source)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : WellSorted.OpenTerm source.costWholeLanguage targetFree
      targetBound targetSort}
    (generator : openEquationGenerator source.costIGSLT targetFree targetBound
      targetSort left right) where
  occurrence : EquationSemantics.AuthoredGeneratorWitness
    defaultBasePremises source.costWholeLanguage left.1 right.1
  erasesTo : occurrence.erase = generator
  leftElaboration : CostOpenElaboration source left
  rightElaboration : CostOpenElaboration source right
  treeAlignment : CostRegionTreeNormalizationAlignment source kernel
    targetFree leftElaboration.tree rightElaboration.tree

namespace CostGeneratorTreeNormalizationAlignment

/-- A proof-relevant tree alignment supplies the common typed normal object
and hence the established root-changing normalization-span interface. -/
def toNormalizationLift
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : WellSorted.OpenTerm source.costWholeLanguage targetFree
      targetBound targetSort}
    {generator : openEquationGenerator source.costIGSLT targetFree targetBound
      targetSort left right}
    (alignment : CostGeneratorTreeNormalizationAlignment source kernel
      generator) :
    CostGeneratorNormalizationLift source kernel.normalize generator where
  occurrence := alignment.occurrence
  erasesTo := alignment.erasesTo
  span :=
    { leftElaboration := alignment.leftElaboration
      rightElaboration := alignment.rightElaboration
      normal := alignment.leftElaboration.normalizeWithStaticErasure
        kernel.normalize
      leftEvaluates := by
        rfl
      rightEvaluates := by
        simpa only [CostOpenElaboration.normalizeWithStaticErasure_pattern]
          using alignment.treeAlignment.normalize_pattern_eq.symm }

end CostGeneratorTreeNormalizationAlignment

/-- Every typed generated edge admits retained endpoint elaborations joined
by a root-aware hereditary tree alignment. -/
def CostOpenGeneratorTreeAlignable
    (source : CIGSLT) (kernel : CostStaticNormalizationKernel source) : Prop :=
  ∀ {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : WellSorted.OpenTerm source.costWholeLanguage targetFree
      targetBound targetSort}
    (generator : openEquationGenerator source.costIGSLT targetFree targetBound
      targetSort left right),
    Nonempty (CostGeneratorTreeNormalizationAlignment source kernel generator)

namespace CostOpenGeneratorTreeAlignable

/-- Structural tree alignability implies the proof-relevant normalization
span obligation used by the compact executor theorem. -/
theorem spanLiftable
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (alignable : CostOpenGeneratorTreeAlignable source kernel) :
    CostOpenGeneratorSpanLiftable source kernel.normalize := by
  intro targetFree targetBound targetSort left right generator
  obtain ⟨alignment⟩ := alignable generator
  exact ⟨alignment.toNormalizationLift⟩

end CostOpenGeneratorTreeAlignable

namespace CostOpenGeneratorInvariantFor

/-- Root-aware occurrence alignment, chooser coherence, and executor
agreement compose to exact invariance of the checked compact normalizer. -/
theorem ofTreeAlignable
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {normalizeOpen : CostOpenNormalizer source}
    (alignable : CostOpenGeneratorTreeAlignable source kernel)
    (coherent : CostStaticRegionNormalizerCompactCoherent source
      kernel.normalize)
    (agrees : CostOpenNormalizerAgreesWithStatic source kernel.normalize
      normalizeOpen) :
    CostOpenGeneratorInvariantFor source normalizeOpen :=
  CostOpenGeneratorInvariantFor.ofSpanLiftable alignable.spanLiftable coherent
    agrees

end CostOpenGeneratorInvariantFor

end Mettapedia.GSLT.LanguageDef
