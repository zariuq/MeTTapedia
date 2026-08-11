import Mettapedia.GSLT.LanguageDef.CostHereditaryFrameNormalization

/-!
# Hereditary normalization of complete Cost region trees

The region-tree traversal is structural.  Its sole semantic parameter is a
typed normalizer for one static frame after all boundary children have been
normalized.  This module states the two local laws needed to lift such a
normalizer through a complete alternating tree and proves the resulting unary
contextual-equivalence theorem.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Framework.ConstructorCategory
open WellSorted

/-- Local laws sufficient to lift one static-frame normalizer through a full
proof-relevant Cost region tree.

The first law says that a frame normalizes relative to its current finite
boundary values.  The second transports already-proved child equivalences
through any surrounding binder weakening. -/
structure CostStaticRegionNormalizerLaws
    (source : CIGSLT) (normalizeStatic : CostStaticRegionNormalizer source) :
    Prop where
  ambientRenamingStable :
    SupportedEquationAmbientRenamingStable
      (profile := source.costWholeReflectionProfile)
      source.costWholeLanguage
  normalizesCurrentFrame : ∀
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable),
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage (normalizeStatic node values).1
      (values.restoreSupportedSkeleton node.boundaryTable node.targetBound
        node.mappedThickenedSkeleton.1)

namespace CostStaticRegionNormalizerLaws

/-- A local frame law plus pointwise equivalence of its current boundary
values yields equivalence to the exact compact term indexed by the node. -/
theorem normalizesOriginal
    {source : CIGSLT} {normalizeStatic : CostStaticRegionNormalizer source}
    (laws : CostStaticRegionNormalizerLaws source normalizeStatic)
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable)
    (valuesEquivalent :
      (values.supportedOpenAssignment node.boundaryTable).Equivalent
        ((TypedCostRegionBoundaryTable.Values.original node.boundaryTable
          ).supportedOpenAssignment node.boundaryTable)) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage (normalizeStatic node values).1 node.term.1 := by
  let valuesAssignment := values.supportedOpenAssignment node.boundaryTable
  let originalAssignment :=
    (TypedCostRegionBoundaryTable.Values.original node.boundaryTable
      ).supportedOpenAssignment node.boundaryTable
  have assignmentStep :=
    node.mappedThickenedSkeleton.2.1.equationEquiv_substitute_pointwise
      valuesAssignment originalAssignment valuesEquivalent
  have assignmentStep' :
      ReflectiveEquationSemantics.ReflectiveEquationEquiv
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage
      (values.restoreSupportedSkeleton node.boundaryTable node.targetBound
        node.mappedThickenedSkeleton.1)
      ((TypedCostRegionBoundaryTable.Values.original node.boundaryTable
        ).restoreSupportedSkeleton node.boundaryTable node.targetBound
          node.mappedThickenedSkeleton.1) := by
    simpa only [valuesAssignment, originalAssignment,
      TypedCostRegionBoundaryTable.Values.supportedOpenAssignment,
      TypedCostRegionBoundaryTable.Values.supportedAssignment,
      TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton,
      WellSorted.SupportSafeOpenPattern.substitute_pattern] using assignmentStep
  have originalRestoration :
      (TypedCostRegionBoundaryTable.Values.original node.boundaryTable
        ).restoreSupportedSkeleton node.boundaryTable node.targetBound
            node.mappedThickenedSkeleton.1 = node.term.1 := by
    rw [TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton_original]
    exact node.restore_mappedThickenedSkeleton_eq_term
  rw [originalRestoration] at assignmentStep'
  exact Relation.EqvGen.trans _ _ _
    (laws.normalizesCurrentFrame node values) assignmentStep'

end CostStaticRegionNormalizerLaws

mutual
  /-- Every complete proof-relevant region tree normalized by a lawful static
  kernel remains in the authored contextual equation class of its input. -/
  theorem CostRegionTree.normalizeWithStatic_equationEquiv
      {source : CIGSLT} (normalizeStatic : CostStaticRegionNormalizer source)
      (laws : CostStaticRegionNormalizerLaws source normalizeStatic)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (tree : CostRegionTree source targetFree available outer pattern type) :
      ReflectiveEquationSemantics.ReflectiveEquationEquiv
        source.costWholeReflectionProfile defaultBasePremises
        source.costWholeLanguage
        (tree.normalize (normalizeStatic := normalizeStatic)).pattern pattern :=
    match tree with
    | @CostRegionTree.bvar _ _ available outer index type lookup => by
        simpa only [CostRegionTree.normalize,
          ReflectiveEquationSemantics.ReflectiveEquationEquiv] using
            (Relation.EqvGen.refl (Pattern.bvar index) :
              Relation.EqvGen
                (ReflectiveEquationSemantics.ReflectiveEquationContextStep
                  source.costWholeReflectionProfile defaultBasePremises
                  source.costWholeLanguage)
                (.bvar index) (.bvar index))
    | @CostRegionTree.fvar _ _ available outer name type lookup => by
        simpa only [CostRegionTree.normalize,
          ReflectiveEquationSemantics.ReflectiveEquationEquiv] using
            (Relation.EqvGen.refl (Pattern.fvar name) :
              Relation.EqvGen
                (ReflectiveEquationSemantics.ReflectiveEquationContextStep
                  source.costWholeReflectionProfile defaultBasePremises
                  source.costWholeLanguage)
                (.fvar name) (.fvar name))
    | @CostRegionTree.static _ _ color outer node children => by
        have valuesEquivalent :
            ((children.normalizeValues (normalizeStatic := normalizeStatic)
              ).supportedOpenAssignment node.boundaryTable).Equivalent
              ((TypedCostRegionBoundaryTable.Values.original
                node.boundaryTable).supportedOpenAssignment
                  node.boundaryTable) :=
          children.normalizeValuesWithStatic_equivalent_original
            normalizeStatic laws
        have normalized := laws.normalizesOriginal node
          (children.normalizeValues (normalizeStatic := normalizeStatic))
          valuesEquivalent
        simpa only [CostRegionTree.normalize] using normalized
    | @CostRegionTree.neutralApplicationOrdinary _ _ available outer rule
        arguments membership notBareCollection constructor materializes neutral
        ordinary children => by
        simpa only [CostRegionTree.normalize] using
          ReflectiveEquationSemantics.equationEquiv_apply_of_forall₂ _
            (children.normalizeWithStatic_equivalent_original
              normalizeStatic laws)
    | @CostRegionTree.neutralApplicationQuote _ _ available outer rule
        arguments membership notBareCollection constructor materializes neutral
        quoted children => by
        simpa only [CostRegionTree.normalize] using
          ReflectiveEquationSemantics.equationEquiv_apply_of_forall₂ _
            (children.normalizeWithStatic_equivalent_original
              normalizeStatic laws)
    | @CostRegionTree.lambda _ _ available outer binder body domain codomain
        bodyTree => by
        have bodyEquivalent :=
          bodyTree.normalizeWithStatic_equationEquiv normalizeStatic laws
        simpa only [CostRegionTree.normalize, OneHoleContext.fill] using
          ReflectiveEquationSemantics.equationEquiv_fill
            (.lambda _ .hole) bodyEquivalent
    | @CostRegionTree.multiLambda _ _ available outer arity binders body domain
        codomain bodyTree => by
        have bodyEquivalent :=
          bodyTree.normalizeWithStatic_equationEquiv normalizeStatic laws
        simpa only [CostRegionTree.normalize, OneHoleContext.fill] using
          ReflectiveEquationSemantics.equationEquiv_fill
            (.multiLambda _ _ .hole) bodyEquivalent
    | @CostRegionTree.subst _ _ available outer body replacement domain codomain
        bodyTree replacementTree => by
        have bodyEquivalent :=
          bodyTree.normalizeWithStatic_equationEquiv normalizeStatic laws
        have replacementEquivalent :=
          replacementTree.normalizeWithStatic_equationEquiv normalizeStatic laws
        have bodyStep := ReflectiveEquationSemantics.equationEquiv_fill
          (.substBody .hole
            (replacementTree.normalize
              (normalizeStatic := normalizeStatic)).pattern)
          bodyEquivalent
        have replacementStep := ReflectiveEquationSemantics.equationEquiv_fill
          (.substReplacement body .hole) replacementEquivalent
        have bodyStep' :
            ReflectiveEquationSemantics.ReflectiveEquationEquiv
            source.costWholeReflectionProfile defaultBasePremises
            source.costWholeLanguage
            (.subst
              (bodyTree.normalize
                (normalizeStatic := normalizeStatic)).pattern
              (replacementTree.normalize
                (normalizeStatic := normalizeStatic)).pattern)
            (.subst body
              (replacementTree.normalize
                (normalizeStatic := normalizeStatic)).pattern) := by
          simpa only [CostRegionTree.normalize, OneHoleContext.fill] using
            bodyStep
        have replacementStep' :
            ReflectiveEquationSemantics.ReflectiveEquationEquiv
              source.costWholeReflectionProfile defaultBasePremises
              source.costWholeLanguage
              (.subst body
                (replacementTree.normalize
                  (normalizeStatic := normalizeStatic)).pattern)
              (.subst body replacement) := by
          simpa only [OneHoleContext.fill] using replacementStep
        have combined :
            ReflectiveEquationSemantics.ReflectiveEquationEquiv
            source.costWholeReflectionProfile defaultBasePremises
            source.costWholeLanguage
            (.subst
              (bodyTree.normalize
                (normalizeStatic := normalizeStatic)).pattern
              (replacementTree.normalize
                (normalizeStatic := normalizeStatic)).pattern)
            (.subst body replacement) := by
          unfold ReflectiveEquationSemantics.ReflectiveEquationEquiv at bodyStep' replacementStep' ⊢
          exact Relation.EqvGen.trans _ _ _ bodyStep' replacementStep'
        simpa only [CostRegionTree.normalize] using combined
    | @CostRegionTree.collection _ _ available outer collectionType elements
        rest elementType children => by
        simpa only [CostRegionTree.normalize] using
          ReflectiveEquationSemantics.equationEquiv_collection_of_forall₂ _ _
            (children.normalizeWithStatic_equivalent_original
              normalizeStatic laws)
  termination_by tree.weight
  decreasing_by
    all_goals subst_vars
    all_goals simp [CostRegionTree.weight]
    all_goals omega

  /-- Constructor arguments remain pointwise equivalent to their authored
  inputs under a lawful static kernel. -/
  theorem CostRegionArgumentTrees.normalizeWithStatic_equivalent_original
      {source : CIGSLT} (normalizeStatic : CostStaticRegionNormalizer source)
      (laws : CostStaticRegionNormalizerLaws source normalizeStatic)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (trees : CostRegionArgumentTrees source targetFree available outer
        arguments parameters) :
      List.Forall₂
        (ReflectiveEquationSemantics.ReflectiveEquationEquiv
          source.costWholeReflectionProfile defaultBasePremises
          source.costWholeLanguage)
        (trees.normalize (normalizeStatic := normalizeStatic)).patterns
        arguments :=
    match trees with
    | @CostRegionArgumentTrees.nil _ _ available outer => by
        simpa only [CostRegionArgumentTrees.normalize] using
          (List.Forall₂.nil : List.Forall₂
            (ReflectiveEquationSemantics.ReflectiveEquationEquiv
              source.costWholeReflectionProfile defaultBasePremises
              source.costWholeLanguage) [] [])
    | @CostRegionArgumentTrees.cons _ _ available outer argument arguments
        parameter parameters expected representation parameterType head tail => by
        simpa only [CostRegionArgumentTrees.normalize] using
          List.Forall₂.cons
            (head.normalizeWithStatic_equationEquiv normalizeStatic laws)
            (tail.normalizeWithStatic_equivalent_original
              normalizeStatic laws)
  termination_by trees.weight
  decreasing_by
    all_goals simp [CostRegionArgumentTrees.weight]
    all_goals omega

  /-- Homogeneous collection elements remain pointwise equivalent to their
  authored inputs under a lawful static kernel. -/
  theorem CostRegionElementTrees.normalizeWithStatic_equivalent_original
      {source : CIGSLT} (normalizeStatic : CostStaticRegionNormalizer source)
      (laws : CostStaticRegionNormalizerLaws source normalizeStatic)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (trees : CostRegionElementTrees source targetFree available outer elements
        elementType) :
      List.Forall₂
        (ReflectiveEquationSemantics.ReflectiveEquationEquiv
          source.costWholeReflectionProfile defaultBasePremises
          source.costWholeLanguage)
        (trees.normalize (normalizeStatic := normalizeStatic)).patterns
        elements :=
    match trees with
    | @CostRegionElementTrees.nil _ _ available outer elementType => by
        simpa only [CostRegionElementTrees.normalize] using
          (List.Forall₂.nil : List.Forall₂
            (ReflectiveEquationSemantics.ReflectiveEquationEquiv
              source.costWholeReflectionProfile defaultBasePremises
              source.costWholeLanguage) [] [])
    | @CostRegionElementTrees.cons _ _ available outer element elements
        elementType head tail => by
        simpa only [CostRegionElementTrees.normalize] using
          List.Forall₂.cons
            (head.normalizeWithStatic_equationEquiv normalizeStatic laws)
            (tail.normalizeWithStatic_equivalent_original
              normalizeStatic laws)
  termination_by trees.weight
  decreasing_by
    all_goals simp [CostRegionElementTrees.weight]
    all_goals omega

  /-- Recursively normalized boundary values are pointwise equivalent to the
  exact original values under every surrounding binder weakening. -/
  theorem CostRegionBoundaryTrees.normalizeValuesWithStatic_equivalent_original
      {source : CIGSLT} (normalizeStatic : CostStaticRegionNormalizer source)
      (laws : CostStaticRegionNormalizerLaws source normalizeStatic)
      {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
      (trees : CostRegionBoundaryTrees source targetFree color table) :
      ((trees.normalizeValues (normalizeStatic := normalizeStatic)
        ).supportedOpenAssignment table).Equivalent
        ((TypedCostRegionBoundaryTable.Values.original table
          ).supportedOpenAssignment table) :=
    match trees with
    | @CostRegionBoundaryTrees.nil _ _ color => by
        intro lookup shift
        simp only [CostRegionBoundaryTrees.normalizeValues,
          TypedCostRegionBoundaryTable.Values.original,
          ReflectiveEquationSemantics.ReflectiveEquationEquiv]
        exact Relation.EqvGen.refl _
    | @CostRegionBoundaryTrees.cons _ _ color occurrence occurrences boundary
        content tail head children => by
        let value : ReflectiveWellSorted.OpenPattern
            source.costWholeReflectionProfile source.costWholeLanguage targetFree
            boundary.boundary.targetSupport boundary.boundary.targetType := by
          refine ⟨(head.normalize
            (normalizeStatic := normalizeStatic)).pattern, ?_⟩
          exact ⟨⟨by simpa only [List.append_nil] using
                (head.normalize (normalizeStatic := normalizeStatic)).typed,
              (head.normalize
                (normalizeStatic := normalizeStatic)).canonicalBinderMetadata
                boundary.contentCanonicalBinderMetadata,
              (head.normalize
                (normalizeStatic := normalizeStatic)).objectPattern
                  boundary.contentObjectPattern,
              by
                change (head.normalize
                  (normalizeStatic := normalizeStatic)).pattern.isWellScopedAt
                    boundary.boundary.targetSupport.length = true
                simpa only [List.append_nil] using
                  (head.normalize (normalizeStatic := normalizeStatic)).typed.isWellScopedAt⟩,
            by
              intro presentation membership
              exact (head.normalize
                (normalizeStatic := normalizeStatic)).reflectiveScope
                  presentation membership
                  (Nat.le_refl boundary.boundary.targetSupport.length)
                  (boundary.contentReflectiveScopeSafe
                    presentation membership)⟩
        have headEquivalent : ∀ shift,
            ReflectiveEquationSemantics.ReflectiveEquationEquiv
              source.costWholeReflectionProfile defaultBasePremises
              source.costWholeLanguage
              (liftBVars 0 shift value.1)
              (liftBVars 0 shift boundary.boundary.content) := by
          intro shift
          simpa only [value] using equationEquiv_liftBVars
            laws.ambientRenamingStable 0 shift
              (head.normalizeWithStatic_equationEquiv normalizeStatic laws)
        have tailEquivalent :
            ((children.normalizeValues (normalizeStatic := normalizeStatic)
              ).supportedOpenAssignment tail).Equivalent
              ((TypedCostRegionBoundaryTable.Values.original tail
                ).supportedOpenAssignment tail) :=
          children.normalizeValuesWithStatic_equivalent_original
            normalizeStatic laws
        intro lookup shift
        simpa only [CostRegionBoundaryTrees.normalizeValues, value] using
          (TypedCostRegionBoundaryTable.Values.supportedOpenAssignment_cons_equivalent
            value
            (children.normalizeValues (normalizeStatic := normalizeStatic))
            headEquivalent tailEquivalent lookup shift)
  termination_by trees.weight
  decreasing_by
    all_goals simp [CostRegionBoundaryTrees.weight]
    all_goals omega
end

/-- Any two proof-relevant decompositions of the same compact typed term have
hereditarily normalized representatives in the same authored equation class. -/
theorem CostRegionTree.normalizeWithStatic_overlap_equivalent
    {source : CIGSLT} (normalizeStatic : CostStaticRegionNormalizer source)
    (laws : CostStaticRegionNormalizerLaws source normalizeStatic)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (first second : CostRegionTree source targetFree available outer pattern
      type) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage
      (first.normalize (normalizeStatic := normalizeStatic)).pattern
      (second.normalize (normalizeStatic := normalizeStatic)).pattern := by
  have firstToInput :=
    first.normalizeWithStatic_equationEquiv normalizeStatic laws
  have secondToInput :=
    second.normalizeWithStatic_equationEquiv normalizeStatic laws
  unfold ReflectiveEquationSemantics.ReflectiveEquationEquiv at firstToInput secondToInput ⊢
  exact Relation.EqvGen.trans _ _ _ firstToInput
    (Relation.EqvGen.symm _ _ secondToInput)

namespace CostOpenElaboration

/-- Normalize one retained elaboration with an explicit static kernel and
repackage the result in the same checked open fibre.  This is the generic
hereditary executor core; a concrete language supplies only the static
normalizer and its local laws. -/
def normalizeWithStaticErasure
    {source : CIGSLT} (normalizeStatic : CostStaticRegionNormalizer source)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort}
    (elaboration : CostOpenElaboration source term) :
    ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort := by
  let normalized := elaboration.tree.normalize
    (normalizeStatic := normalizeStatic)
  refine ⟨normalized.pattern, ?_⟩
  refine ⟨⟨?_, normalized.canonicalBinderMetadata term.2.1.2.1,
    normalized.objectPattern term.2.1.2.2.1, ?_⟩, ?_⟩
  · simpa only [List.append_nil] using normalized.typed
  · change normalized.pattern.isWellScopedAt targetBound.length = true
    simpa only [List.append_nil] using normalized.typed.isWellScopedAt
  · intro presentation membership
    exact normalized.reflectiveScope presentation membership
      (Nat.le_refl targetBound.length) (term.2.2 presentation membership)

@[simp]
theorem normalizeWithStaticErasure_pattern
    {source : CIGSLT} (normalizeStatic : CostStaticRegionNormalizer source)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort}
    (elaboration : CostOpenElaboration source term) :
    (elaboration.normalizeWithStaticErasure normalizeStatic).1 =
      (elaboration.tree.normalize
        (normalizeStatic := normalizeStatic)).pattern :=
  rfl

/-- Typed unary soundness of the generic hereditary executor.  The proof
retains every intermediate equation vertex in the exact open fibre; it uses
only the local typed static-frame law and structural weakening. -/
theorem normalizeWithStaticErasure_typed_openEquationSetoid
    {source : CIGSLT} (normalizeStatic : CostStaticRegionNormalizer source)
    (laws : CostTypedStaticRegionNormalizerLaws source normalizeStatic)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort}
    (elaboration : CostOpenElaboration source term) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      source.costWholeReflectionProfile defaultBasePremises
        source.costWholeLanguage targetFree targetBound
          (.base targetSort.1)).r
      (elaboration.normalizeWithStaticErasure normalizeStatic) term := by
  have split := elaboration.tree.normalizeWithStatic_equationSetoid
    normalizeStatic laws term.2.1.2.1 term.2.1.2.2.1 term.2.2
  have openSplit :=
    WellSorted.AvailableOpenPattern.equationSetoid_to_reflectiveOpenPatternEquationSetoid
      split
  have transported :=
    ReflectiveWellSorted.reflectiveOpenPatternEquationSetoid_reindexBound
      (List.append_nil targetBound) openSplit
  have leftEndpoint :
      ((elaboration.tree.normalizedAvailable term.2.1.2.1 term.2.1.2.2.1
        term.2.2 (normalizeStatic := normalizeStatic)
          ).toReflectiveOpenPattern.reindexBound
            (List.append_nil targetBound)) =
        elaboration.normalizeWithStaticErasure normalizeStatic := by
    apply Subtype.ext
    simp [CostOpenElaboration.normalizeWithStaticErasure,
      CostRegionTree.normalizedAvailable_pattern,
      ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
      WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern]
  have rightEndpoint :
      ((elaboration.tree.originalAvailableOpenPattern term.2.1.2.1
        term.2.1.2.2.1 term.2.2).toReflectiveOpenPattern.reindexBound
          (List.append_nil targetBound)) = term := by
    apply Subtype.ext
    simp [CostRegionTree.originalAvailableOpenPattern_pattern,
      ReflectiveWellSorted.OpenPattern.reindexBound_pattern,
      WellSorted.AvailableOpenPattern.toReflectiveOpenPattern_pattern]
  rw [leftEndpoint, rightEndpoint] at transported
  exact transported

end CostOpenElaboration

/-- Generic checked hereditary Cost normalizer.  The construction is
language-independent: it compiles one admitted open term into its retained
Cost tree, normalizes children before static parents, and erases only the
proof-relevant decomposition. -/
def CIGSLT.costNormalizeOpenWithStatic (source : CIGSLT)
    (normalizeStatic : CostStaticRegionNormalizer source)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort) :
    ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort :=
  (CostOpenElaboration.compile source term).normalizeWithStaticErasure
    normalizeStatic

@[simp]
theorem CIGSLT.costNormalizeOpenWithStatic_pattern (source : CIGSLT)
    (normalizeStatic : CostStaticRegionNormalizer source)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort) :
    (source.costNormalizeOpenWithStatic normalizeStatic term).1 =
      ((CostOpenElaboration.compile source term).tree.normalize
        (normalizeStatic := normalizeStatic)).pattern :=
  rfl

/-- The previously established compact executor is exactly the generic
hereditary executor instantiated by its original mapped-action static
normalizer.  This definitional compatibility is the anti-duplication seam:
parameterization adds no second execution semantics. -/
theorem CIGSLT.costNormalizeOpenWithStatic_default_eq
    (source : CIGSLT)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort) :
    source.costNormalizeOpenWithStatic
        (fun node values => node.normalizeWithReflective values) term =
      source.costNormalizeOpen term := by
  apply Subtype.ext
  rfl

/-- Every lawful static kernel yields a unary-sound generic hereditary Cost
normalizer.  Exact generator invariance is deliberately separate: it needs
the two-endpoint alignment proved below the eventual language instance. -/
theorem CIGSLT.costNormalizeOpenWithStatic_equationEquiv
    (source : CIGSLT) (normalizeStatic : CostStaticRegionNormalizer source)
    (laws : CostStaticRegionNormalizerLaws source normalizeStatic)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage
      (source.costNormalizeOpenWithStatic normalizeStatic term).1 term.1 := by
  rw [source.costNormalizeOpenWithStatic_pattern]
  exact (CostOpenElaboration.compile source term).tree
    |>.normalizeWithStatic_equationEquiv normalizeStatic laws

/-- Every locally typed static kernel yields a typed, unary-sound hereditary
Cost normalizer over arbitrary ciGSLTs. -/
theorem CIGSLT.costNormalizeOpenWithStatic_typed_openEquationSetoid
    (source : CIGSLT) (normalizeStatic : CostStaticRegionNormalizer source)
    (laws : CostTypedStaticRegionNormalizerLaws source normalizeStatic)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      source.costWholeReflectionProfile defaultBasePremises
        source.costWholeLanguage targetFree targetBound
          (.base targetSort.1)).r
      (source.costNormalizeOpenWithStatic normalizeStatic term) term :=
  (CostOpenElaboration.compile source term
    ).normalizeWithStaticErasure_typed_openEquationSetoid normalizeStatic laws

/-- Exact erasure coherence for an arbitrary proof-relevant static kernel.
Unlike unary equation soundness, this property states that two certified
decompositions of the same compact term erase to one identical normalized
pattern. -/
def CostStaticRegionNormalizerCompactCoherent
    (source : CIGSLT) (normalizeStatic : CostStaticRegionNormalizer source) :
    Prop :=
  ∀ {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort)
    (first second : CostOpenElaboration source term),
    (first.tree.normalize (normalizeStatic := normalizeStatic)).pattern =
      (second.tree.normalize (normalizeStatic := normalizeStatic)).pattern

/-- Structural unambiguity makes exact compact output independent of every
proof-relevant compiler choice for any fixed static normalization kernel. -/
theorem CostStaticRegionNode.UnambiguousStaticDecomposition.normalizerCompactCoherent
    {source : CIGSLT}
    (unambiguous :
      CostStaticRegionNode.UnambiguousStaticDecomposition source)
    (normalizeStatic : CostStaticRegionNormalizer source) :
    CostStaticRegionNormalizerCompactCoherent source normalizeStatic := by
  intro targetFree targetBound targetSort term first second
  let compiled := CostRegionTree.buildOpenTerm (source := source) term
  have compiledEq : CostRegionTree.buildFuel? (source := source)
      (targetFree := targetFree) (costRegionPatternWeight term.1 + 1)
        targetBound [] term.1 (.base targetSort.1) = some compiled := by
    simpa only [CostRegionTree.build?] using
      (CostRegionTree.build?_eq_some_buildOpenTerm (source := source) term)
  have firstEq := CostRegionTree.normalize_pattern_eq_of_buildFuel unambiguous
    (normalizeStatic := normalizeStatic)
    (costRegionPatternWeight term.1 + 1) first.tree compiledEq
  have secondEq := CostRegionTree.normalize_pattern_eq_of_buildFuel unambiguous
    (normalizeStatic := normalizeStatic)
    (costRegionPatternWeight term.1 + 1) second.tree compiledEq
  exact firstEq.trans secondEq.symm

end Mettapedia.GSLT.LanguageDef
