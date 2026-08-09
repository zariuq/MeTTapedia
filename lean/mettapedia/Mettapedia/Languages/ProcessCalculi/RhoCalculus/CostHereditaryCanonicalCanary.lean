import Mettapedia.GSLT.LanguageDef.CostSemanticAtom
import Mettapedia.GSLT.LanguageDef.CostSemanticAtomAlignment
import Mettapedia.GSLT.LanguageDef.CostGeneratorHereditaryAlignment
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonical
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryGeneratorClassification

/-!
# Semantic-atom repair canary for the rho Cost ordering obstruction

The established counterexample fails because the outer frame orders a
serialized boundary origin before restoring the child's normalized value.
This file evaluates that same pair through a small semantic-atom frame:

1. normalize the distinguished child meaning (`Quote (Drop 0)` becomes `0`);
2. coalesce that value with the direct source occurrence of `0`;
3. canonicalize the selected rho frame using semantic-value keys; and
4. restore the generated wrapped values.

This is a focused regression canary for the repaired factorization.  It is not
yet the general atom-environment construction or the global generator theorem.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample

/-- Reserved atoms are internal to one finite frame evaluation.  Their names
are never used as semantic ordering keys. -/
def rhoCutOrderZeroAtom : String := "$cost:semantic-atom:0"

def rhoCutOrderAAtom : String := "$cost:semantic-atom:1"

/-- Reify one normalized outer parameter into the common semantic-atom
inventory of the counterexample. -/
def reifyRhoCutOrderParameter : Pattern → Pattern
  | pattern =>
      if pattern = rhoCutOrderRedex then
        .fvar rhoCutOrderZeroAtom
      else if pattern = .fvar "0" then
        .fvar rhoCutOrderZeroAtom
      else if pattern = .fvar "a" then
        .fvar rhoCutOrderAAtom
      else
        pattern

/-- Project the wrapped target endpoint to its selected source-colour frame,
replacing only external parameter values by semantic atoms. -/
def reifyRhoCutOrderFrame : Pattern → Pattern
  | .collection .hashBag
      [.apply wrappedDrop [first], .apply secondWrappedDrop [second]] none =>
      if wrappedDrop = costWrappedConstructorName "PDrop" ∧
          secondWrappedDrop = costWrappedConstructorName "PDrop" then
        .collection .hashBag
          [.apply "PDrop" [reifyRhoCutOrderParameter first],
            .apply "PDrop" [reifyRhoCutOrderParameter second]] none
      else
        .collection .hashBag
          [.apply wrappedDrop [first], .apply secondWrappedDrop [second]] none
  | pattern => pattern

/-- Both endpoints induce the same semantic frame after the child meaning is
known.  This is the coalescence step missing from the old executor. -/
theorem rhoCutOrder_reify_frames_equal :
    reifyRhoCutOrderFrame rhoCutOrderLeftPattern =
      reifyRhoCutOrderFrame rhoCutOrderRightPattern := by
  simp [reifyRhoCutOrderFrame, reifyRhoCutOrderParameter,
    rhoCutOrderLeftPattern, rhoCutOrderRightPattern, rhoCutOrderParallel,
    rhoCutOrderWrappedDrop, rhoCutOrderRedex, rhoCutOrderBaseQuote,
    rhoCutOrderBaseDrop, rhoCutOrderZeroAtom, rhoCutOrderAAtom]

def rhoCutOrderAtomFrame : Pattern :=
  .collection .hashBag
    [.apply "PDrop" [.fvar rhoCutOrderZeroAtom],
      .apply "PDrop" [.fvar rhoCutOrderAAtom]] none

theorem rhoCutOrder_reify_left :
    reifyRhoCutOrderFrame rhoCutOrderLeftPattern = rhoCutOrderAtomFrame := by
  simp [reifyRhoCutOrderFrame, reifyRhoCutOrderParameter,
    rhoCutOrderAtomFrame, rhoCutOrderLeftPattern, rhoCutOrderParallel,
    rhoCutOrderWrappedDrop, rhoCutOrderRedex, rhoCutOrderBaseQuote,
    rhoCutOrderBaseDrop, rhoCutOrderZeroAtom, rhoCutOrderAAtom]

theorem rhoCutOrder_reify_right :
    reifyRhoCutOrderFrame rhoCutOrderRightPattern = rhoCutOrderAtomFrame := by
  simp [reifyRhoCutOrderFrame, reifyRhoCutOrderParameter,
    rhoCutOrderAtomFrame, rhoCutOrderRightPattern, rhoCutOrderParallel,
    rhoCutOrderWrappedDrop, rhoCutOrderRedex, rhoCutOrderBaseQuote,
    rhoCutOrderBaseDrop, rhoCutOrderZeroAtom, rhoCutOrderAAtom]

/-- The ordering key is computed from normalized parameter meanings rather
than the reserved atom spelling. -/
def rhoCutOrderSemanticKey : Pattern → Nat
  | .apply "PDrop" [.fvar name] =>
      if name = rhoCutOrderZeroAtom then 0
      else if name = rhoCutOrderAAtom then 1
      else patternCode (.apply "PDrop" [.fvar name]) + 2
  | pattern => patternCode pattern + 2

/-- The source rho declaration remains the sole equation authority. -/
def rhoCutOrderDeclaration : ReflectivePresentationDecl :=
  rhoReflectivePresentation.toReflectivePresentationDecl

/-- Semantic-key canonicalization leaves the already value-ordered atom frame
in its exact representative. -/
theorem rhoCutOrder_atomFrame_canonical :
    canonicalizeBy rhoCutOrderSemanticKey rhoCutOrderDeclaration
        rhoCutOrderAtomFrame =
      rhoCutOrderAtomFrame := by
  simp [rhoCutOrderAtomFrame, canonicalizeBy, canonicalizeListBy,
    normalizeParallelElementsBy, sortPatternsBy,
    parallelSplice, collapseParallel, rhoCutOrderSemanticKey,
    rhoCutOrderDeclaration, rhoReflectivePresentation,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
    rhoCutOrderZeroAtom, rhoCutOrderAAtom, List.mergeSort]

mutual
  /-- Restore the two closed atom values after mapping the selected source
  frame into the wrapped Cost stratum. -/
  def restoreRhoCutOrderAtoms : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name =>
        if name = rhoCutOrderZeroAtom then .fvar "0"
        else if name = rhoCutOrderAAtom then .fvar "a"
        else .fvar name
    | .apply constructor arguments =>
        .apply constructor (restoreRhoCutOrderAtomList arguments)
    | .lambda binder body =>
        .lambda binder (restoreRhoCutOrderAtoms body)
    | .multiLambda arity binders body =>
        .multiLambda arity binders (restoreRhoCutOrderAtoms body)
    | .subst body replacement =>
        .subst (restoreRhoCutOrderAtoms body)
          (restoreRhoCutOrderAtoms replacement)
    | .collection collectionType elements rest =>
        .collection collectionType (restoreRhoCutOrderAtomList elements) rest

  def restoreRhoCutOrderAtomList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        restoreRhoCutOrderAtoms pattern ::
          restoreRhoCutOrderAtomList patterns
end

/-- The repaired order of operations closes the exact compact discrepancy:
semantic-key canonicalization, static mapping, and value restoration produce
the right endpoint's compact normal representative. -/
theorem rhoCutOrder_atomClosed_normal_canary :
    restoreRhoCutOrderAtoms
        (mapPattern (CostStaticColor.wrapped.symbols rhoCIGSLT)
          (canonicalizeBy rhoCutOrderSemanticKey rhoCutOrderDeclaration
            (reifyRhoCutOrderFrame rhoCutOrderLeftPattern))) =
      rhoCutOrderRightPattern := by
  rw [rhoCutOrder_reify_left, rhoCutOrder_atomFrame_canonical]
  simp [rhoCutOrderAtomFrame, restoreRhoCutOrderAtoms,
    restoreRhoCutOrderAtomList, mapPattern, CostStaticColor.symbols,
    costWrappedStaticSymbols, rhoCutOrderRightPattern, rhoCutOrderParallel,
    rhoCutOrderWrappedDrop, rhoCutOrderZeroAtom, rhoCutOrderAAtom]

/-- The direct endpoint evaluates to the same representative through the same
atom-closed path. -/
theorem rhoCutOrder_atomClosed_right_canary :
    restoreRhoCutOrderAtoms
        (mapPattern (CostStaticColor.wrapped.symbols rhoCIGSLT)
          (canonicalizeBy rhoCutOrderSemanticKey rhoCutOrderDeclaration
            (reifyRhoCutOrderFrame rhoCutOrderRightPattern))) =
      rhoCutOrderRightPattern := by
  rw [rhoCutOrder_reify_right, rhoCutOrder_atomFrame_canonical]
  simp [rhoCutOrderAtomFrame, restoreRhoCutOrderAtoms,
    restoreRhoCutOrderAtomList, mapPattern, CostStaticColor.symbols,
    costWrappedStaticSymbols, rhoCutOrderRightPattern, rhoCutOrderParallel,
    rhoCutOrderWrappedDrop, rhoCutOrderZeroAtom, rhoCutOrderAAtom]

/-! ## Production semantic-atom regression -/

/-- The actual typed base-colour Quote/Drop frame and its structural source
variable meet at one retained semantic atom. -/
noncomputable def rhoCutOrderBaseRedexNodeSemanticAtomJoin :
    PackedCostSemanticAtomJoin rhoCIGSLT
      (CostStaticRegionNode.normalizeHereditary rhoCutOrderBaseRedexNode
        (TypedCostRegionBoundaryTable.Values.original
          rhoCutOrderBaseRedexNode.finiteBoundaryTable)).1
      (.fvar "0") := by
  let values := TypedCostRegionBoundaryTable.Values.original
    rhoCutOrderBaseRedexNode.finiteBoundaryTable
  let packed := rhoCutOrderBaseRedexNode.semanticAtomEnvironment values
  let inventory := packed.1
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  have sourceMembership : costRegionSourceVariableName "0" ∈
      rhoCutOrderBaseRedexNode.skeleton.1.freeFvarNames := by
    rw [rhoCutOrderBaseRedexNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  have occurrenceExists := rhoCutOrderBaseRedexNode.skeleton_fvar_covered
    (costRegionSourceVariableName "0") sourceMembership
  let occurrence := Classical.choose occurrenceExists
  have occurrenceName := Classical.choose_spec occurrenceExists
  have slotExists := environment.slotOfName?_isSome_of_occurrence occurrence
  let slot := (environment.slotOfName? occurrence.name).get slotExists
  have selectedAtOccurrence : environment.slotOfName? occurrence.name =
      some slot := (Option.some_get slotExists).symm
  have selected : environment.slotOfName?
      (costRegionSourceVariableName "0") = some slot := by
    rw [← occurrenceName]
    exact selectedAtOccurrence
  have reifiedFrame :
      (rhoCutOrderBaseRedexNode.reifiedSourceFrame environment).1 =
        .apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor
            [.fvar (environment.atomName slot)]] := by
    rw [rhoCutOrderBaseRedexNode.reifiedSourceFrame_pattern]
    change environment.reify
        (.apply "NQuote"
          [.apply "PDrop" [.fvar (costRegionSourceVariableName "0")]]) = _
    simp [CostStaticAtomEnvironment.reify,
      CostStaticAtomEnvironment.reifyName, selected,
      rhoReflectivePresentation]
  exact CostStaticRegionNode.quoteDropSourceVariableSemanticAtomJoin
    rhoCutOrderBaseRedexNode values occurrence "0" occurrenceName slot
      selectedAtOccurrence reifiedFrame

/-- The actual typed hereditary frame kernel, not the hand-written canary,
collapses the base-colour Quote/Drop child to its source value. -/
theorem rhoCutOrderBaseRedexNode_normalizeHereditary :
    (CostStaticRegionNode.normalizeHereditary rhoCutOrderBaseRedexNode
      (TypedCostRegionBoundaryTable.Values.original
        rhoCutOrderBaseRedexNode.finiteBoundaryTable)).1 =
      .fvar "0" := by
  exact rhoCutOrderBaseRedexNodeSemanticAtomJoin.results_eq

/-- Structural right endpoint of the selected Quote/Drop cell.  Free
variables are structural leaves of the region tree, never static roots. -/
def rhoCutOrderZeroStructuralTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] [] (.fvar "0")
      (.base (costBaseSortName "Name")) :=
  .fvar (by rfl)

/-- The intrinsic static tree exposes exactly the node normalizer result.
The empty child forest contributes the original finite boundary values. -/
theorem rhoCutOrderBaseRedexStaticTree_normalizeHereditary_eq_node :
    (rhoCutOrderBaseRedexStaticTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (CostStaticRegionNode.normalizeHereditary rhoCutOrderBaseRedexNode
        (TypedCostRegionBoundaryTable.Values.original
          rhoCutOrderBaseRedexNode.finiteBoundaryTable)).1 := by
  unfold rhoCutOrderBaseRedexStaticTree
  rw [CostRegionTree.normalize_static_pattern]
  rw [rhoCutOrderBaseRedexChildren.normalizeValues_eq_original_of_entries_eq_nil
    (normalizeStatic := rhoHereditaryStaticNormalizer) (empty := by rfl)]
  rfl

/-- The compactly reindexed base tree has the same hereditary result as its
intrinsic static node; no dependent boundary table is unfolded. -/
theorem rhoCutOrderBaseRedexTree_normalizeHereditary_eq_node :
    (rhoCutOrderBaseRedexTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (CostStaticRegionNode.normalizeHereditary rhoCutOrderBaseRedexNode
        (TypedCostRegionBoundaryTable.Values.original
          rhoCutOrderBaseRedexNode.finiteBoundaryTable)).1 := by
  unfold rhoCutOrderBaseRedexTree
  rw [CostRegionTree.reindexType_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer),
    CostRegionTree.reindexPattern_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer),
    CostRegionTree.reindexAvailable_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)]
  exact rhoCutOrderBaseRedexStaticTree_normalizeHereditary_eq_node

/-- Positive selected-root regression: the exact generated Quote/Drop region
aligns to the structural source variable through one retained semantic atom. -/
noncomputable def rhoCutOrderBaseSelectedTreeNormalizationAlignment :
    CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
        rhoCutOrderBaseRedexTree rhoCutOrderZeroStructuralTree := by
  refine .semanticAtom rhoCutOrderBaseRedexTree
    rhoCutOrderZeroStructuralTree ?_
  exact rhoCutOrderBaseRedexNodeSemanticAtomJoin.transport
    rhoCutOrderBaseRedexTree_normalizeHereditary_eq_node (by
      change (rhoCutOrderZeroStructuralTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          .fvar "0"
      simp [rhoCutOrderZeroStructuralTree, CostRegionTree.normalize])

/-- The selected-root alignment derives the exact compact equality; the
endpoint theorem is not stored as the alignment certificate. -/
theorem rhoCutOrderBaseSelectedTreeNormalizationAlignment_pattern_eq :
    (rhoCutOrderBaseRedexTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (rhoCutOrderZeroStructuralTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  simpa [rhoHereditaryNormalizationKernel] using
    rhoCutOrderBaseSelectedTreeNormalizationAlignment.normalize_pattern_eq

/-- Exact generated Name sort of the selected base-colour cell. -/
def rhoCutOrderBaseSelectedNameSort :
    LangSort rhoCIGSLT.costWholeLanguage :=
  CostStaticColor.base.mapLangSort rhoCIGSLT
    rhoCutOrderBaseRedexNode.sourceSort

/-- Checked left endpoint of the selected base-colour cell. -/
def rhoCutOrderBaseSelectedLeft :
    ReflectiveWellSorted.OpenTerm rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
        rhoCutOrderBaseSelectedNameSort :=
  ReflectiveWellSorted.OpenTerm.reindex rfl
    rhoCutOrderBaseRedexNode_targetBound rfl
    rhoCutOrderBaseRedexNode.termReflective

/-- Checked structural right endpoint of the selected base-colour cell. -/
def rhoCutOrderBaseSelectedRight :
    ReflectiveWellSorted.OpenTerm rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
        rhoCutOrderBaseSelectedNameSort := by
  have sortName : rhoCutOrderBaseSelectedNameSort.1 =
      costBaseSortName "Name" := by
    exact TypeExpr.base.inj rhoCutOrderBaseRedexNode_resultType
  refine ⟨.fvar "0", ?_⟩
  refine ⟨⟨.fvar ?_, rfl, rfl, rfl⟩, ?_⟩
  · simp [rhoCutOrderFree, FreeTypeContext.ofList, sortName]
  · intro declaration membership
    rfl

@[simp]
theorem rhoCutOrderBaseSelectedLeft_pattern :
    rhoCutOrderBaseSelectedLeft.1 = rhoCutOrderRedex := by
  rw [rhoCutOrderBaseSelectedLeft,
    ReflectiveWellSorted.OpenTerm.reindex_pattern]
  change rhoCutOrderBaseRedexNode.term.1 = rhoCutOrderRedex
  exact rhoCutOrderBaseRedexNode_term_pattern

@[simp]
theorem rhoCutOrderBaseSelectedRight_pattern :
    rhoCutOrderBaseSelectedRight.1 = .fvar "0" :=
  rfl

/-- The exact outer occurrence restricts to its retained Quote/Drop redex
without reconstructing declaration identity from proposition-valued support. -/
def rhoCutOrderBaseSelectedGeneratorWitness :
    ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage rhoCutOrderBaseSelectedLeft.1
        rhoCutOrderBaseSelectedRight.1 := by
  change ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
    rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage rhoCutOrderRedex (.fvar "0")
  exact rhoCutOrderGeneratorWitness.atRedex

/-- Any absorber for a retained base-tagged Quote/Drop cell has the base
declaration colour; the wrapped declaration cannot collapse those exact
constructors. -/
theorem rhoCutOrderAbsorption_color_of_redex
    {left right : Pattern}
    {witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right}
    (redex : witness.redex = rhoCutOrderRedex)
    (contractum : witness.contractum = .fvar "0")
    (absorption : RhoCostGeneratorAbsorption witness) :
    absorption.color = .base := by
  cases color : absorption.color with
  | base => rfl
  | wrapped =>
      have representatives := absorption.representatives
      rw [absorption.declaration_eq] at representatives
      rw [redex, contractum, color] at representatives
      simp [rhoCutOrderRedex, rhoCutOrderBaseQuote, rhoCutOrderBaseDrop,
        costStaticReflectivePresentationDecl,
        costWrappedReflectivePresentationDecl,
        ReflectionExtension.mapReflectivePresentation,
        costWrappedStaticReflectiveSymbols, costWrappedStaticSymbols,
        rhoReflectivePresentation,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
        costBaseConstructorName, costWrappedConstructorName,
        costBaseConstructorTag, costWrappedConstructorTag] at representatives

/-- The selected local witness is the base branch of the classifier. -/
theorem rhoCutOrderBaseSelectedAbsorption_color
    (absorption : RhoCostGeneratorAbsorption
      rhoCutOrderBaseSelectedGeneratorWitness) :
    absorption.color = .base :=
  rhoCutOrderAbsorption_color_of_redex rfl rfl absorption

/-- Support erasure of the retained selected-root occurrence. -/
theorem rhoCutOrderBaseSelected_generator :
    ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      (.base rhoCutOrderBaseSelectedNameSort.1) rhoCutOrderBaseSelectedLeft
        rhoCutOrderBaseSelectedRight :=
  rhoCutOrderBaseSelectedGeneratorWitness.erase

/-- The compactly reindexed selected endpoint still exposes its exact base
static root.  Index transport changes no decomposition data. -/
def rhoCutOrderBaseRedexTree_staticRootColor :
    CostRegionTree.StaticRootColor rhoCIGSLT rhoCutOrderFree
      rhoCutOrderBaseRedexTree .base :=
  .reindexType rhoCutOrderBaseRedexNode_resultType _
    (.reindexPattern rhoCutOrderBaseRedexNode_term_pattern _
      (.reindexAvailable rhoCutOrderBaseRedexNode_targetBound _
        (.static rhoCutOrderBaseRedexNode rhoCutOrderBaseRedexChildren)))

/-- Root-only semantic certificate for the selected base Quote/Drop cell. -/
noncomputable def rhoCutOrderBaseSelectedRootBridge :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
        rhoCutOrderBaseRedexTree rhoCutOrderZeroStructuralTree :=
  .semanticAtom rhoCutOrderBaseRedexTree rhoCutOrderZeroStructuralTree
    (rhoCutOrderBaseRedexNodeSemanticAtomJoin.transport
      rhoCutOrderBaseRedexTree_normalizeHereditary_eq_node (by
        change (rhoCutOrderZeroStructuralTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
            .fvar "0"
        simp [rhoCutOrderZeroStructuralTree, CostRegionTree.normalize]))

/-- The selected-root branch of the rho occurrence classifier retains the
exact generated declaration, the decomposition-derived base colour, and the
one-atom semantic certificate. -/
noncomputable def rhoCutOrderBaseSelectedRootAlignment :
    RhoCostGeneratorRootAlignment rhoHereditaryNormalizationKernel
      rhoCutOrderBaseSelected_generator := by
  let absorption := Classical.choice
    (nonempty_rhoCostGeneratorAbsorption
      rhoCutOrderBaseSelectedGeneratorWitness)
  exact
    { occurrence := rhoCutOrderBaseSelectedGeneratorWitness
      erasesTo := Subsingleton.elim _ _
      absorption := absorption
      leftElaboration := ⟨rhoCutOrderBaseRedexTree⟩
      rightElaboration := ⟨rhoCutOrderZeroStructuralTree⟩
      regionColor := .base
      leftRoot := rhoCutOrderBaseRedexTree_staticRootColor
      position := .selected
        (rhoCutOrderBaseSelectedAbsorption_color absorption)
      rootBridge := rhoCutOrderBaseSelectedRootBridge }

/-- Positive classifier canary: the local declaration is selected by the
base root exposed by the retained tree. -/
theorem rhoCutOrderBaseSelectedRootAlignment_isSelected :
    rhoCutOrderBaseSelectedRootAlignment.absorption.color =
      rhoCutOrderBaseSelectedRootAlignment.regionColor := by
  change rhoCutOrderBaseSelectedRootAlignment.absorption.color = .base
  exact rhoCutOrderBaseSelectedAbsorption_color
    rhoCutOrderBaseSelectedRootAlignment.absorption

/-- Unchanged sibling used to exercise single-path structural routing. -/
def rhoCutOrderAStructuralTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] [] (.fvar "a")
      (.base (costBaseSortName "Name")) :=
  .fvar (by rfl)

/-- Shared collection tail; only the leading Quote/Drop occurrence moves. -/
def rhoCutOrderSelectedCollectionTail :
    CostRegionElementTrees rhoCIGSLT rhoCutOrderFree [] [] [.fvar "a"]
      (.base (costBaseSortName "Name")) :=
  .cons rhoCutOrderAStructuralTree
    (.nil [] [] (.base (costBaseSortName "Name")))

def rhoCutOrderSelectedCollectionLeftElements :
    CostRegionElementTrees rhoCIGSLT rhoCutOrderFree [] []
      [rhoCutOrderRedex, .fvar "a"] (.base (costBaseSortName "Name")) :=
  .cons rhoCutOrderBaseRedexTree rhoCutOrderSelectedCollectionTail

def rhoCutOrderSelectedCollectionRightElements :
    CostRegionElementTrees rhoCIGSLT rhoCutOrderFree [] []
      [.fvar "0", .fvar "a"] (.base (costBaseSortName "Name")) :=
  .cons rhoCutOrderZeroStructuralTree rhoCutOrderSelectedCollectionTail

def rhoCutOrderSelectedCollectionLeftTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] []
      (.collection .hashBag [rhoCutOrderRedex, .fvar "a"] none)
      (.collection .hashBag (.base (costBaseSortName "Name"))) :=
  .collection rhoCutOrderSelectedCollectionLeftElements

def rhoCutOrderSelectedCollectionRightTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] []
      (.collection .hashBag [.fvar "0", .fvar "a"] none)
      (.collection .hashBag (.base (costBaseSortName "Name"))) :=
  .collection rhoCutOrderSelectedCollectionRightElements

/-- Positive structural-route regression: the selected semantic root lifts
through exactly one collection element while the sibling tree stays
definitionally unchanged. -/
noncomputable def rhoCutOrderSelectedCollectionRoute :
    CostRegionTreeNormalizationRoute rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
        rhoCutOrderSelectedCollectionLeftTree
        rhoCutOrderSelectedCollectionRightTree :=
  .collection rhoCutOrderSelectedCollectionLeftElements
    rhoCutOrderSelectedCollectionRightElements
    (.head rhoCutOrderBaseRedexTree rhoCutOrderZeroStructuralTree
      rhoCutOrderSelectedCollectionTail (.root rhoCutOrderBaseSelectedRootBridge))

/-- Positive route-localization canary: the selected root is the leading
collection element and the unchanged sibling remains to its right. -/
theorem rhoCutOrderSelectedCollectionRoute_activeContext :
    rhoCutOrderSelectedCollectionRoute.activeContext =
      .collection .hashBag [] .hole [.fvar "a"] none := by
  rfl

/-- Negative route-localization canary: the same semantic root cannot be
misreported as the trailing collection element. -/
theorem rhoCutOrderSelectedCollectionRoute_notTrailing :
    rhoCutOrderSelectedCollectionRoute.activeContext ≠
      .collection .hashBag [.fvar "a"] .hole [] none := by
  decide

/-- Structural routing derives exact equality without reopening the selected
static frame or rechecking its semantic-atom certificate. -/
theorem rhoCutOrderSelectedCollectionRoute_normalize_patterns_eq :
    (rhoCutOrderSelectedCollectionLeftTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (rhoCutOrderSelectedCollectionRightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  exact rhoCutOrderSelectedCollectionRoute.toAlignment.normalize_pattern_eq

/-- The selected branch of the future total occurrence classifier, end to
end: exact authored occurrence, both checked elaborations, and the retained
semantic-atom root alignment. -/
noncomputable def rhoCutOrderBaseSelectedGeneratorTreeAlignment :
    CostGeneratorTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderBaseSelected_generator :=
  rhoCutOrderBaseSelectedRootAlignment.toGeneratorTreeAlignment

/-- The cast-stable tree layer transports the base child result without
unfolding its dependent finite-boundary index. -/
theorem rhoCutOrderBaseRedexTree_normalizeHereditary :
    (CostRegionTree.normalizeHereditary rhoCutOrderBaseRedexTree).pattern =
      .fvar "0" := by
  unfold CostRegionTree.normalizeHereditary rhoCutOrderBaseRedexTree
  rw [CostRegionTree.reindexType_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer),
    CostRegionTree.reindexPattern_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer),
    CostRegionTree.reindexAvailable_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)]
  unfold rhoCutOrderBaseRedexStaticTree
  rw [CostRegionTree.normalize_static_pattern]
  rw [rhoCutOrderBaseRedexChildren.normalizeValues_eq_original_of_entries_eq_nil
    (normalizeStatic := rhoHereditaryStaticNormalizer) (empty := by rfl)]
  exact rhoCutOrderBaseRedexNode_normalizeHereditary

/-- The proof-relevant opposite-colour child retains the same hereditary
normal form through the boundary certificate's dependent index transports. -/
theorem rhoCutOrderBoundaryChild_normalizeHereditary :
    (CostRegionTree.normalizeHereditary rhoCutOrderBoundaryChild).pattern =
      .fvar "0" := by
  unfold CostRegionTree.normalizeHereditary rhoCutOrderBoundaryChild
  rw [CostRegionTree.reindexType_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer),
    CostRegionTree.reindexPattern_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer),
    CostRegionTree.reindexAvailable_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)]
  exact rhoCutOrderBaseRedexTree_normalizeHereditary

/-- Any closed wrapped rho node with two drop parameters whose hereditary
values are `0` and `a` chooses the same semantic-key representative.  The
parameter origins may be source variables or opposite-colour boundaries. -/
theorem normalizeHereditary_parallelDrops_zero_a
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT .wrapped targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT .wrapped
      targetFree node.boundaryTable)
    (zeroName aName : String)
    (skeleton : node.skeleton.1 =
      .collection .hashBag
        [.apply "PDrop" [.fvar zeroName],
          .apply "PDrop" [.fvar aName]] none)
    (zeroValue : values.assignment node.boundaryTable zeroName = .fvar "0")
    (aValue : values.assignment node.boundaryTable aName = .fvar "a")
    (closed : node.targetBound = []) :
    (CostStaticRegionNode.normalizeHereditary node values).1 =
      rhoCutOrderRightPattern := by
  let packed := node.semanticAtomEnvironment values
  let inventory := packed.1
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  have zeroMembership : zeroName ∈ node.skeleton.1.freeFvarNames := by
    rw [skeleton]
    simp [Pattern.freeFvarNames]
  have aMembership : aName ∈ node.skeleton.1.freeFvarNames := by
    rw [skeleton]
    simp [Pattern.freeFvarNames]
  obtain ⟨zeroOccurrence, zeroOccurrenceName⟩ :=
    node.skeleton_fvar_covered zeroName zeroMembership
  obtain ⟨aOccurrence, aOccurrenceName⟩ :=
    node.skeleton_fvar_covered aName aMembership
  obtain ⟨zeroSlot, zeroSelectedAtOccurrence⟩ := Option.isSome_iff_exists.mp
    (environment.slotOfName?_isSome_of_occurrence zeroOccurrence)
  obtain ⟨aSlot, aSelectedAtOccurrence⟩ := Option.isSome_iff_exists.mp
    (environment.slotOfName?_isSome_of_occurrence aOccurrence)
  have zeroSelected : environment.slotOfName? zeroName = some zeroSlot := by
    simpa [zeroOccurrenceName] using zeroSelectedAtOccurrence
  have aSelected : environment.slotOfName? aName = some aSlot := by
    simpa [aOccurrenceName] using aSelectedAtOccurrence
  have reifiedFrame : (node.reifiedSourceFrame environment).1 =
      .collection .hashBag
        [.apply rhoReflectivePresentation.dropConstructor
            [.fvar (environment.atomName zeroSlot)],
          .apply rhoReflectivePresentation.dropConstructor
            [.fvar (environment.atomName aSlot)]] none := by
    rw [node.reifiedSourceFrame_pattern]
    calc
      environment.reify node.skeleton.1 =
          environment.reify
            (.collection .hashBag
              [.apply "PDrop" [.fvar zeroName],
                .apply "PDrop" [.fvar aName]] none) :=
        congrArg environment.reify skeleton
      _ = _ := by
        simp [CostStaticAtomEnvironment.reify,
          CostStaticAtomEnvironment.reifyName, zeroSelected, aSelected,
          rhoReflectivePresentation]
  have zeroNormal : (environment.atomValue zeroSlot).key.normal =
      .fvar "0" := by
    calc
      (environment.atomValue zeroSlot).key.normal =
          values.assignment node.boundaryTable zeroOccurrence.name :=
        environment.atomValue_normal_eq_of_slotOfName?_eq_some zeroOccurrence
          zeroSlot zeroSelectedAtOccurrence
      _ = .fvar "0" := by simpa [zeroOccurrenceName] using zeroValue
  have aNormal : (environment.atomValue aSlot).key.normal = .fvar "a" := by
    calc
      (environment.atomValue aSlot).key.normal =
          values.assignment node.boundaryTable aOccurrence.name :=
        environment.atomValue_normal_eq_of_slotOfName?_eq_some aOccurrence
          aSlot aSelectedAtOccurrence
      _ = .fvar "a" := by simpa [aOccurrenceName] using aValue
  have ordered : patternCode
        (.apply (costWrappedConstructorName
          rhoReflectivePresentation.dropConstructor) [.fvar "0"]) ≤
      patternCode
        (.apply (costWrappedConstructorName
          rhoReflectivePresentation.dropConstructor) [.fvar "a"]) := by
    exact (patternCode_apply_single_fvar_lt_of_stringCode_lt
      (costWrappedConstructorName rhoReflectivePresentation.dropConstructor)
      (by decide)).le
  change (CostStaticRegionNode.normalizeHereditaryWithInventory
    node values inventory).1 = rhoCutOrderRightPattern
  rw [CostStaticRegionNode.normalizeHereditaryWithInventory_pattern]
  simpa [rhoCutOrderRightPattern, rhoCutOrderParallel,
    rhoCutOrderWrappedDrop, rhoReflectivePresentation] using
    (CostStaticRegionNode.normalizeHereditaryRawWithInventory_wrappedParallelTwoDrops
        node values inventory zeroSlot aSlot (.fvar "0") (.fvar "a")
        reifiedFrame zeroNormal aNormal ordered closed)

/-- Source-variable parameters are restored literally; only certified
foreign boundaries draw their value from the recursive child vector. -/
theorem hereditaryValues_assignment_sourceVariable
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (name : String) :
    values.assignment table (costRegionSourceVariableName name) = .fvar name := by
  simp [TypedCostRegionBoundaryTable.Values.assignment]

/-- The left outer frame receives the hereditary normal form of its unique
opposite-colour child at the exact proof-relevant boundary slot. -/
theorem rhoCutOrderLeftHereditaryValues_boundaryAssignment :
    (rhoCutOrderLeftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)).assignment
        rhoCutOrderLeftNode.boundaryTable
        (costRegionBoundaryVariableName
          rhoCutOrderBoundaryWitness.typed.boundary) =
      .fvar "0" := by
  change
    ((CostRegionBoundaryTrees.cons rhoCutOrderBoundaryChild
      CostRegionBoundaryTrees.nil).normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)).assignment
          (.cons rhoCutOrderBoundaryWitness.typed
            rhoCutOrderBoundaryWitness.content_eq .nil)
          (costRegionBoundaryVariableName
            rhoCutOrderBoundaryWitness.typed.boundary) =
      .fvar "0"
  simp only [CostRegionBoundaryTrees.normalizeValues]
  unfold TypedCostRegionBoundaryTable.Values.assignment
  rw [decodeCostRegionSourceVariableName_boundary]
  unfold TypedCostRegionBoundaryTable.Values.resolve
  simp only [if_pos]
  exact rhoCutOrderBoundaryChild_normalizeHereditary

/-- Proof-relevant semantic environment of the left endpoint after its
opposite-colour child has normalized. -/
noncomputable def rhoCutOrderLeftSemanticAtoms :=
  rhoCutOrderLeftNode.semanticAtomEnvironment
    (rhoCutOrderLeftChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer))

/-- Proof-relevant semantic environment of the direct right endpoint. -/
noncomputable def rhoCutOrderRightSemanticAtoms :=
  rhoCutOrderRightNode.semanticAtomEnvironment
    (rhoCutOrderRightChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer))

private theorem rhoCutOrderBoundaryWitness_sourceType :
    rhoCutOrderBoundaryWitness.typed.boundary.type = .base "Name" := by
  exact certifyCostRegionBoundary?_sourceType_eq
    rhoCutOrderBoundaryWitness_spec

private theorem rhoCutOrderBoundaryWitness_sourceSupport :
    rhoCutOrderBoundaryWitness.typed.boundary.support = [] := by
  simpa using
    (certifyCostRegionBoundary?_sourceSupport_eq
      (availableSource := []) rhoCutOrderBoundaryWitness_spec)

private theorem rhoCutOrderName_ne_interactingSort :
    "Name" ≠ rhoCIGSLT.theory.presentation.interactingSort.1.name := by
  change "Name" ≠ "Proc"
  decide

private theorem rhoCutOrderBoundaryWitness_mem_leftTable :
    rhoCutOrderBoundaryWitness.typed ∈
      rhoCutOrderLeftNode.boundaryTable.entries := by
  change rhoCutOrderBoundaryWitness.typed ∈
    (TypedCostRegionBoundaryTable.cons rhoCutOrderBoundaryWitness.typed
      rhoCutOrderBoundaryWitness.content_eq
      TypedCostRegionBoundaryTable.nil).entries
  exact List.mem_cons_self

/-- The left boundary occurrence and the direct right source occurrence of
`0` coalesce in the canonical cross-environment semantic quotient exactly
because all five typed key components agree.  In particular, the proof keeps
decoded source support distinct from restored target support until both are
shown empty for this closed rho boundary. -/
theorem rhoCutOrder_boundary_source_semanticAtom_coalescence :
    ∃ (leftSlot : Fin rhoCutOrderLeftSemanticAtoms.2.atomCount)
        (rightSlot : Fin rhoCutOrderRightSemanticAtoms.2.atomCount),
      rhoCutOrderLeftSemanticAtoms.2.slotOfName?
          (costRegionBoundaryVariableName
            rhoCutOrderBoundaryWitness.typed.boundary) = some leftSlot ∧
      rhoCutOrderRightSemanticAtoms.2.slotOfName?
          (costRegionSourceVariableName "0") = some rightSlot ∧
      (rhoCutOrderLeftSemanticAtoms.2.atomValue leftSlot).key.normal =
          .fvar "0" ∧
      (rhoCutOrderRightSemanticAtoms.2.atomValue rightSlot).key.normal =
          .fvar "0" ∧
      (rhoCutOrderLeftSemanticAtoms.2.atomValue leftSlot).key =
          (rhoCutOrderRightSemanticAtoms.2.atomValue rightSlot).key ∧
      (rhoCutOrderLeftSemanticAtoms.2.semanticKeyCospan
          rhoCutOrderRightSemanticAtoms.2).leftSlot leftSlot =
        (rhoCutOrderLeftSemanticAtoms.2.semanticKeyCospan
          rhoCutOrderRightSemanticAtoms.2).rightSlot rightSlot := by
  let leftEnvironment := rhoCutOrderLeftSemanticAtoms.2
  let rightEnvironment := rhoCutOrderRightSemanticAtoms.2
  have leftMembership :
      costRegionBoundaryVariableName
          rhoCutOrderBoundaryWitness.typed.boundary ∈
        rhoCutOrderLeftNode.skeleton.1.freeFvarNames := by
    rw [rhoCutOrderLeftNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  have rightMembership : costRegionSourceVariableName "0" ∈
      rhoCutOrderRightNode.skeleton.1.freeFvarNames := by
    rw [rhoCutOrderRightNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  obtain ⟨leftOccurrence, leftOccurrenceName⟩ :=
    rhoCutOrderLeftNode.skeleton_fvar_covered _ leftMembership
  obtain ⟨rightOccurrence, rightOccurrenceName⟩ :=
    rhoCutOrderRightNode.skeleton_fvar_covered _ rightMembership
  obtain ⟨leftSlot, leftSelectedAtOccurrence⟩ := Option.isSome_iff_exists.mp
    (leftEnvironment.slotOfName?_isSome_of_occurrence leftOccurrence)
  obtain ⟨rightSlot, rightSelectedAtOccurrence⟩ := Option.isSome_iff_exists.mp
    (rightEnvironment.slotOfName?_isSome_of_occurrence rightOccurrence)
  have leftSelected : leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName
        rhoCutOrderBoundaryWitness.typed.boundary) = some leftSlot := by
    simpa [leftOccurrenceName] using leftSelectedAtOccurrence
  have rightSelected : rightEnvironment.slotOfName?
      (costRegionSourceVariableName "0") = some rightSlot := by
    simpa [rightOccurrenceName] using rightSelectedAtOccurrence
  have leftSourceType :
      (leftEnvironment.atomValue leftSlot).key.sourceType = .base "Name" := by
    have selected :=
      leftEnvironment.sourceFreeContext_eq_atomValue_sourceType_of_slotOfName?_eq_some
        leftOccurrence leftSlot leftSelectedAtOccurrence
    have boundaryLookup :=
      rhoCutOrderLeftNode.boundaryTable.sourceFreeContext_boundaryVariable
        rhoCutOrderBoundaryWitness.typed
        rhoCutOrderBoundaryWitness_mem_leftTable
    have atomToBoundary :
        (leftEnvironment.atomValue leftSlot).key.sourceType =
          rhoCutOrderBoundaryWitness.typed.boundary.type :=
      Option.some.inj
        (selected.symm.trans (by
          simpa [leftOccurrenceName] using boundaryLookup))
    exact atomToBoundary.trans rhoCutOrderBoundaryWitness_sourceType
  have rightSourceContext :
      rhoCutOrderRightNode.boundaryTable.sourceFreeContext
          (costRegionSourceVariableName "0") = some (.base "Name") := by
    rw [TypedCostRegionBoundaryTable.sourceFreeContext_sourceVariable]
    simp [rhoCutOrderFree, WellSorted.FreeTypeContext.ofList,
      decodeCostStaticTypeExpr, costBaseSortName_ne_wrapped,
      rhoCutOrderName_ne_interactingSort]
  have rightSourceType :
      (rightEnvironment.atomValue rightSlot).key.sourceType = .base "Name" := by
    have selected :=
      rightEnvironment.sourceFreeContext_eq_atomValue_sourceType_of_slotOfName?_eq_some
        rightOccurrence rightSlot rightSelectedAtOccurrence
    exact Option.some.inj
      (selected.symm.trans (by
        simpa [rightOccurrenceName] using rightSourceContext))
  have leftSourceSupport :
      (leftEnvironment.atomValue leftSlot).key.sourceSupport = [] := by
    calc
      (leftEnvironment.atomValue leftSlot).key.sourceSupport =
          rhoCutOrderLeftNode.boundaryTable.atomSourceSupport
            leftOccurrence.name :=
        leftEnvironment.atomValue_sourceSupport_eq_atomSourceSupport_of_slotOfName?_eq_some
          leftOccurrence leftSlot leftSelectedAtOccurrence
      _ = rhoCutOrderLeftNode.boundaryTable.atomSourceSupport
            (costRegionBoundaryVariableName
              rhoCutOrderBoundaryWitness.typed.boundary) := by
        rw [leftOccurrenceName]
      _ = rhoCutOrderBoundaryWitness.typed.boundary.support := by
        exact rhoCutOrderLeftNode.boundaryTable.atomSourceSupport_boundaryVariable
          rhoCutOrderBoundaryWitness.typed
          rhoCutOrderBoundaryWitness_mem_leftTable
      _ = [] := rhoCutOrderBoundaryWitness_sourceSupport
  have rightSourceSupport :
      (rightEnvironment.atomValue rightSlot).key.sourceSupport = [] := by
    calc
      (rightEnvironment.atomValue rightSlot).key.sourceSupport =
          rhoCutOrderRightNode.boundaryTable.atomSourceSupport
            rightOccurrence.name :=
        rightEnvironment.atomValue_sourceSupport_eq_atomSourceSupport_of_slotOfName?_eq_some
          rightOccurrence rightSlot rightSelectedAtOccurrence
      _ = rhoCutOrderRightNode.boundaryTable.atomSourceSupport
            (costRegionSourceVariableName "0") := by
        rw [rightOccurrenceName]
      _ = [] := by simp
  have leftTargetType :
      (leftEnvironment.atomValue leftSlot).key.targetType =
        mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
          (.base "Name") := by
    have mapped :=
      leftEnvironment.mappedFreeContext_eq_atomValue_targetType_of_slotOfName?_eq_some
        leftOccurrence leftSlot leftSelectedAtOccurrence
    have targetLookup :
        rhoCutOrderLeftNode.boundaryTable.mappedFreeContext
            (costRegionBoundaryVariableName
              rhoCutOrderBoundaryWitness.typed.boundary) =
          some rhoCutOrderBoundaryWitness.typed.boundary.targetType := by
      simp [TypedCostRegionBoundaryTable.mappedFreeContext,
        decodeCostRegionSourceVariableName_boundary,
        rhoCutOrderLeftNode.boundaryTable.resolve_of_mem_entries
          rhoCutOrderBoundaryWitness.typed
          rhoCutOrderBoundaryWitness_mem_leftTable]
    have atomToBoundary :
        (leftEnvironment.atomValue leftSlot).key.targetType =
          rhoCutOrderBoundaryWitness.typed.boundary.targetType :=
      Option.some.inj
        (mapped.symm.trans (by
          simpa [leftOccurrenceName] using targetLookup))
    exact atomToBoundary.trans rhoCutOrderBoundaryWitness.targetType_eq
  have rightTargetContext :
      rhoCutOrderRightNode.boundaryTable.mappedFreeContext
          (costRegionSourceVariableName "0") =
        some (mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
          (.base "Name")) := by
    simp [TypedCostRegionBoundaryTable.mappedFreeContext,
      rhoCutOrderFree, WellSorted.FreeTypeContext.ofList,
      decodeCostStaticTypeExpr, costBaseSortName_ne_wrapped,
      rhoCutOrderName_ne_interactingSort]
  have rightTargetType :
      (rightEnvironment.atomValue rightSlot).key.targetType =
        mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
          (.base "Name") := by
    have mapped :=
      rightEnvironment.mappedFreeContext_eq_atomValue_targetType_of_slotOfName?_eq_some
        rightOccurrence rightSlot rightSelectedAtOccurrence
    exact Option.some.inj
      (mapped.symm.trans (by
        simpa [rightOccurrenceName] using rightTargetContext))
  have leftTargetSupport :
      (leftEnvironment.atomValue leftSlot).key.targetSupport = [] := by
    calc
      (leftEnvironment.atomValue leftSlot).key.targetSupport =
          rhoCutOrderLeftNode.boundaryTable.sourceSupport
            leftOccurrence.name :=
        leftEnvironment.atomValue_targetSupport_eq_sourceSupport_of_slotOfName?_eq_some
          leftOccurrence leftSlot leftSelectedAtOccurrence
      _ = rhoCutOrderLeftNode.boundaryTable.sourceSupport
            (costRegionBoundaryVariableName
              rhoCutOrderBoundaryWitness.typed.boundary) := by
        rw [leftOccurrenceName]
      _ = rhoCutOrderBoundaryWitness.typed.boundary.targetSupport := by
        exact rhoCutOrderLeftNode.boundaryTable.sourceSupport_boundaryVariable
          rhoCutOrderBoundaryWitness.typed
          rhoCutOrderBoundaryWitness_mem_leftTable
      _ = [] := rhoCutOrderBoundaryWitness.targetSupport_eq
  have rightTargetSupport :
      (rightEnvironment.atomValue rightSlot).key.targetSupport = [] := by
    calc
      (rightEnvironment.atomValue rightSlot).key.targetSupport =
          rhoCutOrderRightNode.boundaryTable.sourceSupport
            rightOccurrence.name :=
        rightEnvironment.atomValue_targetSupport_eq_sourceSupport_of_slotOfName?_eq_some
          rightOccurrence rightSlot rightSelectedAtOccurrence
      _ = rhoCutOrderRightNode.boundaryTable.sourceSupport
            (costRegionSourceVariableName "0") := by
        rw [rightOccurrenceName]
      _ = [] := by simp
  have leftNormal :
      (leftEnvironment.atomValue leftSlot).key.normal = .fvar "0" := by
    calc
      (leftEnvironment.atomValue leftSlot).key.normal =
          (rhoCutOrderLeftChildren.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer)).assignment
              rhoCutOrderLeftNode.boundaryTable leftOccurrence.name :=
        leftEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
          leftOccurrence leftSlot leftSelectedAtOccurrence
      _ = .fvar "0" := by
        simpa [leftOccurrenceName] using
          rhoCutOrderLeftHereditaryValues_boundaryAssignment
  have rightNormal :
      (rightEnvironment.atomValue rightSlot).key.normal = .fvar "0" := by
    calc
      (rightEnvironment.atomValue rightSlot).key.normal =
          (rhoCutOrderRightChildren.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer)).assignment
              rhoCutOrderRightNode.boundaryTable rightOccurrence.name :=
        rightEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
          rightOccurrence rightSlot rightSelectedAtOccurrence
      _ = .fvar "0" := by
        simpa [rightOccurrenceName] using
          (hereditaryValues_assignment_sourceVariable
            rhoCutOrderRightNode.boundaryTable
            (rhoCutOrderRightChildren.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer)) "0")
  have keyEquality :
      (leftEnvironment.atomValue leftSlot).key =
        (rightEnvironment.atomValue rightSlot).key :=
    CostStaticAtomKey.ext_components
      (leftSourceType.trans rightSourceType.symm)
      (leftSourceSupport.trans rightSourceSupport.symm)
      (leftTargetType.trans rightTargetType.symm)
      (leftTargetSupport.trans rightTargetSupport.symm)
      (leftNormal.trans rightNormal.symm)
  refine ⟨leftSlot, rightSlot, ?_, ?_, leftNormal, rightNormal, keyEquality, ?_⟩
  · exact leftSelected
  · exact rightSelected
  · exact (leftEnvironment.semanticKeyCospan rightEnvironment).crossExtensional
      leftSlot rightSlot |>.mpr keyEquality

/-- The unchanged source occurrence `a` selects equal complete semantic keys
at both endpoints.  This is the reflexive companion to the boundary/source
coalescence above and keeps source-name identity out of the canonical frame
comparison itself. -/
theorem rhoCutOrder_sourceA_semanticAtom_coalescence :
    ∃ (leftSlot : Fin rhoCutOrderLeftSemanticAtoms.2.atomCount)
        (rightSlot : Fin rhoCutOrderRightSemanticAtoms.2.atomCount),
      rhoCutOrderLeftSemanticAtoms.2.slotOfName?
          (costRegionSourceVariableName "a") = some leftSlot ∧
      rhoCutOrderRightSemanticAtoms.2.slotOfName?
          (costRegionSourceVariableName "a") = some rightSlot ∧
      (rhoCutOrderLeftSemanticAtoms.2.atomValue leftSlot).key.normal =
          .fvar "a" ∧
      (rhoCutOrderRightSemanticAtoms.2.atomValue rightSlot).key.normal =
          .fvar "a" ∧
      (rhoCutOrderLeftSemanticAtoms.2.atomValue leftSlot).key =
          (rhoCutOrderRightSemanticAtoms.2.atomValue rightSlot).key ∧
      (rhoCutOrderLeftSemanticAtoms.2.semanticKeyCospan
          rhoCutOrderRightSemanticAtoms.2).leftSlot leftSlot =
        (rhoCutOrderLeftSemanticAtoms.2.semanticKeyCospan
          rhoCutOrderRightSemanticAtoms.2).rightSlot rightSlot := by
  let leftEnvironment := rhoCutOrderLeftSemanticAtoms.2
  let rightEnvironment := rhoCutOrderRightSemanticAtoms.2
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  have leftMembership : costRegionSourceVariableName "a" ∈
      rhoCutOrderLeftNode.skeleton.1.freeFvarNames := by
    rw [rhoCutOrderLeftNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  have rightMembership : costRegionSourceVariableName "a" ∈
      rhoCutOrderRightNode.skeleton.1.freeFvarNames := by
    rw [rhoCutOrderRightNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  obtain ⟨leftOccurrence, leftName⟩ :=
    rhoCutOrderLeftNode.skeleton_fvar_covered _ leftMembership
  obtain ⟨rightOccurrence, rightName⟩ :=
    rhoCutOrderRightNode.skeleton_fvar_covered _ rightMembership
  obtain ⟨leftSlot, leftSelectedAtOccurrence⟩ :=
    Option.isSome_iff_exists.mp
      (leftEnvironment.slotOfName?_isSome_of_occurrence leftOccurrence)
  obtain ⟨rightSlot, rightSelectedAtOccurrence⟩ :=
    Option.isSome_iff_exists.mp
      (rightEnvironment.slotOfName?_isSome_of_occurrence rightOccurrence)
  have leftSelected : leftEnvironment.slotOfName?
      (costRegionSourceVariableName "a") = some leftSlot := by
    simpa [leftName] using leftSelectedAtOccurrence
  have rightSelected : rightEnvironment.slotOfName?
      (costRegionSourceVariableName "a") = some rightSlot := by
    simpa [rightName] using rightSelectedAtOccurrence
  have keyEquality : (leftEnvironment.atomValue leftSlot).key =
      (rightEnvironment.atomValue rightSlot).key :=
    CostStaticAtomEnvironment.sourceVariable_key_eq leftEnvironment
      rightEnvironment "a" leftOccurrence rightOccurrence leftName rightName
      leftSlot rightSlot leftSelectedAtOccurrence rightSelectedAtOccurrence
  have leftNormal : (leftEnvironment.atomValue leftSlot).key.normal =
      .fvar "a" := by
    calc
      (leftEnvironment.atomValue leftSlot).key.normal =
          (rhoCutOrderLeftChildren.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer)).assignment
              rhoCutOrderLeftNode.boundaryTable leftOccurrence.name :=
        leftEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
          leftOccurrence leftSlot leftSelectedAtOccurrence
      _ = .fvar "a" := by
        simpa [leftName] using
          (hereditaryValues_assignment_sourceVariable
            rhoCutOrderLeftNode.boundaryTable
            (rhoCutOrderLeftChildren.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer)) "a")
  have rightNormal : (rightEnvironment.atomValue rightSlot).key.normal =
      .fvar "a" := by
    calc
      (rightEnvironment.atomValue rightSlot).key.normal =
          (rhoCutOrderRightChildren.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer)).assignment
              rhoCutOrderRightNode.boundaryTable rightOccurrence.name :=
        rightEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
          rightOccurrence rightSlot rightSelectedAtOccurrence
      _ = .fvar "a" := by
        simpa [rightName] using
          (hereditaryValues_assignment_sourceVariable
            rhoCutOrderRightNode.boundaryTable
            (rhoCutOrderRightChildren.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer)) "a")
  refine ⟨leftSlot, rightSlot, leftSelected, rightSelected, leftNormal,
    rightNormal, keyEquality, ?_⟩
  exact cospan.crossExtensional leftSlot rightSlot |>.mpr keyEquality

/-- The two selected wrapped source frames become definitionally identical
after their endpoint parameter occurrences are mapped into the common
semantic namespace.  The root-changing Quote/Drop edge has disappeared only
because its normalized boundary value shares the full key of source `0`;
the unchanged source `a` is aligned by the generic source-variable law. -/
theorem rhoCutOrder_commonSemanticFrames_eq :
    let cospan := rhoCutOrderLeftSemanticAtoms.2.semanticKeyCospan
      rhoCutOrderRightSemanticAtoms.2
    cospan.reifyLeft rhoCutOrderLeftSemanticAtoms.2.slotOfName?
        rhoCutOrderLeftNode.skeleton.1 =
      cospan.reifyRight rhoCutOrderRightSemanticAtoms.2.slotOfName?
        rhoCutOrderRightNode.skeleton.1 := by
  let leftEnvironment := rhoCutOrderLeftSemanticAtoms.2
  let rightEnvironment := rhoCutOrderRightSemanticAtoms.2
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  obtain ⟨leftZeroSlot, rightZeroSlot, leftZeroSelected,
      rightZeroSelected, leftZeroNormal, rightZeroNormal, zeroKeyEquality,
      zeroLegEquality⟩ :=
    rhoCutOrder_boundary_source_semanticAtom_coalescence
  change leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName
        rhoCutOrderBoundaryWitness.typed.boundary) = some leftZeroSlot
    at leftZeroSelected
  change rightEnvironment.slotOfName?
      (costRegionSourceVariableName "0") = some rightZeroSlot
    at rightZeroSelected
  change (leftEnvironment.atomValue leftZeroSlot).key =
      (rightEnvironment.atomValue rightZeroSlot).key at zeroKeyEquality
  change cospan.leftSlot leftZeroSlot = cospan.rightSlot rightZeroSlot
    at zeroLegEquality
  have leftAMembership : costRegionSourceVariableName "a" ∈
      rhoCutOrderLeftNode.skeleton.1.freeFvarNames := by
    rw [rhoCutOrderLeftNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  have rightAMembership : costRegionSourceVariableName "a" ∈
      rhoCutOrderRightNode.skeleton.1.freeFvarNames := by
    rw [rhoCutOrderRightNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  obtain ⟨leftAOccurrence, leftAName⟩ :=
    rhoCutOrderLeftNode.skeleton_fvar_covered _ leftAMembership
  obtain ⟨rightAOccurrence, rightAName⟩ :=
    rhoCutOrderRightNode.skeleton_fvar_covered _ rightAMembership
  obtain ⟨leftASlot, leftASelectedAtOccurrence⟩ :=
    Option.isSome_iff_exists.mp
      (leftEnvironment.slotOfName?_isSome_of_occurrence leftAOccurrence)
  obtain ⟨rightASlot, rightASelectedAtOccurrence⟩ :=
    Option.isSome_iff_exists.mp
      (rightEnvironment.slotOfName?_isSome_of_occurrence rightAOccurrence)
  have leftASelected : leftEnvironment.slotOfName?
      (costRegionSourceVariableName "a") = some leftASlot := by
    simpa [leftAName] using leftASelectedAtOccurrence
  have rightASelected : rightEnvironment.slotOfName?
      (costRegionSourceVariableName "a") = some rightASlot := by
    simpa [rightAName] using rightASelectedAtOccurrence
  have aKeyEquality :
      (leftEnvironment.atomValue leftASlot).key =
        (rightEnvironment.atomValue rightASlot).key :=
    CostStaticAtomEnvironment.sourceVariable_key_eq leftEnvironment
      rightEnvironment "a" leftAOccurrence rightAOccurrence leftAName
      rightAName leftASlot rightASlot leftASelectedAtOccurrence
      rightASelectedAtOccurrence
  have aLegEquality : cospan.leftSlot leftASlot =
      cospan.rightSlot rightASlot :=
    (cospan.crossExtensional leftASlot rightASlot).mpr aKeyEquality
  change cospan.reifyLeft leftEnvironment.slotOfName?
      rhoCutOrderLeftNode.skeleton.1 =
    cospan.reifyRight rightEnvironment.slotOfName?
      rhoCutOrderRightNode.skeleton.1
  calc
    cospan.reifyLeft leftEnvironment.slotOfName?
        rhoCutOrderLeftNode.skeleton.1 =
      cospan.reifyLeft leftEnvironment.slotOfName?
        (.collection .hashBag
          [.apply "PDrop"
              [.fvar (costRegionBoundaryVariableName
                rhoCutOrderBoundaryWitness.typed.boundary)],
            .apply "PDrop"
              [.fvar (costRegionSourceVariableName "a")]] none) :=
      congrArg (cospan.reifyLeft leftEnvironment.slotOfName?)
        rhoCutOrderLeftNode_skeleton_pattern
    _ = cospan.reifyRight rightEnvironment.slotOfName?
        (.collection .hashBag
          [.apply "PDrop" [.fvar (costRegionSourceVariableName "0")],
            .apply "PDrop"
              [.fvar (costRegionSourceVariableName "a")]] none) := by
      simp [CostStaticAtomKeyCospan.reifyLeft,
        CostStaticAtomKeyCospan.reifyRight,
        CostStaticAtomKeyCospan.reifyWith,
        leftZeroSelected, rightZeroSelected, leftASelected, rightASelected,
        zeroLegEquality, aLegEquality]
    _ = cospan.reifyRight rightEnvironment.slotOfName?
        rhoCutOrderRightNode.skeleton.1 :=
      (congrArg (cospan.reifyRight rightEnvironment.slotOfName?)
        rhoCutOrderRightNode_skeleton_pattern).symm

/-- The same common semantic frame equality after mapping both selected
outer frames into their shared wrapped Cost stratum.  Semantic-atom renaming
commutes with constructor colouring, while the closed nodes require no
ambient binder insertion. -/
theorem rhoCutOrder_commonMappedSemanticFrames_eq :
    let cospan := rhoCutOrderLeftSemanticAtoms.2.semanticKeyCospan
      rhoCutOrderRightSemanticAtoms.2
    cospan.reifyLeft rhoCutOrderLeftSemanticAtoms.2.slotOfName?
        rhoCutOrderLeftNode.mappedThickenedSkeleton.1 =
      cospan.reifyRight rhoCutOrderRightSemanticAtoms.2.slotOfName?
        rhoCutOrderRightNode.mappedThickenedSkeleton.1 := by
  let leftEnvironment := rhoCutOrderLeftSemanticAtoms.2
  let rightEnvironment := rhoCutOrderRightSemanticAtoms.2
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  change cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot
      rhoCutOrderLeftNode.mappedThickenedSkeleton.1 =
    cospan.reifyWith rightEnvironment.slotOfName? cospan.rightSlot
      rhoCutOrderRightNode.mappedThickenedSkeleton.1
  rw [rhoCutOrderLeftNode.mappedThickenedSkeleton_pattern,
    rhoCutOrderRightNode.mappedThickenedSkeleton_pattern]
  rw [CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
      rhoCutOrderLeftNode.thinning rfl,
    CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
      rhoCutOrderRightNode.thinning rfl]
  rw [cospan.reifyWith_mapPattern, cospan.reifyWith_mapPattern]
  exact congrArg (mapPattern (CostStaticColor.symbols rhoCIGSLT .wrapped))
    rhoCutOrder_commonSemanticFrames_eq

/-- The mapped common-frame equality stated with the canonical environment
projection used by the reusable root-bridge constructor. -/
theorem rhoCutOrder_commonMappedSemanticFrames_eq_ofInventory :
    let leftValues := rhoCutOrderLeftChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer)
    let rightValues := rhoCutOrderRightChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer)
    let leftInventory :=
      (rhoCutOrderLeftNode.semanticAtomEnvironment leftValues).1
    let rightInventory :=
      (rhoCutOrderRightNode.semanticAtomEnvironment rightValues).1
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
    let rightEnvironment :=
      CostStaticAtomEnvironment.ofInventory rightInventory
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot
        rhoCutOrderLeftNode.mappedThickenedSkeleton.1 =
      cospan.reifyWith rightEnvironment.slotOfName? cospan.rightSlot
        rhoCutOrderRightNode.mappedThickenedSkeleton.1 := by
  let leftValues := rhoCutOrderLeftChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rhoCutOrderRightChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (rhoCutOrderLeftNode.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rhoCutOrderRightNode.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  have leftProjection : rhoCutOrderLeftSemanticAtoms.2 = leftEnvironment := by
    exact Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticAtomEnvironment_snd_eq_ofInventory_fst
      rhoCutOrderLeftNode leftValues
  have rightProjection : rhoCutOrderRightSemanticAtoms.2 = rightEnvironment := by
    exact Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticAtomEnvironment_snd_eq_ofInventory_fst
      rhoCutOrderRightNode rightValues
  have commonMapped := rhoCutOrder_commonMappedSemanticFrames_eq
  rw [leftProjection, rightProjection] at commonMapped
  exact commonMapped

/-- The two mixed-colour endpoint frames also have one representative under
the selected wrapped declaration at the common semantic apex.  This is the
exact premise consumed by the keyed-frame root bridge; it is derived from
the pre-canonical frame square, not from equality of evaluator outputs. -/
theorem rhoCutOrder_commonKeyedSemanticFrames_eq :
    let leftValues := rhoCutOrderLeftChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer)
    let rightValues := rhoCutOrderRightChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer)
    let leftInventory :=
      (rhoCutOrderLeftNode.semanticAtomEnvironment leftValues).1
    let rightInventory :=
      (rhoCutOrderRightNode.semanticAtomEnvironment rightValues).1
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
    let rightEnvironment :=
      CostStaticAtomEnvironment.ofInventory rightInventory
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
      rhoReflectivePresentation
    canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        declaration rhoCutOrderLeftNode.targetBound.length
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (rhoCutOrderLeftNode.reifyTargetFrame leftEnvironment)) =
      canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        declaration rhoCutOrderLeftNode.targetBound.length
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rhoCutOrderRightNode.reifyTargetFrame rightEnvironment)) := by
  let leftValues := rhoCutOrderLeftChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rhoCutOrderRightChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (rhoCutOrderLeftNode.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rhoCutOrderRightNode.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
    rhoReflectivePresentation
  have commonMapped := rhoCutOrder_commonMappedSemanticFrames_eq_ofInventory
  have leftFrameFactor :=
    leftEnvironment.reifyWith_reifyTargetFrame_eq_mappedThickenedSkeleton
      rhoCutOrderLeftNode cospan cospan.leftSlot
  have rightFrameFactor :=
    rightEnvironment.reifyWith_reifyTargetFrame_eq_mappedThickenedSkeleton
      rhoCutOrderRightNode cospan cospan.rightSlot
  have commonFrames :
      cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (rhoCutOrderLeftNode.reifyTargetFrame leftEnvironment) =
        cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rhoCutOrderRightNode.reifyTargetFrame rightEnvironment) :=
    leftFrameFactor.trans (commonMapped.trans rightFrameFactor.symm)
  exact congrArg
    (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
      declaration rhoCutOrderLeftNode.targetBound.length) commonFrames

/-- The selected canonical frames themselves meet in the common semantic
namespace before either endpoint restores atom values.  Thus equality of the
hereditary evaluator results is obtained from the canonical atom square, not
used as an assumption when constructing that square. -/
theorem rhoCutOrder_commonCanonicalSemanticFrames_eq :
    let leftInventory := rhoCutOrderLeftSemanticAtoms.1
    let rightInventory := rhoCutOrderRightSemanticAtoms.1
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
    let rightEnvironment :=
      CostStaticAtomEnvironment.ofInventory rightInventory
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (rhoCutOrderLeftNode.canonicalizeReifiedTargetFrame leftEnvironment
          (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
            rhoReflectivePresentation)) =
      cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rhoCutOrderRightNode.canonicalizeReifiedTargetFrame rightEnvironment
          (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
            rhoReflectivePresentation)) := by
  let leftValues := rhoCutOrderLeftChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rhoCutOrderRightChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory := rhoCutOrderLeftSemanticAtoms.1
  let rightInventory := rhoCutOrderRightSemanticAtoms.1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  have leftProjection : rhoCutOrderLeftSemanticAtoms.2 = leftEnvironment := by
    exact Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticAtomEnvironment_snd_eq_ofInventory_fst
      rhoCutOrderLeftNode leftValues
  have rightProjection : rhoCutOrderRightSemanticAtoms.2 = rightEnvironment := by
    exact Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticAtomEnvironment_snd_eq_ofInventory_fst
      rhoCutOrderRightNode rightValues
  have zeroCoalescence :=
    rhoCutOrder_boundary_source_semanticAtom_coalescence
  rw [leftProjection, rightProjection] at zeroCoalescence
  obtain ⟨leftZeroSlot, rightZeroSlot, leftZeroSelected,
      rightZeroSelected, leftZeroNormal, rightZeroNormal, zeroKeyEquality,
      zeroLegEquality⟩ :=
    zeroCoalescence
  have aCoalescence := rhoCutOrder_sourceA_semanticAtom_coalescence
  rw [leftProjection, rightProjection] at aCoalescence
  obtain ⟨leftASlot, rightASlot, leftASelected, rightASelected, leftANormal,
      rightANormal, aKeyEquality, aLegEquality⟩ :=
    aCoalescence
  change leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName
        rhoCutOrderBoundaryWitness.typed.boundary) = some leftZeroSlot
    at leftZeroSelected
  change rightEnvironment.slotOfName?
      (costRegionSourceVariableName "0") = some rightZeroSlot
    at rightZeroSelected
  change (leftEnvironment.atomValue leftZeroSlot).key.normal = .fvar "0"
    at leftZeroNormal
  change (rightEnvironment.atomValue rightZeroSlot).key.normal = .fvar "0"
    at rightZeroNormal
  change cospan.leftSlot leftZeroSlot = cospan.rightSlot rightZeroSlot
    at zeroLegEquality
  change leftEnvironment.slotOfName?
      (costRegionSourceVariableName "a") = some leftASlot at leftASelected
  change rightEnvironment.slotOfName?
      (costRegionSourceVariableName "a") = some rightASlot at rightASelected
  change (leftEnvironment.atomValue leftASlot).key.normal = .fvar "a"
    at leftANormal
  change (rightEnvironment.atomValue rightASlot).key.normal = .fvar "a"
    at rightANormal
  change cospan.leftSlot leftASlot = cospan.rightSlot rightASlot
    at aLegEquality
  have leftReifiedFrame :
      (rhoCutOrderLeftNode.reifiedSourceFrame leftEnvironment).1 =
        .collection .hashBag
          [.apply rhoReflectivePresentation.dropConstructor
              [.fvar (leftEnvironment.atomName leftZeroSlot)],
            .apply rhoReflectivePresentation.dropConstructor
              [.fvar (leftEnvironment.atomName leftASlot)]] none := by
    rw [rhoCutOrderLeftNode.reifiedSourceFrame_pattern]
    calc
      leftEnvironment.reify rhoCutOrderLeftNode.skeleton.1 =
          leftEnvironment.reify
            (.collection .hashBag
              [.apply "PDrop"
                  [.fvar (costRegionBoundaryVariableName
                    rhoCutOrderBoundaryWitness.typed.boundary)],
                .apply "PDrop"
                  [.fvar (costRegionSourceVariableName "a")]] none) :=
        congrArg leftEnvironment.reify rhoCutOrderLeftNode_skeleton_pattern
      _ = _ := by
        simp [CostStaticAtomEnvironment.reify,
          CostStaticAtomEnvironment.reifyName, leftZeroSelected, leftASelected,
          rhoReflectivePresentation]
  have rightReifiedFrame :
      (rhoCutOrderRightNode.reifiedSourceFrame rightEnvironment).1 =
        .collection .hashBag
          [.apply rhoReflectivePresentation.dropConstructor
              [.fvar (rightEnvironment.atomName rightZeroSlot)],
            .apply rhoReflectivePresentation.dropConstructor
              [.fvar (rightEnvironment.atomName rightASlot)]] none := by
    rw [rhoCutOrderRightNode.reifiedSourceFrame_pattern]
    calc
      rightEnvironment.reify rhoCutOrderRightNode.skeleton.1 =
          rightEnvironment.reify
            (.collection .hashBag
              [.apply "PDrop" [.fvar (costRegionSourceVariableName "0")],
                .apply "PDrop"
                  [.fvar (costRegionSourceVariableName "a")]] none) :=
        congrArg rightEnvironment.reify rhoCutOrderRightNode_skeleton_pattern
      _ = _ := by
        simp [CostStaticAtomEnvironment.reify,
          CostStaticAtomEnvironment.reifyName, rightZeroSelected,
          rightASelected, rhoReflectivePresentation]
  have ordered : patternCode
        (.apply (costWrappedConstructorName
          rhoReflectivePresentation.dropConstructor) [.fvar "0"]) ≤
      patternCode
        (.apply (costWrappedConstructorName
          rhoReflectivePresentation.dropConstructor) [.fvar "a"]) := by
    exact (patternCode_apply_single_fvar_lt_of_stringCode_lt
      (costWrappedConstructorName rhoReflectivePresentation.dropConstructor)
      (by decide)).le
  have leftCanonical :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionNode.canonicalizeReifiedTargetFrame_wrappedParallelTwoDrops
      rhoCutOrderLeftNode leftValues leftInventory leftZeroSlot leftASlot
        (.fvar "0") (.fvar "a") leftReifiedFrame leftZeroNormal leftANormal
        ordered (by rfl)
  have rightCanonical :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionNode.canonicalizeReifiedTargetFrame_wrappedParallelTwoDrops
      rhoCutOrderRightNode rightValues rightInventory rightZeroSlot rightASlot
        (.fvar "0") (.fvar "a") rightReifiedFrame rightZeroNormal rightANormal
        ordered (by rfl)
  have leftZeroAtomSelected :
      leftEnvironment.lookupAtom?
          ((CostStaticAtomEnvironment.ofInventory leftInventory).atomName
            leftZeroSlot) = some leftZeroSlot := by
    change leftEnvironment.lookupAtom?
        (leftEnvironment.atomName leftZeroSlot) = some leftZeroSlot
    exact leftEnvironment.lookupAtom?_atomName leftZeroSlot
  have rightZeroAtomSelected :
      rightEnvironment.lookupAtom?
          ((CostStaticAtomEnvironment.ofInventory rightInventory).atomName
            rightZeroSlot) = some rightZeroSlot := by
    change rightEnvironment.lookupAtom?
        (rightEnvironment.atomName rightZeroSlot) = some rightZeroSlot
    exact rightEnvironment.lookupAtom?_atomName rightZeroSlot
  have leftAAtomSelected :
      leftEnvironment.lookupAtom?
          ((CostStaticAtomEnvironment.ofInventory leftInventory).atomName
            leftASlot) = some leftASlot := by
    change leftEnvironment.lookupAtom?
        (leftEnvironment.atomName leftASlot) = some leftASlot
    exact leftEnvironment.lookupAtom?_atomName leftASlot
  have rightAAtomSelected :
      rightEnvironment.lookupAtom?
          ((CostStaticAtomEnvironment.ofInventory rightInventory).atomName
            rightASlot) = some rightASlot := by
    change rightEnvironment.lookupAtom?
        (rightEnvironment.atomName rightASlot) = some rightASlot
    exact rightEnvironment.lookupAtom?_atomName rightASlot
  change cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
      (rhoCutOrderLeftNode.canonicalizeReifiedTargetFrame leftEnvironment
        (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
          rhoReflectivePresentation)) =
    cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
      (rhoCutOrderRightNode.canonicalizeReifiedTargetFrame rightEnvironment
        (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
          rhoReflectivePresentation))
  rw [leftCanonical, rightCanonical]
  simp only [CostStaticAtomKeyCospan.reifyWith, List.map,
    leftZeroAtomSelected,
    rightZeroAtomSelected, leftAAtomSelected, rightAAtomSelected,
    zeroLegEquality, aLegEquality]

/-- The same canonical-frame equality derived by the general atom-covered
semantic-cospan naturality law.  The proof uses only the pre-canonical common
frame and never computes either endpoint's sort order. -/
theorem rhoCutOrder_commonCanonicalSemanticFrames_eq_byNaturality :
    let leftInventory := rhoCutOrderLeftSemanticAtoms.1
    let rightInventory := rhoCutOrderRightSemanticAtoms.1
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
    let rightEnvironment :=
      CostStaticAtomEnvironment.ofInventory rightInventory
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (rhoCutOrderLeftNode.canonicalizeReifiedTargetFrame leftEnvironment
          (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
            rhoReflectivePresentation)) =
      cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rhoCutOrderRightNode.canonicalizeReifiedTargetFrame rightEnvironment
          (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
            rhoReflectivePresentation)) := by
  let leftValues := rhoCutOrderLeftChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rhoCutOrderRightChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory := rhoCutOrderLeftSemanticAtoms.1
  let rightInventory := rhoCutOrderRightSemanticAtoms.1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  have leftProjection : rhoCutOrderLeftSemanticAtoms.2 = leftEnvironment := by
    exact Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticAtomEnvironment_snd_eq_ofInventory_fst
      rhoCutOrderLeftNode leftValues
  have rightProjection : rhoCutOrderRightSemanticAtoms.2 = rightEnvironment := by
    exact Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticAtomEnvironment_snd_eq_ofInventory_fst
      rhoCutOrderRightNode rightValues
  have commonMappedRaw := rhoCutOrder_commonMappedSemanticFrames_eq
  rw [leftProjection, rightProjection] at commonMappedRaw
  have commonMapped :
      cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot
          rhoCutOrderLeftNode.mappedThickenedSkeleton.1 =
        cospan.reifyWith rightEnvironment.slotOfName? cospan.rightSlot
          rhoCutOrderRightNode.mappedThickenedSkeleton.1 := by
    exact commonMappedRaw
  have leftFrameFactor :=
    leftEnvironment.reifyWith_reifyTargetFrame_eq_mappedThickenedSkeleton
      rhoCutOrderLeftNode cospan cospan.leftSlot
  have rightFrameFactor :=
    rightEnvironment.reifyWith_reifyTargetFrame_eq_mappedThickenedSkeleton
      rhoCutOrderRightNode cospan cospan.rightSlot
  have commonFrames :
      cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (rhoCutOrderLeftNode.reifyTargetFrame leftEnvironment) =
        cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rhoCutOrderRightNode.reifyTargetFrame rightEnvironment) :=
    leftFrameFactor.trans (commonMapped.trans rightFrameFactor.symm)
  have leftCovered : leftEnvironment.Covers
      (rhoCutOrderLeftNode.reifyTargetFrame leftEnvironment) := by
    intro name membership
    exact rhoCutOrderLeftNode.reifyTargetFrame_atomCovered leftEnvironment
      name membership
  have rightCovered : rightEnvironment.Covers
      (rhoCutOrderRightNode.reifyTargetFrame rightEnvironment) := by
    intro name membership
    exact rhoCutOrderRightNode.reifyTargetFrame_atomCovered rightEnvironment
      name membership
  change cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (CostStaticRegionNode.semanticPatternKeyAt leftEnvironment)
        (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
          rhoReflectivePresentation)
        rhoCutOrderLeftNode.targetBound.length
        (rhoCutOrderLeftNode.reifyTargetFrame leftEnvironment)) =
    cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (CostStaticRegionNode.semanticPatternKeyAt rightEnvironment)
        (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
          rhoReflectivePresentation)
        rhoCutOrderRightNode.targetBound.length
        (rhoCutOrderRightNode.reifyTargetFrame rightEnvironment))
  rw [show rhoCutOrderLeftNode.targetBound.length = 0 by rfl,
    show rhoCutOrderRightNode.targetBound.length = 0 by rfl]
  exact leftEnvironment.commonCanonicalFrames_eq_of_commonFrames_eq
    rightEnvironment cospan
    (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
      rhoReflectivePresentation)
    0 (rhoCutOrderLeftNode.reifyTargetFrame leftEnvironment)
    (rhoCutOrderRightNode.reifyTargetFrame rightEnvironment)
    leftCovered rightCovered commonFrames

/-- The canonical mixed-colour frames also agree at their restored compact
meaning in the independently constructed common atom namespace.  This is the
weaker, tie-tolerant premise used by the production root bridge. -/
theorem rhoCutOrder_commonRestoredCanonicalSemanticFrames_eq :
    let leftValues := rhoCutOrderLeftChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer)
    let rightValues := rhoCutOrderRightChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer)
    let leftInventory :=
      (rhoCutOrderLeftNode.semanticAtomEnvironment leftValues).1
    let rightInventory :=
      (rhoCutOrderRightNode.semanticAtomEnvironment rightValues).1
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
    let rightEnvironment :=
      CostStaticAtomEnvironment.ofInventory rightInventory
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    ReflectiveContextSupport.substituteAt
      rhoCIGSLT.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment
        rhoCutOrderLeftNode.targetBound.length
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (rhoCutOrderLeftNode.canonicalizeReifiedTargetFrame leftEnvironment
            (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
              rhoReflectivePresentation))) =
      ReflectiveContextSupport.substituteAt
        rhoCIGSLT.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment
        rhoCutOrderLeftNode.targetBound.length
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rhoCutOrderRightNode.canonicalizeReifiedTargetFrame rightEnvironment
            (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
              rhoReflectivePresentation))) := by
  let leftValues := rhoCutOrderLeftChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rhoCutOrderRightChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (rhoCutOrderLeftNode.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rhoCutOrderRightNode.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  have frames := rhoCutOrder_commonCanonicalSemanticFrames_eq_byNaturality
  change cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
      (rhoCutOrderLeftNode.canonicalizeReifiedTargetFrame leftEnvironment
        (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
          rhoReflectivePresentation)) =
    cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
      (rhoCutOrderRightNode.canonicalizeReifiedTargetFrame rightEnvironment
        (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
          rhoReflectivePresentation)) at frames
  exact congrArg
    (ReflectiveContextSupport.substituteAt
      rhoCIGSLT.costWholeReflectionProfile
      cospan.commonSupport cospan.commonAssignment
      rhoCutOrderLeftNode.targetBound.length) frames

/-- The mixed-colour rho canary closes through the canonical semantic-atom
frame square.  The positional occurrence inventories remain distinct; the
bridge identifies only atoms with equal complete typed semantic keys. -/
noncomputable def rhoCutOrderCanonicalRootBridge :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree rhoCutOrderLeftTree
        rhoCutOrderRightTree :=
  rhoStaticRootBridgeOfCommonKeyedFrame rhoCutOrderLeftNode
    rhoCutOrderRightNode rhoCutOrderLeftChildren rhoCutOrderRightChildren rfl
      rhoCutOrder_commonKeyedSemanticFrames_eq

/-- Tie-tolerant restoration bridge for the same mixed-colour canary,
retained as an independent positive regression.  The production route now
passes through `rhoCutOrderForeignRootBridge` instead. -/
noncomputable def rhoCutOrderRestorationRootBridge :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree rhoCutOrderLeftTree
        rhoCutOrderRightTree :=
  rhoStaticRootBridgeOfCommonRestoredCanonicalFrame rhoCutOrderLeftNode
    rhoCutOrderRightNode rhoCutOrderLeftChildren rhoCutOrderRightChildren rfl
      rhoCutOrder_commonRestoredCanonicalSemanticFrames_eq

/-- The two selected wrapped parent frames expose parallel outer contents in
the common semantic namespace, and those contents coincide exactly for this
fixture.  This is the parallel-factorization premise of the reusable
foreign-root bridge; nothing about endpoint atom order or canonical-frame
equality is consumed here. -/
theorem rhoCutOrder_reified_frames_parallel :
    let leftValues := rhoCutOrderLeftChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer)
    let rightValues := rhoCutOrderRightChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer)
    let leftInventory :=
      (rhoCutOrderLeftNode.semanticAtomEnvironment leftValues).1
    let rightInventory :=
      (rhoCutOrderRightNode.semanticAtomEnvironment rightValues).1
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
    let rightEnvironment :=
      CostStaticAtomEnvironment.ofInventory rightInventory
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
      rhoReflectivePresentation
    ∃ contents : List Pattern,
      cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (rhoCutOrderLeftNode.reifyTargetFrame leftEnvironment) =
        .collection declaration.parallelCollection contents none ∧
      cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rhoCutOrderRightNode.reifyTargetFrame rightEnvironment) =
        .collection declaration.parallelCollection contents none := by
  let leftValues := rhoCutOrderLeftChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rhoCutOrderRightChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (rhoCutOrderLeftNode.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rhoCutOrderRightNode.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
    rhoReflectivePresentation
  have leftFactor :=
    leftEnvironment.reifyWith_reifyTargetFrame_eq_mappedThickenedSkeleton
      rhoCutOrderLeftNode cospan cospan.leftSlot
  have rightFactor :=
    rightEnvironment.reifyWith_reifyTargetFrame_eq_mappedThickenedSkeleton
      rhoCutOrderRightNode cospan cospan.rightSlot
  have commonMapped := rhoCutOrder_commonMappedSemanticFrames_eq_ofInventory
  obtain ⟨contents, leftShape⟩ :
      ∃ contents : List Pattern,
        cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot
            rhoCutOrderLeftNode.mappedThickenedSkeleton.1 =
          .collection declaration.parallelCollection contents none := by
    have skeletonReified :
        cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot
            rhoCutOrderLeftNode.mappedThickenedSkeleton.1 =
          mapPattern (CostStaticColor.symbols rhoCIGSLT .wrapped)
            (cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot
              rhoCutOrderLeftNode.skeleton.1) := by
      rw [rhoCutOrderLeftNode.mappedThickenedSkeleton_pattern,
        CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
          rhoCutOrderLeftNode.thinning rfl]
      exact cospan.reifyWith_mapPattern _ _ _ _
    have skeletonList := congrArg
      (cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot)
      rhoCutOrderLeftNode_skeleton_pattern
    refine ⟨[mapPattern (CostStaticColor.symbols rhoCIGSLT .wrapped)
        (cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot
          (.apply "PDrop"
            [.fvar (costRegionBoundaryVariableName
              rhoCutOrderBoundaryWitness.typed.boundary)])),
      mapPattern (CostStaticColor.symbols rhoCIGSLT .wrapped)
        (cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot
          (.apply "PDrop" [.fvar (costRegionSourceVariableName "a")]))], ?_⟩
    rw [skeletonReified, skeletonList]
    simp only [CostStaticAtomKeyCospan.reifyWith, mapPattern,
      mapPatternList_eq_map, List.map_cons, List.map_nil]
    rfl
  exact ⟨contents, leftFactor.trans leftShape,
    rightFactor.trans (commonMapped.symm.trans leftShape)⟩

/-- Production bridge for the mixed-colour canary, obtained through the
reusable foreign-root terminal.  The fixture's recursively normalized,
restored outer contents coincide exactly, so its permutation premise is the
reflexive one; the bridge itself never consults endpoint atom order or the
stronger canonical-frame equality. -/
noncomputable def rhoCutOrderForeignRootBridge :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree rhoCutOrderLeftTree
        rhoCutOrderRightTree :=
  rhoStaticRootBridgeOfCommonRestoredParallelContentsPerm
    rhoCutOrderLeftNode rhoCutOrderRightNode rhoCutOrderLeftChildren
    rhoCutOrderRightChildren rfl
    rhoCutOrder_reified_frames_parallel.choose_spec.1
    rhoCutOrder_reified_frames_parallel.choose_spec.2
    (List.Perm.refl _)

/-- Proof-relevant root-crossing certificate for the mixed-colour canary.
The two positional environments remain distinct; only their complete
semantic keys meet in the finite apex. -/
noncomputable def rhoCutOrderSemanticFrameAlignment :
    CostStaticAtomFrameAlignment rhoCutOrderLeftSemanticAtoms.2
      rhoCutOrderRightSemanticAtoms.2
        rhoCutOrderLeftNode.mappedThickenedSkeleton.1
        rhoCutOrderRightNode.mappedThickenedSkeleton.1 where
  cospan := rhoCutOrderLeftSemanticAtoms.2.semanticKeyCospan
    rhoCutOrderRightSemanticAtoms.2
  leftCovered := by
    intro name membership
    apply rhoCutOrderLeftNode.skeleton_fvar_covered name
    simpa using membership
  rightCovered := by
    intro name membership
    apply rhoCutOrderRightNode.skeleton_fvar_covered name
    simpa using membership
  reifiedFrames_eq := by
    simpa [CostStaticAtomKeyCospan.reifyLeft,
      CostStaticAtomKeyCospan.reifyRight] using
        rhoCutOrder_commonMappedSemanticFrames_eq

/-- Evaluating the two source frames through their original finite boundary
tables agrees exactly, because both evaluations factor through the common
semantic frame and the common support/value assignment.  This is the local
root-crossing square beneath the already-proved hereditary tree span. -/
theorem rhoCutOrder_commonSemanticRestoration_eq :
    ReflectiveContextSupport.substituteAt
      rhoCIGSLT.costWholeReflectionProfile
        rhoCutOrderLeftNode.boundaryTable.restorationSupport
        ((rhoCutOrderLeftChildren.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)).assignment
            rhoCutOrderLeftNode.boundaryTable)
        0 rhoCutOrderLeftNode.mappedThickenedSkeleton.1 =
      ReflectiveContextSupport.substituteAt
        rhoCIGSLT.costWholeReflectionProfile
        rhoCutOrderRightNode.boundaryTable.restorationSupport
        ((rhoCutOrderRightChildren.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)).assignment
            rhoCutOrderRightNode.boundaryTable)
        0 rhoCutOrderRightNode.mappedThickenedSkeleton.1 := by
  exact CostStaticAtomFrameAlignment.restoredFrames_eq
    rhoCutOrderSemanticFrameAlignment 0

/-- The direct endpoint's finite substitution is the expected compact
wrapped frame.  This is the endpoint factor of the semantic-atom square,
separate from hereditary canonicalization. -/
theorem rhoCutOrderRight_commonSemanticRestoration_pattern :
    ReflectiveContextSupport.substituteAt
      rhoCIGSLT.costWholeReflectionProfile
        rhoCutOrderRightNode.boundaryTable.restorationSupport
        ((rhoCutOrderRightChildren.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)).assignment
            rhoCutOrderRightNode.boundaryTable)
        0 rhoCutOrderRightNode.mappedThickenedSkeleton.1 =
      rhoCutOrderRightPattern := by
  rw [rhoCutOrderRightNode.mappedThickenedSkeleton_pattern,
    CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
      rhoCutOrderRightNode.thinning rfl,
    ReflectiveWellSorted.OpenTerm.toCore_pattern,
    rhoCutOrderRightNode_skeleton_pattern]
  simp [ReflectiveContextSupport.substituteAt,
    hereditaryValues_assignment_sourceVariable,
    rhoCutOrderRightPattern, rhoCutOrderParallel, rhoCutOrderWrappedDrop,
    mapPattern, mapPatternList_eq_map, CostStaticColor.symbols_constructor,
    CostStaticColor.constructorTag, costWrappedConstructorName,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]

/-- The selected left wrapped frame forgets that `0` arrived through a
base-colour boundary and chooses the same semantic representative as a direct
source occurrence. -/
theorem rhoCutOrderLeftNode_normalizeHereditary :
    (CostStaticRegionNode.normalizeHereditary rhoCutOrderLeftNode
      (rhoCutOrderLeftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1 =
      rhoCutOrderRightPattern := by
  exact normalizeHereditary_parallelDrops_zero_a rhoCutOrderLeftNode
    (rhoCutOrderLeftChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer))
    (costRegionBoundaryVariableName
      rhoCutOrderBoundaryWitness.typed.boundary)
    (costRegionSourceVariableName "a")
    rhoCutOrderLeftNode_skeleton_pattern
    rhoCutOrderLeftHereditaryValues_boundaryAssignment
    (hereditaryValues_assignment_sourceVariable _ _ "a") rfl

/-- The direct right wrapped frame chooses that same semantic representative
without needing an opposite-colour child. -/
theorem rhoCutOrderRightNode_normalizeHereditary :
    (CostStaticRegionNode.normalizeHereditary rhoCutOrderRightNode
      (rhoCutOrderRightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1 =
      rhoCutOrderRightPattern := by
  exact normalizeHereditary_parallelDrops_zero_a rhoCutOrderRightNode
    (rhoCutOrderRightChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer))
    (costRegionSourceVariableName "0") (costRegionSourceVariableName "a")
    rhoCutOrderRightNode_skeleton_pattern
    (hereditaryValues_assignment_sourceVariable _ _ "0")
    (hereditaryValues_assignment_sourceVariable _ _ "a") rfl

/-- The two local hereditary evaluator results factor through the generic
proof-relevant semantic-atom square.  Exact evaluator equality is not stored
in this certificate; it is derived from the mapped-frame alignment. -/
noncomputable def rhoCutOrderStaticEvaluationBridge :
    CostStaticAtomEvaluationBridge rhoCutOrderSemanticFrameAlignment 0
      (rhoHereditaryStaticNormalizer rhoCutOrderLeftNode
        (rhoCutOrderLeftChildren.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      (rhoHereditaryStaticNormalizer rhoCutOrderRightNode
        (rhoCutOrderRightChildren.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1 where
  leftFactors := by
    calc
      _ = rhoCutOrderRightPattern := rhoCutOrderLeftNode_normalizeHereditary
      _ = ReflectiveContextSupport.substituteAt
          rhoCIGSLT.costWholeReflectionProfile
          rhoCutOrderRightNode.boundaryTable.restorationSupport
          ((rhoCutOrderRightChildren.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer)).assignment
              rhoCutOrderRightNode.boundaryTable)
          0 rhoCutOrderRightNode.mappedThickenedSkeleton.1 :=
        rhoCutOrderRight_commonSemanticRestoration_pattern.symm
      _ = _ := rhoCutOrder_commonSemanticRestoration_eq.symm
  rightFactors := by
    exact rhoCutOrderRightNode_normalizeHereditary.trans
      rhoCutOrderRight_commonSemanticRestoration_pattern.symm

/-- Positive root-crossing regression through the reusable bridge: the
selected left and right static evaluators agree exactly even though their
finite boundary inventories differ. -/
theorem rhoCutOrder_staticEvaluationBridge_results_eq :
    (rhoHereditaryStaticNormalizer rhoCutOrderLeftNode
        (rhoCutOrderLeftChildren.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1 =
      (rhoHereditaryStaticNormalizer rhoCutOrderRightNode
        (rhoCutOrderRightChildren.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1 :=
  rhoCutOrderStaticEvaluationBridge.results_eq

/-- The mixed-colour rho obstruction inhabits the generic proof-relevant
root-changing tree alignment.  The certificate retains the two distinct
finite boundary inventories and their common semantic-atom cospan. -/
noncomputable def rhoCutOrderTreeNormalizationAlignment :
    CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree rhoCutOrderLeftTree
        rhoCutOrderRightTree :=
  rhoCutOrderForeignRootBridge.toTreeAlignment

/-- Positive generic-alignment regression: the root-aware structural
relation derives exact equality of the complete hereditary tree results. -/
theorem rhoCutOrder_treeNormalizationAlignment_pattern_eq :
    (rhoCutOrderLeftTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (rhoCutOrderRightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  simpa [rhoHereditaryNormalizationKernel] using
    rhoCutOrderTreeNormalizationAlignment.normalize_pattern_eq

/-- Root-only semantic certificate for the mixed-colour outer frame.  The
production authority is the reusable foreign-root bridge; the keyed and
restoration bridges above remain as independent regressions. -/
noncomputable def rhoCutOrderRootBridge :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree rhoCutOrderLeftTree
        rhoCutOrderRightTree :=
  rhoCutOrderForeignRootBridge

/-- The contextual mixed-colour witness still carries the base Quote/Drop
declaration, hence it is foreign to the selected wrapped root. -/
theorem rhoCutOrderAbsorption_color
    (absorption : RhoCostGeneratorAbsorption rhoCutOrderGeneratorWitness) :
    absorption.color = .base :=
  rhoCutOrderAbsorption_color_of_redex rfl rfl absorption

/-- The mixed-colour branch records the exact base declaration against the
decomposition-derived wrapped root before passing to the generic alignment. -/
noncomputable def rhoCutOrderGeneratorRootAlignment :
    RhoCostGeneratorRootAlignment rhoHereditaryNormalizationKernel
      rhoCutOrder_generator := by
  let absorption := Classical.choice
    (nonempty_rhoCostGeneratorAbsorption rhoCutOrderGeneratorWitness)
  exact
    { occurrence := rhoCutOrderGeneratorWitness
      erasesTo := Subsingleton.elim _ _
      absorption := absorption
      leftElaboration := ⟨rhoCutOrderLeftTree⟩
      rightElaboration := ⟨rhoCutOrderRightTree⟩
      regionColor := .wrapped
      leftRoot := .static rhoCutOrderLeftNode rhoCutOrderLeftChildren
      position := .foreign (by
        simpa using rhoCutOrderAbsorption_color absorption)
      rootBridge := rhoCutOrderRootBridge }

/-- Positive foreign-branch canary: the retained base declaration is exactly
opposite the selected wrapped outer frame. -/
theorem rhoCutOrderGeneratorRootAlignment_isForeign :
    rhoCutOrderGeneratorRootAlignment.absorption.color =
      rhoCutOrderGeneratorRootAlignment.regionColor.flip := by
  change rhoCutOrderGeneratorRootAlignment.absorption.color = .base
  exact rhoCutOrderAbsorption_color
    rhoCutOrderGeneratorRootAlignment.absorption

/-- Negative classifier canary: the mixed-colour occurrence cannot be
misreported as selected by the wrapped frame. -/
theorem rhoCutOrderGeneratorRootAlignment_notSelected :
    rhoCutOrderGeneratorRootAlignment.absorption.color ≠
      rhoCutOrderGeneratorRootAlignment.regionColor := by
  intro selected
  have base := rhoCutOrderAbsorption_color
    rhoCutOrderGeneratorRootAlignment.absorption
  have impossible := base.symm.trans selected
  change (CostStaticColor.base : CostStaticColor) = .wrapped at impossible
  cases impossible

/-- The generic tree alignment is tied to the exact authored reflective
occurrence and its support erasure. -/
noncomputable def rhoCutOrderGeneratorTreeNormalizationAlignment :
    CostGeneratorTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrder_generator :=
  rhoCutOrderGeneratorRootAlignment.toGeneratorTreeAlignment

/-- Hereditary normalization of the proof-relevant left tree repairs the
exact ordering mismatch exhibited by the old child-first raw executor. -/
theorem rhoCutOrderLeftTree_normalizeHereditary :
    (CostRegionTree.normalizeHereditary rhoCutOrderLeftTree).pattern =
      rhoCutOrderRightPattern := by
  unfold CostRegionTree.normalizeHereditary rhoCutOrderLeftTree
  calc
    ((CostRegionTree.static rhoCutOrderLeftNode
        rhoCutOrderLeftChildren).normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (rhoHereditaryStaticNormalizer rhoCutOrderLeftNode
          (rhoCutOrderLeftChildren.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1 :=
      CostRegionTree.normalize_static_pattern rhoHereditaryStaticNormalizer
        rhoCutOrderLeftNode rhoCutOrderLeftChildren
    _ = rhoCutOrderRightPattern := rhoCutOrderLeftNode_normalizeHereditary

/-- The proof-relevant right tree reaches the same exact representative. -/
theorem rhoCutOrderRightTree_normalizeHereditary :
    (CostRegionTree.normalizeHereditary rhoCutOrderRightTree).pattern =
      rhoCutOrderRightPattern := by
  unfold CostRegionTree.normalizeHereditary rhoCutOrderRightTree
  calc
    ((CostRegionTree.static rhoCutOrderRightNode
        rhoCutOrderRightChildren).normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (rhoHereditaryStaticNormalizer rhoCutOrderRightNode
          (rhoCutOrderRightChildren.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1 :=
      CostRegionTree.normalize_static_pattern rhoHereditaryStaticNormalizer
        rhoCutOrderRightNode rhoCutOrderRightChildren
    _ = rhoCutOrderRightPattern := rhoCutOrderRightNode_normalizeHereditary

/-- The mixed-colour generator has a proof-relevant root-changing span through
the direct right endpoint.  The left elaboration retains its opposite-colour
Quote/Drop child even though both hereditary evaluations meet at one typed
compact normal object. -/
noncomputable def rhoCutOrderNormalizationSpan :
    CostNormalizationSpan rhoCIGSLT rhoHereditaryStaticNormalizer
      rhoCutOrderLeft rhoCutOrderRight :=
  rhoCutOrderGeneratorTreeNormalizationAlignment.toNormalizationLift.span

/-- The span retains the exact generated reflective occurrence before its
support projection to the proposition-valued reflective generator relation. -/
noncomputable def rhoCutOrderGeneratorNormalizationLift :
    CostGeneratorNormalizationLift rhoCIGSLT
      rhoHereditaryStaticNormalizer rhoCutOrder_generator :=
  rhoCutOrderGeneratorTreeNormalizationAlignment.toNormalizationLift

/-- Vertical chooser coherence transports the hand-built semantic span to
the deterministic production elaborations without inspecting either
dependent boundary table. -/
theorem rhoCutOrder_compiledHereditaryPatterns_eq :
    ((CostOpenElaboration.compile rhoCIGSLT rhoCutOrderLeft).tree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      ((CostOpenElaboration.compile rhoCIGSLT rhoCutOrderRight).tree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
  rhoCutOrderNormalizationSpan.compiledPatterns_eq
    rhoHereditaryCompactCoherent

/-- Exact replay transports the hand-built left witness to the production
planner and hereditary compact executor. -/
theorem rhoCutOrderLeft_costNormalizeOpenHereditary_pattern :
    (rhoCostNormalizeOpenHereditary rhoCutOrderLeft).1 =
      rhoCutOrderRightPattern := by
  rw [rhoCostNormalizeOpenHereditary_pattern]
  rw [← CostRegionTree.normalizeHereditary_eq_buildOpenTerm
    rhoCutOrderLeft rhoCutOrderLeftTree]
  exact rhoCutOrderLeftTree_normalizeHereditary

/-- Exact replay transports the hand-built right witness to the same
production representative. -/
theorem rhoCutOrderRight_costNormalizeOpenHereditary_pattern :
    (rhoCostNormalizeOpenHereditary rhoCutOrderRight).1 =
      rhoCutOrderRightPattern := by
  rw [rhoCostNormalizeOpenHereditary_pattern]
  rw [← CostRegionTree.normalizeHereditary_eq_buildOpenTerm
    rhoCutOrderRight rhoCutOrderRightTree]
  exact rhoCutOrderRightTree_normalizeHereditary

/-- Positive regression: the hereditary production executor exactly
collapses the generated rho equation edge that refutes the old raw executor's
generator-invariance law. -/
theorem rhoCutOrder_costNormalizeOpenHereditary_eq :
    rhoCostNormalizeOpenHereditary rhoCutOrderLeft =
      rhoCostNormalizeOpenHereditary rhoCutOrderRight := by
  apply Subtype.ext
  rw [rhoCutOrderLeft_costNormalizeOpenHereditary_pattern,
    rhoCutOrderRight_costNormalizeOpenHereditary_pattern]

/-- The repaired exact collapse is tied to the actual authored generator,
not merely to two independently chosen example terms. -/
theorem rhoCutOrder_hereditary_generator_canary :
    ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
        rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
        rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
        (.base rhoCutOrderWrappedProcSort.1) rhoCutOrderLeft rhoCutOrderRight ∧
      rhoCostNormalizeOpenHereditary rhoCutOrderLeft =
        rhoCostNormalizeOpenHereditary rhoCutOrderRight :=
  ⟨rhoCutOrder_generator, rhoCutOrder_costNormalizeOpenHereditary_eq⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalCanary
