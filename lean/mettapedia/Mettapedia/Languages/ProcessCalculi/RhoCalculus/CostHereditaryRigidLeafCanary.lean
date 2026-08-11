import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticStructuralClosure
import Mettapedia.GSLT.LanguageDef.CostStaticRootView
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticRootClassification

/-!
# Bound-variable collapse canaries for hereditary rho Cost

The semantic-atom environment is generated from free-variable occurrences.
A reflective collapse can instead expose a bound variable, so a total
static-to-structural closure may not assume that every surviving leaf selects
an atom slot.

There are two distinct boundary cases.  A bare parallel singleton containing
the ambient bound process is a well-sorted open rho Cost object and supplies
the genuine carrier counterexample.  A Quote/Drop shell around an ambient
bound name is typable and canonicalizes to that name, but quotation seals the
outer binder; it therefore fails the reflective-scope component of the open
object carrier.  Recording both facts prevents the typable canary from being
misreported as an admitted object.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

private def rhoRigidLeafFree : FreeTypeContext := fun _ => none

private def rhoRigidNameBound : List TypeExpr :=
  [.base (costBaseSortName "Name")]

private def rhoRigidProcBound : List TypeExpr :=
  [.base (costBaseSortName "Proc")]

private def rhoRigidBaseDeclaration : ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT .base
    rhoReflectivePresentation.toReflectivePresentationDecl

private theorem rhoRigidRule_mem (index : Nat) (inBounds : index < 6) :
    rhoCalc.terms[index]'(by simp [rhoCalc]; omega) ∈ rhoCalc.terms :=
  List.getElem_mem _

/-! ## Typable Quote/Drop collapse outside the admitted carrier -/

def rhoQuoteDropBVarLeft : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [.apply (costBaseConstructorName "PDrop") [.bvar 0]]

def rhoQuoteDropBVarRight : Pattern := .bvar 0

theorem rhoQuoteDropBVarRight_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoRigidLeafFree rhoRigidNameBound
      rhoQuoteDropBVarRight (.base (costBaseSortName "Name")) :=
  .bvar (by simp [rhoRigidNameBound])

private theorem rhoQuoteDropBVarDrop_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoRigidLeafFree rhoRigidNameBound
      (.apply (costBaseConstructorName "PDrop") [.bvar 0])
      (.base (costBaseSortName "Proc")) := by
  apply HasType.constructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[1])
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _
      (rhoRigidRule_mem 1 (by omega))
  · rw [usesBareCollection_costBaseConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costBaseDropConstructor_params]
    exact .cons (by trivial) rfl rhoQuoteDropBVarRight_typed .nil

theorem rhoQuoteDropBVarLeft_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoRigidLeafFree rhoRigidNameBound
      rhoQuoteDropBVarLeft (.base (costBaseSortName "Name")) := by
  apply HasType.constructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[2])
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _
      (rhoRigidRule_mem 2 (by omega))
  · rw [usesBareCollection_costBaseConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costBaseQuoteConstructor_params]
    exact .cons (by trivial) rfl rhoQuoteDropBVarDrop_typed .nil

theorem rhoQuoteDropBVar_canonical :
    canonicalize rhoRigidBaseDeclaration rhoQuoteDropBVarLeft =
      canonicalize rhoRigidBaseDeclaration rhoQuoteDropBVarRight := by
  apply canonicalize_quote_drop
  decide

/-- The outer name binder is sealed by `NQuote`; hence the typable collapse is
not an admitted open object. -/
theorem rhoQuoteDropBVar_not_reflectiveScopeSafe :
    ¬ ReflectiveWellSorted.ReflectiveScopeSafeAt
      rhoCIGSLT.costWholeReflectionProfile
      rhoRigidNameBound.length rhoQuoteDropBVarLeft := by
  intro safe
  have sourceMembership :
    rhoReflectivePresentation.toReflectivePresentationDecl ∈
        rhoCIGSLT.reflection.1.presentations := by
    change rhoReflectivePresentation.toReflectivePresentationDecl ∈
      ReflectionExtension.rhoReflectionProfile.presentations
    simp [ReflectionExtension.rhoReflectionProfile]
  have membership : rhoRigidBaseDeclaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa only [CIGSLT.costWholeReflectionProfile_presentations,
      rhoRigidBaseDeclaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl
        sourceMembership
  have checked := safe rhoRigidBaseDeclaration membership
  have quoteName : rhoRigidBaseDeclaration.quoteConstructor =
      costBaseConstructorName "NQuote" := rfl
  rw [quoteName] at checked
  simp [rhoQuoteDropBVarLeft, binderSafeAt, binderSafeListAt] at checked

theorem rhoQuoteDropBVar_not_wellSorted :
    ¬ ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      rhoRigidLeafFree rhoRigidNameBound
      (.base (costBaseSortName "Name")) rhoQuoteDropBVarLeft := by
  intro admitted
  exact rhoQuoteDropBVar_not_reflectiveScopeSafe admitted.2

/-! ## Admitted parallel-singleton collapse with no semantic atom -/

def rhoParallelSingletonBVarLeft : Pattern :=
  .collection .hashBag [.bvar 0] none

def rhoParallelSingletonBVarRight : Pattern := .bvar 0

theorem rhoParallelSingletonBVarRight_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoRigidLeafFree rhoRigidProcBound
      rhoParallelSingletonBVarRight (.base (costBaseSortName "Proc")) :=
  .bvar (by simp [rhoRigidProcBound])

theorem rhoParallelSingletonBVarLeft_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoRigidLeafFree rhoRigidProcBound
      rhoParallelSingletonBVarLeft (.base (costBaseSortName "Proc")) := by
  apply HasType.collectionConstructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[3])
      (parameterName := "ps")
      (elementType := .base (costBaseSortName "Proc"))
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _
      (rhoRigidRule_mem 3 (by omega))
  · exact rho_costBaseParallelConstructor_params
  · exact .cons rhoParallelSingletonBVarRight_typed
      (.nil rhoRigidProcBound _)

theorem rhoParallelSingletonBVarLeft_wellSorted :
    OpenPatternWellSorted rhoCIGSLT.costWholeLanguage rhoRigidLeafFree
      rhoRigidProcBound (.base (costBaseSortName "Proc"))
      rhoParallelSingletonBVarLeft := by
  exact ⟨rhoParallelSingletonBVarLeft_typed, rfl, rfl,
    rhoParallelSingletonBVarLeft_typed.isWellScopedAt⟩

private theorem rhoParallelSingletonBVarLeft_reflectiveScopeSafe :
    ReflectiveWellSorted.ReflectiveScopeSafeAt
      rhoCIGSLT.costWholeReflectionProfile rhoRigidProcBound.length
      rhoParallelSingletonBVarLeft := by
  intro declaration membership
  simp [rhoParallelSingletonBVarLeft, rhoRigidProcBound,
    binderSafeAt, binderSafeListAt]

theorem rhoParallelSingletonBVarRight_wellSorted :
    OpenPatternWellSorted rhoCIGSLT.costWholeLanguage rhoRigidLeafFree
      rhoRigidProcBound (.base (costBaseSortName "Proc"))
      rhoParallelSingletonBVarRight := by
  exact ⟨rhoParallelSingletonBVarRight_typed, rfl, rfl,
    rhoParallelSingletonBVarRight_typed.isWellScopedAt⟩

private theorem rhoParallelSingletonBVarRight_reflectiveScopeSafe :
    ReflectiveWellSorted.ReflectiveScopeSafeAt
      rhoCIGSLT.costWholeReflectionProfile rhoRigidProcBound.length
      rhoParallelSingletonBVarRight := by
  intro declaration membership
  simp [rhoParallelSingletonBVarRight, rhoRigidProcBound, binderSafeAt]

/-- Checked open term used to exercise the production region-tree compiler. -/
def rhoParallelSingletonBVarTerm :
    ReflectiveWellSorted.OpenTerm rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage rhoRigidLeafFree rhoRigidProcBound
      (CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc) :=
  ⟨rhoParallelSingletonBVarLeft,
    rhoParallelSingletonBVarLeft_wellSorted,
    rhoParallelSingletonBVarLeft_reflectiveScopeSafe⟩

private def rhoRigidParallelChoice : CostCollectionTypingChoice :=
  .bare rhoCalc.terms[3] (.base "Proc")

private theorem rhoRigidParallelChoice_mem :
    rhoRigidParallelChoice ∈
      costStaticCollectionTypingChoices rhoCIGSLT .base rhoRigidLeafFree
        rhoRigidProcBound .hashBag [rhoParallelSingletonBVarRight]
        (mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT)
          (.base rhoProc.1)) := by
  apply mem_costStaticCollectionTypingChoices_complete
  right
  refine ⟨rhoCalc.terms[3], .base "Proc", rfl,
    rhoRigidRule_mem 3 (by omega), ?_, rfl, "ps", rfl, rfl⟩
  apply rhoCIGSLT.bareCollectionConstructorsWrapped _
    (rhoRigidRule_mem 3 (by omega))
  exact ⟨"ps", .hashBag, .base "Proc", rfl⟩

private def rhoParallelSingletonBVarElementPlan (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .base rhoRigidLeafFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base
        rhoRigidProcBound)
      rhoRigidProcBound
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base
        rhoRigidProcBound)
      rhoRigidProcBound outer rhoParallelSingletonBVarRight
      (.base "Proc") := by
  have boundEq : rhoRigidProcBound =
      [mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT)
        (.base "Proc")] := rfl
  apply CostStaticRegionPlan.bvar 0
  · rw [boundEq]
    change
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base
        (([.base "Proc"] : List TypeExpr).map
          (mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT))))[0]? =
        some (.base "Proc")
    rw [CostStaticBinderThinning.sourceContextOfTarget_map]
    rfl
  · rw [boundEq,
      CostStaticBinderThinning.toSourceIndex?_eq_targetToSourceIndex?]
    simp [CostStaticBinderThinning.targetToSourceIndex?]
  · rw [boundEq]
    change 0 <
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base
        (([.base "Proc"] : List TypeExpr).map
          (mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT)))).length
    rw [CostStaticBinderThinning.sourceContextOfTarget_map]
    decide

private def rhoParallelSingletonBVarPlan :
    CostStaticRegionPlan rhoCIGSLT .base rhoRigidLeafFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base
        rhoRigidProcBound)
      rhoRigidProcBound
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base
        rhoRigidProcBound)
      rhoRigidProcBound .hole rhoParallelSingletonBVarLeft
      (.base "Proc") := by
  apply CostStaticRegionPlan.collection rhoRigidParallelChoice
    rhoRigidParallelChoice_mem
  exact .cons
    (rhoParallelSingletonBVarElementPlan
      (OneHoleContext.collection .hashBag [] .hole [] none))
    .nil

private def rhoParallelSingletonBVarNode :
    CostStaticRegionNode rhoCIGSLT .base rhoRigidLeafFree :=
  CostStaticRegionNode.ofPlan rhoParallelSingletonBVarTerm.toCore
    rhoParallelSingletonBVarPlan rfl

private def rhoParallelSingletonBVarChildren :
    CostRegionBoundaryTrees rhoCIGSLT rhoRigidLeafFree .base
      rhoParallelSingletonBVarNode.finiteBoundaryTable :=
  CostRegionBoundaryTrees.ofEntriesEqNil
    rhoParallelSingletonBVarNode.finiteBoundaryTable (by rfl)

/-- The singleton static tree at the node's intrinsic dependent indices. -/
private def rhoParallelSingletonBVarStaticTree :
    CostRegionTree rhoCIGSLT rhoRigidLeafFree
      rhoParallelSingletonBVarNode.targetBound []
      rhoParallelSingletonBVarNode.term.1
      (.base (CostStaticColor.base.mapLangSort rhoCIGSLT
        rhoParallelSingletonBVarNode.sourceSort).1) :=
  .static rhoParallelSingletonBVarNode rhoParallelSingletonBVarChildren

private theorem rhoParallelSingletonBVarNode_targetBound :
    rhoParallelSingletonBVarNode.targetBound = rhoRigidProcBound := by
  rfl

private theorem rhoParallelSingletonBVarNode_term_pattern :
    rhoParallelSingletonBVarNode.term.1 =
      rhoParallelSingletonBVarLeft := by
  rfl

private theorem rhoParallelSingletonBVarNode_resultType :
    (.base (CostStaticColor.base.mapLangSort rhoCIGSLT
      rhoParallelSingletonBVarNode.sourceSort).1 : TypeExpr) =
        .base (costBaseSortName "Proc") := by
  rfl

/-- Hand-checked decomposition of the same open object.  It is used only as
proof-relevant evidence; exact compiler replay later transports its result to
the deterministic production tree.  The transports are explicit so that the
finite boundary table remains opaque during normalization. -/
def rhoParallelSingletonBVarTree :
    CostRegionTree rhoCIGSLT rhoRigidLeafFree rhoRigidProcBound []
      rhoParallelSingletonBVarLeft (.base (costBaseSortName "Proc")) :=
  CostRegionTree.reindexType rhoParallelSingletonBVarNode_resultType
    (CostRegionTree.reindexPattern rhoParallelSingletonBVarNode_term_pattern
      (CostRegionTree.reindexAvailable
        rhoParallelSingletonBVarNode_targetBound
        rhoParallelSingletonBVarStaticTree))

@[simp]
private theorem rhoParallelSingletonBVarNode_skeleton :
    rhoParallelSingletonBVarNode.skeleton.1 =
      rhoParallelSingletonBVarLeft := by
  rfl

private theorem rhoParallelSingletonBVarNode_reifiedSourceFrame
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT .base
      rhoRigidLeafFree rhoParallelSingletonBVarNode.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT .base rhoRigidLeafFree
      rhoParallelSingletonBVarNode.boundaryTable values
      rhoParallelSingletonBVarNode.skeleton.1) :
    (rhoParallelSingletonBVarNode.reifiedSourceFrame
      (CostStaticAtomEnvironment.ofInventory inventory)).1 =
        .collection rhoReflectivePresentation.parallelCollection
          [.bvar 0] none := by
  rw [rhoParallelSingletonBVarNode.reifiedSourceFrame_pattern]
  change (CostStaticAtomEnvironment.ofInventory inventory).reify
      rhoParallelSingletonBVarLeft = _
  simp [rhoParallelSingletonBVarLeft, CostStaticAtomEnvironment.reify,
    rhoReflectivePresentation]

@[simp]
private theorem rhoParallelSingletonBVarNode_mappedBVar :
    rhoParallelSingletonBVarNode.thinning.thickenAmbientBVars 0
        (mapPattern (CostStaticColor.base.symbols rhoCIGSLT) (.bvar 0)) =
      .bvar 0 := by
  simp only [mapPattern, CostStaticBinderThinning.thickenAmbientBVars]
  have contracted :
      rhoParallelSingletonBVarNode.thinning.toSourceIndex? 0 = some 0 := by
    rw [CostStaticBinderThinning.toSourceIndex?_eq_targetToSourceIndex?]
    simp only [rhoParallelSingletonBVarNode, CostStaticRegionNode.ofPlan,
      rhoParallelSingletonBVarTerm, rhoRigidProcBound,
      CostStaticBinderThinning.targetToSourceIndex?]
    change (match decodeCostStaticTypeExpr rhoCIGSLT .base
        (mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT)
          (.base "Proc")) with
      | none => none
      | some _ => some 0) = some 0
    rw [decodeCostStaticTypeExpr_mapTypeExpr]
  have embedded :=
    rhoParallelSingletonBVarNode.thinning.toTargetIndex_of_toSourceIndex?_eq_some
      contracted
  simp [CostStaticBinderThinning.embedIndexAt, embedded]

/-- The explicit proof-relevant singleton decomposition evaluates through
the rigid-leaf branch rather than manufacturing a semantic-atom slot. -/
theorem rhoParallelSingletonBVarNode_normalizeHereditary
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT .base
      rhoRigidLeafFree rhoParallelSingletonBVarNode.boundaryTable) :
    (CostStaticRegionNode.normalizeHereditary
      rhoParallelSingletonBVarNode values).1 =
        rhoParallelSingletonBVarRight := by
  unfold CostStaticRegionNode.normalizeHereditary
  rw [CostStaticRegionNode.normalizeHereditaryWithInventory_pattern]
  let inventory :=
    (rhoParallelSingletonBVarNode.semanticAtomEnvironment values).1
  have evaluated :=
    CostStaticRegionNode.normalizeHereditaryRawWithInventory_parallelSingleton_bvar
      rhoParallelSingletonBVarNode values inventory 0
        (rhoParallelSingletonBVarNode_reifiedSourceFrame values inventory)
  simpa only [rhoParallelSingletonBVarNode_mappedBVar,
    rhoParallelSingletonBVarRight] using evaluated

/-- The complete hand-checked tree exposes the bound process after child-first
hereditary normalization. -/
theorem rhoParallelSingletonBVarTree_normalizeHereditary :
    (CostRegionTree.normalizeHereditary
      rhoParallelSingletonBVarTree).pattern =
        rhoParallelSingletonBVarRight := by
  unfold CostRegionTree.normalizeHereditary rhoParallelSingletonBVarTree
  rw [CostRegionTree.reindexType_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer),
    CostRegionTree.reindexPattern_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer),
    CostRegionTree.reindexAvailable_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)]
  unfold rhoParallelSingletonBVarStaticTree
  rw [CostRegionTree.normalize_static_pattern]
  exact rhoParallelSingletonBVarNode_normalizeHereditary _

/-- Exact replay transports the rigid-leaf calculation to the deterministic
production elaboration. -/
theorem rhoParallelSingletonBVarCompiled_normalizeHereditary :
    (CostRegionTree.normalizeHereditary
      (CostRegionTree.buildOpenTerm
        (source := rhoCIGSLT) rhoParallelSingletonBVarTerm)).pattern =
        rhoParallelSingletonBVarRight := by
  rw [← CostRegionTree.normalizeHereditary_eq_buildOpenTerm
    rhoParallelSingletonBVarTerm rhoParallelSingletonBVarTree]
  exact rhoParallelSingletonBVarTree_normalizeHereditary

/-- The deterministic compiler retains the admitted singleton bag as one
static root. -/
theorem rhoParallelSingletonBVarTree_rootIsStatic :
    (CostRegionTree.buildOpenTerm
      (source := rhoCIGSLT) rhoParallelSingletonBVarTerm).rootIsStatic = true :=
  CostStaticRootShape.baseCollection.rootIsStatic _

/-- The process singleton cannot be selected at the wrapped colour: rho's
interacting `Proc` sort is sent to the reserved wrapped sort there, whereas
the compiled endpoint lives in the generated base-`Proc` fibre. -/
theorem rhoParallelSingletonBVarStaticRootColor_eq_base
    {color : CostStaticColor}
    (root : CostRegionTree.StaticRootColor rhoCIGSLT rhoRigidLeafFree
      (CostRegionTree.buildOpenTerm
        (source := rhoCIGSLT) rhoParallelSingletonBVarTerm) color) :
    color = .base := by
  cases color with
  | base => rfl
  | wrapped =>
      let view := root.toView
      have sortEq :
          CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc =
            CostStaticColor.wrapped.mapLangSort rhoCIGSLT
              view.node.sourceSort := by
        apply Subtype.ext
        have typeEq := view.typeEq
        injection typeEq with nameEq
        exact nameEq.symm
      have avoids :=
        (CostStaticColor.mapLangSort_base_eq_wrapped_iff_eq rhoCIGSLT
          rhoProc view.node.sourceSort).1 sortEq
      have sourceSortEq :
          view.node.sourceSort.1 =
            rhoCIGSLT.theory.presentation.interactingSort.1.name := by
        calc
          view.node.sourceSort.1 = rhoProc.1 :=
            congrArg Subtype.val avoids.1.symm
          _ = rhoCIGSLT.theory.presentation.interactingSort.1.name := by
            rfl
      exact (avoids.2 sourceSortEq).elim

/-- Exact base-colour static certificate recovered from the compiled tree. -/
noncomputable def rhoParallelSingletonBVarBaseRoot :
    CostRegionTree.StaticRootColor rhoCIGSLT rhoRigidLeafFree
      (CostRegionTree.buildOpenTerm
        (source := rhoCIGSLT) rhoParallelSingletonBVarTerm) .base := by
  let packed := Classical.choice
    (CostStaticRootShape.baseCollection.nonempty_staticRootColor
      (CostRegionTree.buildOpenTerm
        (source := rhoCIGSLT) rhoParallelSingletonBVarTerm))
  have colorEq : packed.1 = .base :=
    rhoParallelSingletonBVarStaticRootColor_eq_base packed.2
  exact cast
    (congrArg
      (fun color => CostRegionTree.StaticRootColor rhoCIGSLT rhoRigidLeafFree
        (CostRegionTree.buildOpenTerm
          (source := rhoCIGSLT) rhoParallelSingletonBVarTerm) color)
      colorEq)
    packed.2

/-- Cast-stable node/forest view of the actual compiler output. -/
noncomputable def rhoParallelSingletonBVarStaticView :=
  rhoParallelSingletonBVarBaseRoot.toView

/-- Structural endpoint exposed by singleton collapse. -/
def rhoParallelSingletonBVarRightTree :
    CostRegionTree rhoCIGSLT rhoRigidLeafFree rhoRigidProcBound []
      rhoParallelSingletonBVarRight (.base (costBaseSortName "Proc")) :=
  .bvar (by simp [rhoRigidProcBound])

@[simp]
theorem rhoParallelSingletonBVarRightTree_normalize :
    (rhoParallelSingletonBVarRightTree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        rhoParallelSingletonBVarRight := by
  simp [rhoParallelSingletonBVarRightTree, CostRegionTree.normalize,
    rhoParallelSingletonBVarRight]

/-- The actual deterministic compiler output closes against the structural
bound-variable endpoint through the rigid-leaf terminal.  This is the
production-path regression: the hand tree is used only to prove the compiled
normal form above, while the bridge itself exposes the compiler's static
root certificate. -/
noncomputable def rhoParallelSingletonBVarCompiledRootBridge :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoRigidLeafFree
      (CostRegionTree.buildOpenTerm
        (source := rhoCIGSLT) rhoParallelSingletonBVarTerm)
      rhoParallelSingletonBVarRightTree := by
  apply CostRegionTree.StaticRootView.rootBridge_reindex_left
    rhoParallelSingletonBVarStaticView
  let staticNormal :
      (rhoHereditaryStaticNormalizer
        rhoParallelSingletonBVarStaticView.node
        (rhoParallelSingletonBVarStaticView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1 =
          rhoParallelSingletonBVarRight := by
    calc
      (rhoHereditaryStaticNormalizer
          rhoParallelSingletonBVarStaticView.node
          (rhoParallelSingletonBVarStaticView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1 =
          ((CostRegionTree.buildOpenTerm
          (source := rhoCIGSLT) rhoParallelSingletonBVarTerm).normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
        (rhoParallelSingletonBVarStaticView.normalize_pattern
          rhoHereditaryStaticNormalizer).symm
      _ = rhoParallelSingletonBVarRight := by
        simpa only [CostRegionTree.normalizeHereditary] using
          rhoParallelSingletonBVarCompiled_normalizeHereditary
  let exposure : RhoCollapsingLeafExposure
      rhoParallelSingletonBVarStaticView.node
      rhoParallelSingletonBVarStaticView.children
      rhoParallelSingletonBVarRightTree :=
    .rigidBVar 0
      (by simpa [rhoParallelSingletonBVarRight] using staticNormal)
      (by simpa [rhoParallelSingletonBVarRight] using
        rhoParallelSingletonBVarRightTree_normalize)
  exact exposure.toRootBridge

/-- The production bridge entails exact hereditary equality without exposing
the compiler's dependent boundary table. -/
theorem rhoParallelSingletonBVarCompiledRootBridge_normalize_pattern_eq :
    ((CostRegionTree.buildOpenTerm
        (source := rhoCIGSLT) rhoParallelSingletonBVarTerm).normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (rhoParallelSingletonBVarRightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
  rhoParallelSingletonBVarCompiledRootBridge.toTreeAlignment.normalize_pattern_eq

theorem rhoParallelSingletonBVar_canonical :
    canonicalize rhoRigidBaseDeclaration rhoParallelSingletonBVarLeft =
      canonicalize rhoRigidBaseDeclaration rhoParallelSingletonBVarRight := by
  change canonicalize rhoRigidBaseDeclaration
      (.collection rhoRigidBaseDeclaration.parallelCollection
        [rhoParallelSingletonBVarRight] none) = _
  exact canonicalize_parallel_singleton rhoRigidBaseDeclaration
    rhoParallelSingletonBVarRight

/-! ## Exact zero-atom inventories -/

private def rhoRigidEmptyTable :
    TypedCostRegionBoundaryTable rhoCIGSLT .base rhoRigidLeafFree [] := .nil

private def rhoRigidEmptyValues :
    TypedCostRegionBoundaryTable.Values rhoCIGSLT .base rhoRigidLeafFree
      rhoRigidEmptyTable := .nil

private def rhoQuoteDropBVarSourceFrame : Pattern :=
  .apply "NQuote" [.apply "PDrop" [.bvar 0]]

private def rhoQuoteDropBVarInventory :
    CostStaticParameterInventory rhoCIGSLT .base rhoRigidLeafFree
      rhoRigidEmptyTable rhoRigidEmptyValues rhoQuoteDropBVarSourceFrame where
  entries := []
  positions := by
    simp [CostStaticFVarOccurrence.enumerate, rhoQuoteDropBVarSourceFrame,
      Pattern.freeFvarNames]

private def rhoParallelSingletonBVarInventory :
    CostStaticParameterInventory rhoCIGSLT .base rhoRigidLeafFree
      rhoRigidEmptyTable rhoRigidEmptyValues rhoParallelSingletonBVarLeft where
  entries := []
  positions := by
    simp [CostStaticFVarOccurrence.enumerate, rhoParallelSingletonBVarLeft,
      Pattern.freeFvarNames]

/-- Every exact inventory of the bound-variable Quote/Drop source frame is
empty, independently of the boundary table from which it is requested. -/
theorem rhoQuoteDropBVar_anyInventory_empty
    {targetFree : FreeTypeContext} {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT .base targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT .base targetFree
      table}
    (inventory : CostStaticParameterInventory rhoCIGSLT .base targetFree table
      values rhoQuoteDropBVarSourceFrame) :
    inventory.entries = [] := by
  have positions := inventory.positions
  simpa [CostStaticFVarOccurrence.enumerate, rhoQuoteDropBVarSourceFrame,
    Pattern.freeFvarNames] using positions

/-- Every exact inventory of the admitted bound-process singleton is empty.
This statement applies directly to the inventory projected from any compiled
static node with this source frame. -/
theorem rhoParallelSingletonBVar_anyInventory_empty
    {targetFree : FreeTypeContext} {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT .base targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT .base targetFree
      table}
    (inventory : CostStaticParameterInventory rhoCIGSLT .base targetFree table
      values rhoParallelSingletonBVarLeft) :
    inventory.entries = [] := by
  have positions := inventory.positions
  simpa [CostStaticFVarOccurrence.enumerate, rhoParallelSingletonBVarLeft,
    Pattern.freeFvarNames] using positions

theorem rhoQuoteDropBVar_anyInventory_noSemanticAtom
    {targetFree : FreeTypeContext} {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT .base targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT .base targetFree
      table}
    (inventory : CostStaticParameterInventory rhoCIGSLT .base targetFree table
      values rhoQuoteDropBVarSourceFrame) :
    IsEmpty (Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount) := by
  rw [CostStaticAtomEnvironment.ofInventory_atomCount]
  simp only [CostStaticParameterInventory.semanticAtoms,
    rhoQuoteDropBVar_anyInventory_empty inventory, List.map_nil,
    List.dedup_nil, List.length_nil]
  infer_instance

theorem rhoParallelSingletonBVar_anyInventory_noSemanticAtom
    {targetFree : FreeTypeContext} {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT .base targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT .base targetFree
      table}
    (inventory : CostStaticParameterInventory rhoCIGSLT .base targetFree table
      values rhoParallelSingletonBVarLeft) :
    IsEmpty (Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount) := by
  rw [CostStaticAtomEnvironment.ofInventory_atomCount]
  simp only [CostStaticParameterInventory.semanticAtoms,
    rhoParallelSingletonBVar_anyInventory_empty inventory, List.map_nil,
    List.dedup_nil, List.length_nil]
  infer_instance

theorem rhoQuoteDropBVar_inventory_empty :
    rhoQuoteDropBVarInventory.entries = [] :=
  rhoQuoteDropBVar_anyInventory_empty rhoQuoteDropBVarInventory

theorem rhoParallelSingletonBVar_inventory_empty :
    rhoParallelSingletonBVarInventory.entries = [] :=
  rhoParallelSingletonBVar_anyInventory_empty
    rhoParallelSingletonBVarInventory

/-- Bound variables do not manufacture semantic-atom slots in a Quote/Drop
source frame.  This is an inventory fact, not an admission claim. -/
theorem rhoQuoteDropBVar_noSemanticAtom :
    IsEmpty (Fin (CostStaticAtomEnvironment.ofInventory
      rhoQuoteDropBVarInventory).atomCount) := by
  exact rhoQuoteDropBVar_anyInventory_noSemanticAtom
    rhoQuoteDropBVarInventory

/-- The admitted parallel-singleton collapse has no semantic-atom slot.  A
total asymmetric closure therefore needs an independently restored rigid-leaf
case in addition to its atom case. -/
theorem rhoParallelSingletonBVar_noSemanticAtom :
    IsEmpty (Fin (CostStaticAtomEnvironment.ofInventory
      rhoParallelSingletonBVarInventory).atomCount) := by
  exact rhoParallelSingletonBVar_anyInventory_noSemanticAtom
    rhoParallelSingletonBVarInventory

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
