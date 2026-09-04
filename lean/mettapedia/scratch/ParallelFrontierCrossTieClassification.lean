import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier

/-!
# Classifying a canonicalized frontier endpoint back to its leaf provenance

The cross-tie obligation of the independent-depth parallel provider quantifies
over endpoints of `parallelContents` applied to the keyed canonical frame of a
whole admitted plan.  Discharging it needs each endpoint returned to the leaf
it came from, together with that leaf's admitted provenance.
-/

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhoCommonRestorationApex
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelFrontier

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ParallelFrontierCrossTies

/-- **Endpoint provenance.**  Every element of the keyed canonical parallel
contents of an admitted process plan's parent frame is the keyed canonical
frame of one authored frontier leaf, and that leaf carries its full admitted
provenance together with its membership in the raw payload frontier. -/
theorem exists_leafWitness_of_mem_parallelContents
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      table values root}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {frameSourceBound frameTargetBound : List TypeExpr}
    (frameThinning : CostStaticBinderThinning rhoCIGSLT color
      frameSourceBound frameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (admission : plan.RawAdmission) (scopeDepth keyDepth : Nat)
    {endpoint : Pattern} :
    let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
      color rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    let frame := fun pattern =>
      cospan.reifyWith environment.lookupAtom? leg
        (frameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (environment.reify pattern)))
    endpoint ∈ parallelContents targetDeclaration
        (canonicalizeListByAt key targetDeclaration keyDepth
          [frame plan.abstractPattern]) →
      ∃ rawLeaf abstractLeaf,
        rawLeaf ∈ parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            payload ∧
          LeafWitness sourceBound targetBound thinning sourceAvailable
            plan.abstractPattern plan.boundaryTable.entries rawLeaf
              abstractLeaf ∧
          canonicalizeByAt key targetDeclaration keyDepth
            (frame abstractLeaf) = endpoint := by
  intro targetDeclaration key frame membership
  have permutation :=
    processPlan_commonReifiedMappedThickened_frontier_perm environment
      frameThinning cospan leg plan admission scopeDepth keyDepth
  have mappedMembership : endpoint ∈
      (parallelLeaves rhoReflectivePresentation.toReflectivePresentationDecl
        plan.abstractPattern).map
          (fun leaf => canonicalizeByAt key targetDeclaration keyDepth
            (frame leaf)) := by
    refine (List.Perm.mem_iff ?_).mp membership
    simpa only [canonicalizeListByAt, key, frame, targetDeclaration]
      using permutation
  have traversal :=
    parallelLeaves_map_abstractPattern_forall2_with_membership plan admission
      (fun leaf => canonicalizeByAt key targetDeclaration keyDepth
        (frame leaf))
  obtain ⟨rawLeaf, _rawMembership, abstractLeaf, leafMembership, witness,
      framed⟩ := exists_left_of_forall₂_mem_right traversal mappedMembership
  exact ⟨rawLeaf, abstractLeaf, leafMembership, witness, framed⟩

/-! ## Depth constancy from closed assignments -/

/-- **Closed assignments restore uniformly.**  When every value a support
assignment can install is binder-closed, reflective supported substitution no
longer depends on the visible depth, at any pattern.  This is the engine
behind every rigid and closed-atom cross tie: two such leaves that agree at
one depth agree at all of them. -/
theorem substituteAt_eq_of_assignment_isWellScopedAt_zero
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support) (assignment : ContextSupport.Assignment)
    (closed : ∀ name, (assignment name).isWellScopedAt 0 = true)
    (pattern : Pattern) (first second : Nat) :
    ReflectiveContextSupport.substituteAt profile support assignment first
        pattern =
      ReflectiveContextSupport.substituteAt profile support assignment second
        pattern := by
  induction pattern using Pattern.inductionOn generalizing first second with
  | hbvar index => simp only [ReflectiveContextSupport.substituteAt]
  | hfvar name =>
      simp only [ReflectiveContextSupport.substituteAt]
      rw [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
          (closed name),
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
          (closed name)]
  | happly constructor arguments inductionHypothesis =>
      simp only [ReflectiveContextSupport.substituteAt, Pattern.apply.injEq,
        true_and]
      refine List.map_congr_left ?_
      intro argument membership
      exact inductionHypothesis argument membership _ _
  | hlambda binder body inductionHypothesis =>
      simp only [ReflectiveContextSupport.substituteAt, Pattern.lambda.injEq,
        true_and]
      exact inductionHypothesis _ _
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [ReflectiveContextSupport.substituteAt,
        Pattern.multiLambda.injEq, true_and]
      exact inductionHypothesis _ _
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [ReflectiveContextSupport.substituteAt, Pattern.subst.injEq]
      exact ⟨bodyHypothesis _ _, replacementHypothesis _ _⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [ReflectiveContextSupport.substituteAt,
        Pattern.collection.injEq, true_and, and_true]
      refine List.map_congr_left ?_
      intro element membership
      exact inductionHypothesis element membership _ _

/-- **Uniform ties from closed assignments.**  Two patterns that restore
equally at one depth restore equally at every depth, whenever the common
assignment installs only binder-closed values. -/
theorem restoresTogether_of_substituteAt_eq_of_assignment_isWellScopedAt_zero
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support) (assignment : ContextSupport.Assignment)
    (closed : ∀ name, (assignment name).isWellScopedAt 0 = true)
    {left right : Pattern} {keyDepth : Nat}
    (tie : ReflectiveContextSupport.substituteAt profile support assignment
        keyDepth left =
      ReflectiveContextSupport.substituteAt profile support assignment
        keyDepth right) :
    ReflectiveContextSupport.RestoresTogether profile support assignment left
      right := by
  intro depth
  rw [substituteAt_eq_of_assignment_isWellScopedAt_zero profile support
      assignment closed left depth keyDepth,
    substituteAt_eq_of_assignment_isWellScopedAt_zero profile support
      assignment closed right depth keyDepth]
  exact tie

/-! ## The binder discipline blocking a process-supported semantic atom -/

/-- **Every binder of the process calculus binds a name.**  The grammar's only
abstraction parameter is the input continuation, whose binder type is the
name-to-process arrow.  Consequently no ambient binder context of an admitted
plan ever carries a process type. -/
theorem rhoCalc_abstraction_type_eq_name_to_process
    (rule : Mettapedia.OSLF.MeTTaIL.Syntax.GrammarRule)
    (membership : rule ∈ rhoCalc.terms)
    {binderName : Option String} {binder : String} {binderType : TypeExpr}
    (parameter :
      Mettapedia.OSLF.MeTTaIL.Syntax.TermParam.abstractionNamed binderName
        binder binderType ∈ rule.params) :
    binderType = TypeExpr.funType TypeExpr.name TypeExpr.proc := by
  change rule ∈ [rhoCalc.terms[0], rhoCalc.terms[1], rhoCalc.terms[2],
    rhoCalc.terms[3], rhoCalc.terms[4], rhoCalc.terms[5]] at membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rhoCalc, List.getElem_cons_zero, List.getElem_cons_succ,
      List.mem_cons, List.not_mem_nil, or_false,
      Mettapedia.OSLF.MeTTaIL.Syntax.TermParam.abstraction] at parameter <;>
    simp_all

/-! ## Boundary endpoints are parent semantic atoms -/

theorem boundaryPlan_commonFrame_eq_atom
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      table}
    {rootAbstract : Pattern}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      table values rootAbstract}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {frameSourceBound frameTargetBound : List TypeExpr}
    (frameThinning : CostStaticBinderThinning rhoCIGSLT color
      frameSourceBound frameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer skeletonContext : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (rootEq : rootAbstract = skeletonContext.fill plan.abstractPattern)
    (boundaryClass : plan.rootClass.IsCertifiedBoundary)
    (scopeDepth keyDepth : Nat) :
    let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
      color rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    ∃ slot : Fin environment.atomCount,
      canonicalizeByAt key targetDeclaration keyDepth
          (cospan.reifyWith environment.lookupAtom? leg
            (frameThinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (environment.reify plan.abstractPattern)))) =
        cospan.reifyWith environment.lookupAtom? leg
          (.fvar (environment.atomName slot)) := by
  dsimp only
  let reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract :=
    { sourceBound := sourceBound
      targetBound := targetBound
      thinning := thinning
      sourceAvailable := sourceAvailable
      outer := outer
      sourceType := .base "Proc"
      plan := plan
      skeletonContext := skeletonContext
      abstract_eq := rootEq }
  obtain ⟨boundary⟩ :=
    reached.nonempty_boundaryView_of_boundaryClass boundaryClass
  obtain ⟨slot, selected⟩ := Option.isSome_iff_exists.mp
    (environment.slotOfName?_isSome_of_occurrence
      boundary.stopped.boundaryOccurrence)
  refine ⟨slot, ?_⟩
  rw [boundary.abstract_eq]
  simp only [CostStaticAtomEnvironment.reify,
    CostStaticBinderThinning.thickenAmbientBVars, mapPattern]
  unfold CostStaticAtomEnvironment.reifyName
  have selected' : environment.slotOfName?
      (costRegionBoundaryVariableName boundary.stopped.certified.typed.boundary) =
        some slot := by
    simpa only [boundary.stopped.boundaryOccurrence_name] using selected
  rw [selected']
  simp [Pattern.renameFVars, canonicalizeByAt]

theorem boundaryPlans_commonRestorationApex_of_keyEq
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable rightValues rightRoot}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftFrameSourceBound leftFrameTargetBound : List TypeExpr}
    {rightFrameSourceBound rightFrameTargetBound : List TypeExpr}
    (leftFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      leftFrameSourceBound leftFrameTargetBound)
    (rightFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      rightFrameSourceBound rightFrameTargetBound)
    {leftSourceBound leftTargetBound rightSourceBound rightTargetBound :
      List TypeExpr}
    {leftThinning : CostStaticBinderThinning rhoCIGSLT color leftSourceBound
      leftTargetBound}
    {rightThinning : CostStaticBinderThinning rhoCIGSLT color rightSourceBound
      rightTargetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter leftContext rightContext : OneHoleContext}
    {leftPayload rightPayload : Pattern}
    (leftPlan : CostStaticRegionPlan rhoCIGSLT color targetFree leftSourceBound
      leftTargetBound leftThinning leftAvailable leftOuter leftPayload
      (.base "Proc"))
    (rightPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
      rightSourceBound rightTargetBound rightThinning rightAvailable rightOuter
      rightPayload (.base "Proc"))
    (leftRootEq : leftRoot = leftContext.fill leftPlan.abstractPattern)
    (rightRootEq : rightRoot = rightContext.fill rightPlan.abstractPattern)
    (leftBoundary : leftPlan.rootClass.IsCertifiedBoundary)
    (rightBoundary : rightPlan.rootClass.IsCertifiedBoundary)
    {exposedSupport : List TypeExpr}
    (leftSupport : ∀ slot,
      (leftEnvironment.atomValue slot).key.targetSupport = exposedSupport ∨
        (leftEnvironment.atomValue slot).key.targetSupport = [])
    (rightSupport : ∀ slot,
      (rightEnvironment.atomValue slot).key.targetSupport = exposedSupport ∨
        (rightEnvironment.atomValue slot).key.targetSupport = [])
    (scopeDepth keyDepth restorationDepth : Nat)
    (keyEq :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
        color rhoReflectivePresentation.toReflectivePresentationDecl
      let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
      key keyDepth
          (canonicalizeByAt key targetDeclaration keyDepth
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftFrameThinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols rhoCIGSLT)
                  (leftEnvironment.reify leftPlan.abstractPattern))))) =
        key keyDepth
          (canonicalizeByAt key targetDeclaration keyDepth
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightFrameThinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols rhoCIGSLT)
                  (rightEnvironment.reify rightPlan.abstractPattern)))))) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
      color rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      targetDeclaration restorationDepth
      (canonicalizeByAt key targetDeclaration keyDepth
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftFrameThinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (leftEnvironment.reify leftPlan.abstractPattern)))))
      (canonicalizeByAt key targetDeclaration keyDepth
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightFrameThinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (rightEnvironment.reify rightPlan.abstractPattern))))) := by
  dsimp only at keyEq ⊢
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  obtain ⟨leftSlot, leftShape⟩ :=
    boundaryPlan_commonFrame_eq_atom leftEnvironment leftFrameThinning cospan
      cospan.leftSlot leftPlan leftRootEq leftBoundary scopeDepth keyDepth
  obtain ⟨rightSlot, rightShape⟩ :=
    boundaryPlan_commonFrame_eq_atom rightEnvironment rightFrameThinning cospan
      cospan.rightSlot rightPlan rightRootEq rightBoundary scopeDepth keyDepth
  have atomKeyEq :
      key keyDepth
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (.fvar (leftEnvironment.atomName leftSlot))) =
        key keyDepth
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (.fvar (rightEnvironment.atomName rightSlot))) := by
    rw [← leftShape, ← rightShape]
    exact keyEq
  have atomApex :=
    RhoMatchedStaticFramesApex.atom_of_keyEqAt_of_support_eq_or_nil
      leftEnvironment rightEnvironment leftSlot rightSlot
      (leftSupport leftSlot) (rightSupport rightSlot) keyDepth atomKeyEq
      targetDeclaration restorationDepth
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    leftShape.symm rightShape.symm atomApex

/-- Structural application trees retain their outer application head under
hereditary normalization; only their argument spine is normalized. -/
theorem normalize_pattern_apply_of_structural
    {targetFree : WellSorted.FreeTypeContext} {available outer : List TypeExpr}
    {wire : String} {arguments : List Pattern} {type : TypeExpr}
    (tree : CostRegionTree rhoCIGSLT targetFree available outer
      (.apply wire arguments) type)
    (structural : tree.rootIsStatic = false) :
    ∃ normalizedArguments,
      (tree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          .apply wire normalizedArguments := by
  cases tree.structuralRootView structural with
  | neutralApplicationOrdinary _ _ _ _ _ _ children =>
      exact ⟨(children.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).patterns, by
        simp [CostRegionTree.normalize]⟩
  | neutralApplicationQuote _ _ _ _ _ _ children =>
      exact ⟨(children.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).patterns, by
        simp [CostRegionTree.normalize]⟩

theorem processBoundaryTree_normalize_apply
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (boundaryClass : plan.rootClass.IsCertifiedBoundary)
    (tree : CostRegionTree rhoCIGSLT targetFree sourceAvailable [] payload
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc"))) :
    ∃ constructor : rhoCIGSLT.DeclaredCostConstructor,
    ∃ wire normalizedArguments,
      rhoCIGSLT.renderDeclaredCostConstructor constructor = wire ∧
      rhoCIGSLT.declaredCostConstructorRole constructor ≠ .static color ∧
      (tree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          .apply wire normalizedArguments := by
  let reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      plan.abstractPattern :=
    { sourceBound := sourceBound
      targetBound := targetBound
      thinning := thinning
      sourceAvailable := sourceAvailable
      outer := outer
      sourceType := .base "Proc"
      plan := plan
      skeletonContext := .hole
      abstract_eq := rfl }
  obtain ⟨boundary⟩ :=
    reached.nonempty_boundaryView_of_boundaryClass boundaryClass
  have member : boundary.stopped.certified.typed ∈
      plan.boundaryTable.entries := by
    rw [boundary.entries_eq]
    simp
  have kind := plan.boundaryKind_of_mem_entries
    boundary.stopped.certified.typed member
  cases kind with
  | application constructor rendered outsideCurrent content =>
      rename_i wire arguments
      have payloadShape : payload = .apply wire arguments :=
        boundary.content_eq.symm.trans content
      subst payload
      have structural : tree.rootIsStatic = false := by
        by_contra notStructural
        have static : tree.rootIsStatic = true :=
          Bool.eq_true_of_not_eq_false notStructural
        obtain ⟨treeColor, view⟩ :=
          tree.staticRootView_of_rootIsStatic static
        have colorEq : treeColor = color := by
          by_contra different
          have flipEq : treeColor = color.flip :=
            CostStaticColor.eq_flip_of_ne (Ne.symm different)
          subst treeColor
          apply mapTypeExpr_flipProc_ne color.flip
            (.base view.node.sourceSort.1)
          simpa [CostStaticColor.mapLangSort_name, mapTypeExpr] using
            view.typeEq.symm
        subst treeColor
        obtain ⟨currentConstructor, decoded, current⟩ :=
          view.node.plan.application_dispatch_of_isStaticRoot
            view.node.rootStatic view.patternEq
        have currentRendered :
            rhoCIGSLT.renderDeclaredCostConstructor currentConstructor = wire :=
          rhoCIGSLT.renderDeclaredCostConstructor_eq_of_decode wire
            currentConstructor decoded
        have constructorEq : constructor = currentConstructor :=
          rhoCIGSLT.renderDeclaredCostConstructor_injective
            (rendered.trans currentRendered.symm)
        subst currentConstructor
        exact outsideCurrent current
      obtain ⟨normalizedArguments, normalized⟩ :=
        normalize_pattern_apply_of_structural tree structural
      exact ⟨constructor, wire, normalizedArguments, rendered,
        outsideCurrent, normalized⟩
  | collection currentRejected oppositeChoice oppositeSelected content =>
      exact absurd oppositeSelected (fun selected =>
        rho_boundaryCollection_choices_absurd color targetFree _ _ _ _
          selected currentRejected)

theorem boundaryPlan_commonAtom_normalized_application
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (trees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.finiteBoundaryTable
      (trees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      node.plan.abstractPattern}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {frameSourceBound frameTargetBound : List TypeExpr}
    (frameThinning : CostStaticBinderThinning rhoCIGSLT color
      frameSourceBound frameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer skeletonContext : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (rootEq : node.plan.abstractPattern =
      skeletonContext.fill plan.abstractPattern)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      plan.boundaryTable.entries node.plan.boundaryTable.entries)
    (boundaryClass : plan.rootClass.IsCertifiedBoundary)
    (scopeDepth keyDepth : Nat) :
    let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
      color rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    ∃ slot : Fin environment.atomCount,
    ∃ constructor : rhoCIGSLT.DeclaredCostConstructor,
    ∃ wire normalizedArguments,
      canonicalizeByAt key targetDeclaration keyDepth
          (cospan.reifyWith environment.lookupAtom? leg
            (frameThinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (environment.reify plan.abstractPattern)))) =
        cospan.reifyWith environment.lookupAtom? leg
          (.fvar (environment.atomName slot)) ∧
      rhoCIGSLT.renderDeclaredCostConstructor constructor = wire ∧
      rhoCIGSLT.declaredCostConstructorRole constructor ≠ .static color ∧
      (environment.atomValue slot).key.normal =
        .apply wire normalizedArguments := by
  dsimp only
  let reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      node.plan.abstractPattern :=
    { sourceBound := sourceBound
      targetBound := targetBound
      thinning := thinning
      sourceAvailable := sourceAvailable
      outer := outer
      sourceType := .base "Proc"
      plan := plan
      skeletonContext := skeletonContext
      abstract_eq := rootEq }
  obtain ⟨boundary⟩ :=
    reached.nonempty_boundaryView_of_boundaryClass boundaryClass
  have singletonEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [boundary.stopped.certified.typed]
        node.plan.boundaryTable.entries := by
    rw [← boundary.entries_eq]
    exact embedding
  obtain ⟨slot, selected⟩ := Option.isSome_iff_exists.mp
    (environment.slotOfName?_isSome_of_occurrence
      boundary.stopped.boundaryOccurrence)
  let selectedTree :=
    boundary.stopped.selectedTreeFromForest singletonEmbedding trees
  let processTree :=
    (((selectedTree.reindexAvailable boundary.targetSupport_eq).reindexPattern
      boundary.content_eq).reindexType boundary.targetType_eq)
  obtain ⟨constructor, wire, normalizedArguments, rendered, outsideCurrent,
      processNormal⟩ :=
    processBoundaryTree_normalize_apply plan boundaryClass processTree
  have processTreeNormal :
      (processTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (selectedTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    simp [processTree, CostRegionTree.reindexType_normalize,
      CostRegionTree.reindexPattern_normalize,
      CostRegionTree.reindexAvailable_normalize]
  have selectedNormal :
      (selectedTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        .apply wire normalizedArguments :=
    processTreeNormal.symm.trans processNormal
  have atomEq := boundary.stopped.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition singletonEmbedding
      trees (environment := environment) (slot := slot) selected
  have atomNormal := congrArg (fun atom => atom.key.normal) atomEq
  have atomNormalEq : (environment.atomValue slot).key.normal =
      (selectedTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    simpa only [TypedCostStaticAtom.ofBoundaryValue,
      CostRegionTree.normalizedBoundaryValue_pattern,
      rhoHereditaryNormalizationKernel] using atomNormal
  have frameShape :
      canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          keyDepth
          (cospan.reifyWith environment.lookupAtom? leg
            (frameThinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (environment.reify plan.abstractPattern)))) =
        cospan.reifyWith environment.lookupAtom? leg
          (.fvar (environment.atomName slot)) := by
    rw [boundary.abstract_eq]
    simp only [CostStaticAtomEnvironment.reify,
      CostStaticBinderThinning.thickenAmbientBVars, mapPattern]
    unfold CostStaticAtomEnvironment.reifyName
    have selected' : environment.slotOfName?
        (costRegionBoundaryVariableName
          boundary.stopped.certified.typed.boundary) = some slot := by
      simpa only [boundary.stopped.boundaryOccurrence_name] using selected
    rw [selected']
    simp [Pattern.renameFVars, canonicalizeByAt]
  exact ⟨slot, constructor, wire, normalizedArguments, frameShape, rendered,
    outsideCurrent, atomNormalEq.trans selectedNormal⟩

theorem processPlan_abstract_root_cases
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (notBoundary : ¬ plan.rootClass.IsCertifiedBoundary) :
    (∃ index, plan.abstractPattern = .bvar index) ∨
    (∃ name, plan.abstractPattern =
      .fvar (costRegionSourceVariableName name)) ∨
    (∃ constructor : rhoCIGSLT.DeclaredCostConstructor,
      ∃ sourceWire targetWire arguments,
        rhoCIGSLT.renderDeclaredCostConstructor constructor = targetWire ∧
        rhoCIGSLT.declaredCostConstructorRole constructor = .static color ∧
        targetWire = (color.symbols rhoCIGSLT).constructor sourceWire ∧
        plan.abstractPattern = .apply sourceWire arguments) ∨
    ∃ collectionType elements rest,
      plan.abstractPattern = .collection collectionType elements rest := by
  generalize sourceTypeEq : (TypeExpr.base "Proc") = sourceType at plan
  cases plan with
  | bvar sourceIndex lookup correspondence availableScope =>
      exact Or.inl ⟨sourceIndex, rfl⟩
  | fvar lookup =>
      rename_i name
      exact Or.inr (Or.inl ⟨name, rfl⟩)
  | boundaryApplication constructor rendered outsideCurrent certified
      certifies =>
      exact (notBoundary (by
        simp [CostStaticRegionPlan.rootClass,
          CostStaticPlanRootClass.IsCertifiedBoundary])).elim
  | application constructor rendered current preimage notBare children =>
      have targetWire :
          rhoCIGSLT.renderDeclaredCostConstructor constructor =
            (color.symbols rhoCIGSLT).constructor
              preimage.sourceConstructor.1.label := by
        exact (rhoCIGSLT.materializeDeclaredCostConstructor_label
          constructor).symm.trans preimage.labelMap
      exact Or.inr (Or.inr (Or.inl ⟨constructor,
        preimage.sourceConstructor.1.label,
        (color.symbols rhoCIGSLT).constructor
          preimage.sourceConstructor.1.label,
        children.abstractPatterns, targetWire, current, rfl, rfl⟩))
  | lambda bodyPlan => cases sourceTypeEq
  | multiLambda bodyPlan => cases sourceTypeEq
  | collection choice selected children =>
      exact Or.inr (Or.inr (Or.inr ⟨_, children.abstractPatterns,
        Option.map costRegionSourceVariableName _, rfl⟩))
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact (notBoundary (by
        simp [CostStaticRegionPlan.rootClass,
          CostStaticPlanRootClass.IsCertifiedBoundary])).elim

/-- After parent reification and keyed canonicalization, a non-boundary
process leaf still restores with one of the four possible non-boundary root
shapes.  In the application case the retained head is rendered by a
constructor declared static at the current colour. -/
theorem nonBoundaryPlan_commonFrame_restored_root_cases
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      table values root}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {frameSourceBound frameTargetBound : List TypeExpr}
    (frameThinning : CostStaticBinderThinning rhoCIGSLT color
      frameSourceBound frameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (legCommutes : ∀ slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer skeletonContext : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (rootEq : root = skeletonContext.fill plan.abstractPattern)
    (notBoundary : ¬ plan.rootClass.IsCertifiedBoundary)
    (stable : plan.abstractPattern ≠
        .apply rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor [] ∧
      (∀ elements, plan.abstractPattern ≠
        .collection rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
          elements none) ∧
      ∀ arguments, plan.abstractPattern ≠
        .apply rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor
          arguments)
    (scopeDepth keyDepth : Nat) :
    let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
      color rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    let endpoint := canonicalizeByAt key targetDeclaration keyDepth
      (cospan.reifyWith environment.lookupAtom? leg
        (frameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (environment.reify plan.abstractPattern))))
    let restored := ReflectiveContextSupport.substituteAt
      rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment keyDepth endpoint
    (∃ index, restored = .bvar index) ∨
    (∃ name, restored = .fvar name) ∨
    (∃ constructor : rhoCIGSLT.DeclaredCostConstructor,
      ∃ wire arguments,
        rhoCIGSLT.renderDeclaredCostConstructor constructor = wire ∧
        rhoCIGSLT.declaredCostConstructorRole constructor = .static color ∧
        restored = .apply wire arguments) ∨
    ∃ collectionType elements rest,
      restored = .collection collectionType elements rest := by
  dsimp only
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let frame := fun pattern =>
    cospan.reifyWith environment.lookupAtom? leg
      (frameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (environment.reify pattern)))
  let endpoint := canonicalizeByAt key targetDeclaration keyDepth
    (frame plan.abstractPattern)
  let restored := ReflectiveContextSupport.substituteAt
    rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
      cospan.commonAssignment keyDepth endpoint
  change (∃ index, restored = .bvar index) ∨
    (∃ name, restored = .fvar name) ∨
    (∃ constructor : rhoCIGSLT.DeclaredCostConstructor,
      ∃ wire arguments,
        rhoCIGSLT.renderDeclaredCostConstructor constructor = wire ∧
        rhoCIGSLT.declaredCostConstructorRole constructor = .static color ∧
        restored = .apply wire arguments) ∨
    ∃ collectionType elements rest,
      restored = .collection collectionType elements rest
  have framedStable := commonReifiedMappedThickened_root_stable environment
    frameThinning cospan leg scopeDepth plan.abstractPattern stable
  change frame plan.abstractPattern ≠
        .apply targetDeclaration.parallelUnitConstructor [] ∧
      (∀ elements, frame plan.abstractPattern ≠
        .collection targetDeclaration.parallelCollection elements none) ∧
      ∀ arguments, frame plan.abstractPattern ≠
        .apply targetDeclaration.quoteConstructor arguments at framedStable
  rcases processPlan_abstract_root_cases plan notBoundary with
      ⟨index, abstractEq⟩ | ⟨name, abstractEq⟩ |
      ⟨constructor, sourceWire, targetWire, arguments, rendered, current,
        targetWireEq, abstractEq⟩ |
      ⟨collectionType, elements, rest, abstractEq⟩
  · left
    refine ⟨frameThinning.embedIndexAt scopeDepth index, ?_⟩
    have frameShape : frame plan.abstractPattern =
        .bvar (frameThinning.embedIndexAt scopeDepth index) := by
      rw [abstractEq]
      simp only [frame, cospan.reifyWith_eq_renameFVars,
        environment.reify_eq_renameFVars, Pattern.renameFVars, mapPattern,
        CostStaticBinderThinning.thickenAmbientBVars]
    dsimp only [restored, endpoint]
    rw [frameShape]
    simp only [canonicalizeByAt,
      ReflectiveContextSupport.substituteAt]
  · right; left
    have rootFill : root = skeletonContext.fill
        (.fvar (costRegionSourceVariableName name)) := by
      rw [← abstractEq]
      exact rootEq
    let occurrence : CostStaticFVarOccurrence root :=
      { name := costRegionSourceVariableName name
        context := skeletonContext
        selected := by
          rw [rootFill]
          exact Selects.of_fill _ _ }
    obtain ⟨slot, selected⟩ := Option.isSome_iff_exists.mp
      (environment.slotOfName?_isSome_of_occurrence occurrence)
    have selectedAtName : environment.slotOfName?
        (costRegionSourceVariableName name) = some slot := by
      simpa only [occurrence] using selected
    have frameShape : frame plan.abstractPattern =
        .fvar (cospan.commonAtomName (leg slot)) := by
      rw [abstractEq]
      simp [frame,
        Pattern.renameFVars, mapPattern,
        CostStaticBinderThinning.thickenAmbientBVars,
        CostStaticAtomEnvironment.reifyName, selectedAtName,
        CostStaticAtomKeyCospan.reifyNameWith,
        CostStaticAtomEnvironment.lookupAtom?_atomName]
    refine ⟨name, ?_⟩
    dsimp only [restored, endpoint]
    rw [frameShape]
    simp only [canonicalizeByAt,
      ReflectiveContextSupport.substituteAt,
      CostStaticAtomKeyCospan.commonAssignment_commonAtomName,
      CostStaticAtomKeyCospan.commonSupport_commonAtomName]
    rw [legCommutes slot]
    rw [environment.atomValue_normal_eq_of_slotOfName?_eq_some
      occurrence slot selected]
    have assignmentEq : values.assignment table occurrence.name =
        .fvar name := by
      simpa only [occurrence] using values.assignment_sourceVariable name
    rw [assignmentEq]
    simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]
  · right; right; left
    obtain ⟨framedArguments, frameShape⟩ : ∃ framedArguments,
        frame plan.abstractPattern = .apply targetWire framedArguments := by
      rw [abstractEq]
      rw [show targetWire = (color.symbols rhoCIGSLT).constructor sourceWire
        from targetWireEq]
      simp [frame, Pattern.renameFVars, mapPattern,
        mapPatternList_eq_map,
        CostStaticBinderThinning.thickenAmbientBVars]
    have notQuote : targetWire ≠ targetDeclaration.quoteConstructor := by
      intro equality
      apply framedStable.2.2 framedArguments
      rw [frameShape, equality]
    let childDepth := if ReflectiveContextSupport.isQuoteConstructor
        rhoCIGSLT.costWholeReflectionProfile targetWire then 0 else keyDepth
    let normalizedArguments := canonicalizeListByAt key targetDeclaration
      keyDepth framedArguments
    let restoredArguments := normalizedArguments.map
      (ReflectiveContextSupport.substituteAt
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment childDepth)
    refine ⟨constructor, targetWire, restoredArguments, rendered, current, ?_⟩
    dsimp only [restored, endpoint]
    rw [frameShape]
    simp [canonicalizeByAt,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
      notQuote,
      restoredArguments, normalizedArguments, childDepth,
      ReflectiveContextSupport.substituteAt]
  · right; right; right
    obtain ⟨framedElements, frameShape⟩ : ∃ framedElements,
        frame plan.abstractPattern =
          .collection collectionType framedElements rest := by
      rw [abstractEq]
      simp [frame, Pattern.renameFVars, mapPattern,
        mapPatternList_eq_map,
        CostStaticBinderThinning.thickenAmbientBVars]
    dsimp only [restored, endpoint]
    rw [frameShape]
    by_cases restNone : rest = none
    · subst rest
      have notParallel : collectionType ≠ targetDeclaration.parallelCollection := by
        intro equality
        apply framedStable.2.1 framedElements
        rw [frameShape, equality]
      let normalizedElements := canonicalizeListByAt key targetDeclaration
        keyDepth framedElements
      let restoredElements := normalizedElements.map
        (ReflectiveContextSupport.substituteAt
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment keyDepth)
      refine ⟨collectionType, restoredElements, none, ?_⟩
      simp [canonicalizeByAt, notParallel,
        restoredElements, normalizedElements,
        ReflectiveContextSupport.substituteAt]
    · let normalizedElements := canonicalizeListByAt key targetDeclaration
        keyDepth framedElements
      let restoredElements := normalizedElements.map
        (ReflectiveContextSupport.substituteAt
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment keyDepth)
      refine ⟨collectionType, restoredElements, rest, ?_⟩
      simp [canonicalizeByAt,
        restoredElements, normalizedElements,
        ReflectiveContextSupport.substituteAt]

/-- A certified process boundary and a non-boundary process leaf cannot tie
under the common semantic ordering key.  The boundary restores to an
application headed by an outside-current declared constructor, whereas every
non-boundary root is rigid, an authored source variable, a current
application, or a collection. -/
theorem boundaryPlan_commonSemanticKey_ne_nonBoundaryPlan
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (leftNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.finiteBoundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.plan.abstractPattern}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    {rightOccurrences : List CostRegionOccurrence}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightTable}
    {rightRoot : Pattern}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable rightValues rightRoot}
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftFrameSourceBound leftFrameTargetBound : List TypeExpr}
    {rightFrameSourceBound rightFrameTargetBound : List TypeExpr}
    (leftFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      leftFrameSourceBound leftFrameTargetBound)
    (rightFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      rightFrameSourceBound rightFrameTargetBound)
    {leftSourceBound leftTargetBound rightSourceBound rightTargetBound :
      List TypeExpr}
    {leftThinning : CostStaticBinderThinning rhoCIGSLT color leftSourceBound
      leftTargetBound}
    {rightThinning : CostStaticBinderThinning rhoCIGSLT color rightSourceBound
      rightTargetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter leftContext rightContext : OneHoleContext}
    {leftPayload rightPayload : Pattern}
    (leftPlan : CostStaticRegionPlan rhoCIGSLT color targetFree leftSourceBound
      leftTargetBound leftThinning leftAvailable leftOuter leftPayload
      (.base "Proc"))
    (rightPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
      rightSourceBound rightTargetBound rightThinning rightAvailable rightOuter
      rightPayload (.base "Proc"))
    (leftRootEq : leftNode.plan.abstractPattern =
      leftContext.fill leftPlan.abstractPattern)
    (rightRootEq : rightRoot = rightContext.fill rightPlan.abstractPattern)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftPlan.boundaryTable.entries leftNode.plan.boundaryTable.entries)
    (leftBoundary : leftPlan.rootClass.IsCertifiedBoundary)
    (rightNotBoundary : ¬ rightPlan.rootClass.IsCertifiedBoundary)
    (rightStable : rightPlan.abstractPattern ≠
        .apply rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor [] ∧
      (∀ elements, rightPlan.abstractPattern ≠
        .collection rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
          elements none) ∧
      ∀ arguments, rightPlan.abstractPattern ≠
        .apply rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor
          arguments)
    (scopeDepth keyDepth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
      color rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    let leftEndpoint := canonicalizeByAt key targetDeclaration keyDepth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftFrameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (leftEnvironment.reify leftPlan.abstractPattern))))
    let rightEndpoint := canonicalizeByAt key targetDeclaration keyDepth
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightFrameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (rightEnvironment.reify rightPlan.abstractPattern))))
    key keyDepth leftEndpoint ≠ key keyDepth rightEndpoint := by
  dsimp only
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let leftEndpoint := canonicalizeByAt key targetDeclaration keyDepth
    (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
      (leftFrameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (leftEnvironment.reify leftPlan.abstractPattern))))
  let rightEndpoint := canonicalizeByAt key targetDeclaration keyDepth
    (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
      (rightFrameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (rightEnvironment.reify rightPlan.abstractPattern))))
  change key keyDepth leftEndpoint ≠ key keyDepth rightEndpoint
  obtain ⟨leftSlot, boundaryConstructor, boundaryWire,
      boundaryArguments, leftShape, boundaryRendered, boundaryOutside,
      boundaryNormal⟩ :=
    boundaryPlan_commonAtom_normalized_application leftNode leftTrees
      leftEnvironment leftFrameThinning cospan cospan.leftSlot leftPlan
      leftRootEq leftEmbedding leftBoundary scopeDepth keyDepth
  have leftRestoredShape : ∃ restoredArguments,
      ReflectiveContextSupport.substituteAt
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment keyDepth leftEndpoint =
        .apply boundaryWire restoredArguments := by
    let shift := keyDepth -
      (leftEnvironment.atomValue leftSlot).key.targetSupport.length
    let restoredArguments := boundaryArguments.map
      (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 shift)
    refine ⟨restoredArguments, ?_⟩
    dsimp only [leftEndpoint]
    rw [leftShape]
    simp only [CostStaticAtomKeyCospan.reifyWith,
      CostStaticAtomEnvironment.lookupAtom?_atomName,
      ReflectiveContextSupport.substituteAt,
      CostStaticAtomKeyCospan.commonAssignment_commonAtomName,
      CostStaticAtomKeyCospan.commonSupport_commonAtomName]
    rw [cospan.leftCommutes leftSlot, boundaryNormal]
    simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars,
      restoredArguments, shift]
  have rightCases := nonBoundaryPlan_commonFrame_restored_root_cases
    rightEnvironment rightFrameThinning cospan cospan.rightSlot
      cospan.rightCommutes rightPlan rightRootEq rightNotBoundary rightStable
      scopeDepth keyDepth
  intro keyEq
  have restoredEq :=
    (cospan.commonSemanticPatternKeyAt_eq_iff rhoCIGSLT keyDepth
      leftEndpoint rightEndpoint).mp keyEq
  obtain ⟨leftRestoredArguments, leftRestored⟩ := leftRestoredShape
  rcases rightCases with ⟨index, rightRestored⟩ |
      ⟨name, rightRestored⟩ |
      ⟨rightConstructor, rightWire, rightArguments, rightRendered,
        rightCurrent, rightRestored⟩ |
      ⟨collectionType, elements, rest, rightRestored⟩
  · rw [leftRestored, rightRestored] at restoredEq
    cases restoredEq
  · rw [leftRestored, rightRestored] at restoredEq
    cases restoredEq
  · rw [leftRestored, rightRestored] at restoredEq
    have wireEq : boundaryWire = rightWire :=
      (Pattern.apply.inj restoredEq).1
    have constructorEq : boundaryConstructor = rightConstructor :=
      rhoCIGSLT.renderDeclaredCostConstructor_injective
        (boundaryRendered.trans (wireEq.trans rightRendered.symm))
    subst rightConstructor
    exact boundaryOutside rightCurrent
  · rw [leftRestored, rightRestored] at restoredEq
    cases restoredEq

end ParallelFrontierCrossTies
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
