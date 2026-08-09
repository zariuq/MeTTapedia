import Mettapedia.GSLT.LanguageDef.CostStaticPlanOccurrenceCoverage
import Mettapedia.GSLT.LanguageDef.CostHereditaryTransportAtoms
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary

/-!
# Paired context-view canaries over the rho breadth fixtures

The endpoint-pair scaffold is exercised against the actual generated rho Cost
language:

- a genuine cell-level edge for the base Quote/Drop collapse, paired
  reached/reached at the root and through the quote frame (availability
  reset travels through the plan indices);
- a boundary-carrying edge whose stopped pair retains the certified
  boundary at its exact endpoint position and exhibits the source pullback;
- the breadth witness represented as a two-cell family, one cell per changed
  sibling;
- duplication and discard as honest finite occurrence maps over a rho
  boundary, and the no-creation emptiness at the actual edge interface;
- repeated equal typed entries retaining distinct replayable positions;
- the negative spelling lemma showing why a changed boundary content admits
  no decoration-level reflective witness: the content-keyed boundary
  variable and the retagged source variable can never canonicalize equally,
  so a stopped cell must close at the restoration apex rather than at the
  skeleton.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanPairCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary

/-! ## The collapsed endpoint plan and the source-language collapse witness -/

/-- Collapsed endpoint of the base Quote/Drop cell: the plain free name. -/
def rhoPairFvarAPlan :
    CostStaticRegionPlan rhoCIGSLT .base rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] .hole (.fvar "a") (.base "Name") :=
  .fvar (by
    simp [rhoCutOrderFree, FreeTypeContext.ofList, mapTypeExpr,
      CostStaticColor.symbols, costBaseStaticSymbols,
      costBasePresentationSymbols])

theorem rhoPairSourceReflectiveDecl_mem :
    rhoReflectivePresentation.toReflectivePresentationDecl ∈
      rhoCIGSLT.reflection.1.presentations := by
  change rhoReflectivePresentation.toReflectivePresentationDecl ∈
    ReflectionExtension.rhoReflectionProfile.presentations
  simp [ReflectionExtension.rhoReflectionProfile]

/-- The base Quote/Drop collapse as a source-language reflective occurrence
between the two decoration skeletons. -/
def rhoPairCollapseWitness :
    ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.reflection.1 defaultBasePremises
      rhoCIGSLT.theory.presentation.presentation.language
      rhoBreadthBaseRedexAPlan.decoration.abstractPattern
      rhoPairFvarAPlan.decoration.abstractPattern := by
  refine ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness.reflective .hole
    ⟨rhoReflectivePresentation.toReflectivePresentationDecl,
      rhoPairSourceReflectiveDecl_mem⟩ ?_
  have leftEq : rhoBreadthBaseRedexAPlan.decoration.abstractPattern =
      .apply "NQuote" [.apply "PDrop"
        [.fvar (costRegionSourceVariableName "a")]] := by
    unfold rhoBreadthBaseRedexAPlan rhoBreadthBaseDropAPlan
      rhoBreadthBaseFvarAPlan
    simp [CostStaticRegionPlan.decoration,
      CostStaticArgumentPlan.decorations,
      CostStaticPlanDecoration.abstractPattern,
      CostStaticPlanDecorationNode.abstractPattern,
      rhoBreadthBaseQuotePreimage, rhoBreadthBaseDropPreimage,
      costStaticConstructorPreimage, rhoBreadthBaseQuoteDeclared,
      rhoBreadthBaseDropDeclared, rhoCalc]
  have rightEq : rhoPairFvarAPlan.decoration.abstractPattern =
      .fvar (costRegionSourceVariableName "a") := by
    simp [rhoPairFvarAPlan, CostStaticRegionPlan.decoration,
      CostStaticPlanDecoration.abstractPattern,
      CostStaticPlanDecorationNode.abstractPattern]
  rw [leftEq, rightEq]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
    rhoReflectivePresentation]

/-! ## Cell-level edge for the base collapse (empty boundary inventories) -/

/-- The base Quote/Drop collapse as a lawful static-plan edge.  Both endpoint
regions are boundary-free, so the occurrence pullback is the identity of the
empty inventory; every source choice sits inside the reflective redex. -/
def rhoPairCollapseEdge :
    CostStaticPlanEdge rhoCIGSLT rhoBreadthBaseRedexAPlan.decoration
      rhoPairFvarAPlan.decoration [] [] where
  sameFiber := ⟨rfl, rfl, rfl, rfl, rfl⟩
  generatorWitness := rhoPairCollapseWitness
  sourceBoundaryInventory := rfl
  targetBoundaryInventory := rfl
  boundaryOrigins := CostBoundaryFiberMap.identity []
  choiceOrigins :=
    { origin := fun _index => none
      preservesFiber := fun _target _source impossible => nomatch impossible }
  introducedChoice := fun targetIndex _origin =>
    ((show rhoPairFvarAPlan.decoration.choiceOccurrences = [] from rfl) ▸
      targetIndex).elim0
  sourceContextChoiceCovered := fun _sourceIndex notInRedex =>
    absurd ⟨_, rfl⟩ notInRedex
  boundaryChoiceCoherent := fun targetIndex => targetIndex.elim0

/-- Paired reached/reached views at the collapse roots. -/
theorem rhoPair_collapse_pair_root :
    Nonempty (CostStaticPlanContextPair rhoCIGSLT .base rhoCutOrderFree
      rhoPairCollapseEdge rhoBreadthRedexA (.fvar "a")
      rhoBreadthBaseRedexAPlan.abstractPattern
      rhoPairFvarAPlan.abstractPattern
      rhoBreadthBaseRedexAPlan.boundaryTable.entries
      rhoPairFvarAPlan.boundaryTable.entries) :=
  rhoPairCollapseEdge.nonempty_contextPair rhoBreadthBaseRedexAPlan
    rhoPairFvarAPlan rfl rfl .hole .hole rfl rfl

/-- Quote-reset configuration: the left view descends through the quote
frame, whose plan spine resets the reflective availability index, while the
right view stays at the collapsed root.  The pair exists with different
context shapes on the two endpoints. -/
theorem rhoPair_collapse_pair_quoteReset :
    Nonempty (CostStaticPlanContextPair rhoCIGSLT .base rhoCutOrderFree
      rhoPairCollapseEdge (rhoCutOrderBaseDrop (.fvar "a")) (.fvar "a")
      rhoBreadthBaseRedexAPlan.abstractPattern
      rhoPairFvarAPlan.abstractPattern
      rhoBreadthBaseRedexAPlan.boundaryTable.entries
      rhoPairFvarAPlan.boundaryTable.entries) :=
  rhoPairCollapseEdge.nonempty_contextPair rhoBreadthBaseRedexAPlan
    rhoPairFvarAPlan rfl rfl
    (.apply (costBaseConstructorName "NQuote") [] .hole []) .hole rfl rfl

/-! ## Boundary-carrying edge and the stopped pair with pullback -/

/-- Inessential recursive decoration attached to the boundary occurrence in
the finite edge inventories; only the boundary component is constrained by
the edge laws. -/
def rhoPairTreeDecoration : CostTreeDecoration rhoCIGSLT :=
  .mk [] [] (.fvar "x") (.base "Name") .fvar

/-- The wrapped left sibling's certified boundary as an edge-inventory
occurrence. -/
noncomputable def rhoPairBoundaryEntry :
    CostRegionBoundary × CostTreeDecoration rhoCIGSLT :=
  (rhoBreadthBoundaryWitnessA.typed.boundary, rhoPairTreeDecoration)

/-- A lawful edge on the wrapped left sibling whose inventories carry the
certified boundary on both endpoints.  The generator is the reflexive
reflective occurrence; the boundary pullback is the identity of the
singleton inventory. -/
noncomputable def rhoPairBoundaryEdge :
    CostStaticPlanEdge rhoCIGSLT rhoBreadthLeftProcessPlan.decoration
      rhoBreadthLeftProcessPlan.decoration [rhoPairBoundaryEntry]
      [rhoPairBoundaryEntry] where
  sameFiber := ⟨rfl, rfl, rfl, rfl, rfl⟩
  generatorWitness := .reflective .hole
    ⟨rhoReflectivePresentation.toReflectivePresentationDecl,
      rhoPairSourceReflectiveDecl_mem⟩ rfl
  sourceBoundaryInventory := rfl
  targetBoundaryInventory := rfl
  boundaryOrigins := CostBoundaryFiberMap.identity [rhoPairBoundaryEntry]
  choiceOrigins :=
    { origin := fun index => some index
      preservesFiber := fun _target _source someEq => by
        cases Option.some.inj someEq
        exact CostStaticChoiceOccurrence.sameFiber_refl _ }
  introducedChoice := fun _targetIndex impossible => nomatch impossible
  sourceContextChoiceCovered := fun sourceIndex _notInRedex =>
    ⟨sourceIndex, rfl, rfl⟩
  boundaryChoiceCoherent := fun targetIndex =>
    ⟨⟨1, by decide⟩, ⟨1, by decide⟩, by
      rcases targetIndex with ⟨_ | _, inBounds⟩
      · exact rfl
      · exact absurd inBounds (by simp), rfl, by
      rcases targetIndex with ⟨_ | _, inBounds⟩
      · exact rfl
      · exact absurd inBounds (by simp)⟩

/-- The stopped inventory view of the wrapped left sibling, retained with
its replayable singleton embedding. -/
noncomputable def rhoPairStoppedView :
    CostStaticPlanContextInventoryView rhoCIGSLT .wrapped rhoCutOrderFree
      (rhoCutOrderBaseDrop (.fvar "a"))
      rhoBreadthLeftProcessPlan.abstractPattern
      rhoBreadthLeftProcessPlan.boundaryTable.entries where
  view := .stopped
    { boundarySupport := []
      boundaryType := _
      content := rhoBreadthRedexA
      certified := rhoBreadthBoundaryWitnessA
      residual := .apply (costBaseConstructorName "NQuote") [] .hole []
      content_eq := rfl
      skeletonContext := .apply "PDrop" [] .hole []
      abstract_eq := rfl }
  entryEmbedding := .keep (.nil [])

/-- The stopped endpoint pair over the boundary-carrying edge: both
endpoint views stop at the certified boundary at its exact retained
position. -/
noncomputable def rhoPairStoppedPair :
    CostStaticPlanContextPair rhoCIGSLT .wrapped rhoCutOrderFree
      rhoPairBoundaryEdge (rhoCutOrderBaseDrop (.fvar "a"))
      (rhoCutOrderBaseDrop (.fvar "a"))
      rhoBreadthLeftProcessPlan.abstractPattern
      rhoBreadthLeftProcessPlan.abstractPattern
      rhoBreadthLeftProcessPlan.boundaryTable.entries
      rhoBreadthLeftProcessPlan.boundaryTable.entries where
  left := rhoPairStoppedView
  right := rhoPairStoppedView
  leftRoot_eq := rhoBreadthLeftProcessPlan.decoration_abstractPattern
  rightRoot_eq := rhoBreadthLeftProcessPlan.decoration_abstractPattern
  leftTable_eq := rfl
  rightTable_eq := rfl

/-- The stopped boundary is retained at position zero of the endpoint
inventory and pulls back to position zero of the source inventory. -/
theorem rhoPair_stopped_pullback :
    rhoPairStoppedPair.selectedPullback ⟨0, by decide⟩ =
      ⟨0, by decide⟩ := rfl

/-- The exhibited pullback stays in the exact type/support fibre of the
retained boundary. -/
theorem rhoPair_stopped_pullback_sameFiber :
    CostRegionBoundary.SameFiber
      ([rhoPairBoundaryEntry].get
        (rhoPairStoppedPair.selectedPullback ⟨0, by decide⟩)).1
      ((rhoPairStoppedPair.right.view.retainedEntries.get
        ⟨0, by decide⟩)).boundary :=
  rhoPairStoppedPair.selectedPullback_sameFiber ⟨0, by decide⟩

/-- The full-inventory pullback recovers the fixture's certified source
boundary exactly. -/
theorem rhoPair_stopped_selectedSourceEntry_eq :
    rhoPairStoppedPair.selectedSourceEntry ⟨0, by decide⟩ =
      rhoBreadthBoundaryWitnessA.typed := by
  apply TypedCostRegionBoundary.ext
  rfl

/-- The retained target entry is the same certified fixture boundary. -/
theorem rhoPair_stopped_selectedTargetEntry_eq :
    rhoPairStoppedPair.right.view.retainedEntries.get ⟨0, by decide⟩ =
      rhoBreadthBoundaryWitnessA.typed := by
  apply TypedCostRegionBoundary.ext
  rfl

/-- The known recursive source child, transported to the exact full-inventory
entry selected by the nonlinear pullback. -/
noncomputable def rhoPairStoppedSourceTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree
      (rhoPairStoppedPair.selectedSourceEntry ⟨0, by decide⟩).boundary.targetSupport
      []
      (rhoPairStoppedPair.selectedSourceEntry ⟨0, by decide⟩).boundary.content
      (rhoPairStoppedPair.selectedSourceEntry ⟨0, by decide⟩).boundary.targetType :=
  rhoBreadthBoundaryChildA.reindexBoundary
    rhoPair_stopped_selectedSourceEntry_eq.symm

/-- The same known child, transported to the exact retained target entry. -/
noncomputable def rhoPairStoppedTargetTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree
      (rhoPairStoppedPair.right.view.retainedEntries.get
        ⟨0, by decide⟩).boundary.targetSupport []
      (rhoPairStoppedPair.right.view.retainedEntries.get
        ⟨0, by decide⟩).boundary.content
      (rhoPairStoppedPair.right.view.retainedEntries.get
        ⟨0, by decide⟩).boundary.targetType :=
  rhoBreadthBoundaryChildA.reindexBoundary
    rhoPair_stopped_selectedTargetEntry_eq.symm

/-- The transported stopped-site children remain hereditarily aligned. -/
noncomputable def rhoPairStoppedChildrenAlignment :
    CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
      rhoPairStoppedSourceTree rhoPairStoppedTargetTree :=
  CostRegionTreeNormalizationAlignment.reindexBoundaries
    rhoPair_stopped_selectedSourceEntry_eq.symm
    rhoPair_stopped_selectedTargetEntry_eq.symm
    (.refl rhoBreadthBoundaryChildA)

/-- The generic full-table selectors recover aligned recursive children for
the stopped singleton pair.  This exercises the position casts used by the
restoration joint rather than supplying hand-reindexed trees beside it. -/
noncomputable def rhoPairStoppedForestChildrenAlignment :
    CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
      (rhoPairStoppedPair.selectedSourceTreeFromForest
        rhoBreadthLeftProcessChildren ⟨0, by decide⟩)
      (rhoPairStoppedPair.selectedTargetTreeFromForest
        rhoBreadthLeftProcessChildren ⟨0, by decide⟩) := by
  exact .refl _

/-- The full-inventory pullback selects the actual typed source entry, and a
recursive child alignment turns its same-fibre law into semantic-atom
equality.  This is the positive stopped-site joint needed by restoration
closure. -/
theorem rhoPair_stopped_selectedSourceAtom_eq :
    TypedCostStaticAtom.ofBoundaryValue
        (rhoPairStoppedPair.selectedSourceEntry ⟨0, by decide⟩)
        (rhoPairStoppedSourceTree.normalizedBoundaryValue
          rhoHereditaryNormalizationKernel) =
      TypedCostStaticAtom.ofBoundaryValue
        (rhoPairStoppedPair.right.view.retainedEntries.get ⟨0, by decide⟩)
        (rhoPairStoppedTargetTree.normalizedBoundaryValue
          rhoHereditaryNormalizationKernel) :=
  rhoPairStoppedPair.alignedSelectedSourceAtom_eq ⟨0, by decide⟩
    rhoPairStoppedSourceTree rhoPairStoppedTargetTree
    rhoPairStoppedChildrenAlignment

/-- The normalized value vector of the actual wrapped child realizes that
proof-relevant child as a semantic atom through finite name lookup.  This is
the concrete rho instance of the generic child-to-environment joint. -/
theorem rhoPair_leftProcessChildren_resolveAtom :
    ∀ index : Fin rhoBreadthLeftProcessChildren.decorations.length,
      ∃ resolved : TypedCostRegionBoundaryTable.Values.Resolved rhoCIGSLT
          .wrapped rhoCutOrderFree,
        (rhoBreadthLeftProcessChildren.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer)).resolve
              rhoBreadthLeftProcessNode.finiteBoundaryTable
              (costRegionBoundaryVariableName
                (rhoBreadthLeftProcessChildren.getDecoration
                  index).boundary.boundary) = some resolved ∧
          TypedCostStaticAtom.ofBoundaryValue resolved.1 resolved.2 =
            TypedCostStaticAtom.ofBoundaryValue
              (rhoBreadthLeftProcessChildren.getDecoration index).boundary
              ((rhoBreadthLeftProcessChildren.getDecoration
                index).tree.normalizedBoundaryValue
                  rhoHereditaryNormalizationKernel) :=
  CostRegionBoundaryTrees.exists_resolve_normalizedAtom_eq_getDecoration
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition
    rhoBreadthLeftProcessChildren

/-- Child-normalized values and the two independently exposed views of the
same proof-relevant parent atom environment.  Keeping both views lets the
canary exercise the generic cross-environment stopped-site theorem rather
than closing by reflexivity. -/
noncomputable def rhoPairStoppedValues :=
  rhoBreadthLeftProcessChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)

noncomputable def rhoPairStoppedPackedEnvironment :=
  rhoBreadthLeftProcessNode.semanticAtomEnvironment rhoPairStoppedValues

noncomputable def rhoPairStoppedLeftEnvironment :=
  rhoPairStoppedPackedEnvironment.2

noncomputable def rhoPairStoppedRightEnvironment :=
  CostStaticAtomEnvironment.ofInventory rhoPairStoppedPackedEnvironment.1

/-- Positive stopped-site canary for the complete joint.  Exact finite-table
positions select the recursive children, child alignment identifies their
semantic atoms, and the two parent environments consequently expose equal
atom values at the certified boundary name. -/
theorem rhoPair_stopped_selectedEnvironmentAtoms_eq :
    ∃ (leftOccurrence : CostStaticFVarOccurrence
          rhoBreadthLeftProcessNode.skeleton.1)
      (leftSlot : Fin rhoPairStoppedLeftEnvironment.atomCount)
      (rightOccurrence : CostStaticFVarOccurrence
          rhoBreadthLeftProcessNode.skeleton.1)
      (rightSlot : Fin rhoPairStoppedRightEnvironment.atomCount),
      leftOccurrence.name = costRegionBoundaryVariableName
          (rhoPairStoppedPair.selectedSourceEntry ⟨0, by decide⟩).boundary ∧
      rhoPairStoppedLeftEnvironment.slotOfName? leftOccurrence.name =
          some leftSlot ∧
      rightOccurrence.name = costRegionBoundaryVariableName
          (rhoPairStoppedPair.right.view.retainedEntries.get
            ⟨0, by decide⟩).boundary ∧
      rhoPairStoppedRightEnvironment.slotOfName? rightOccurrence.name =
          some rightSlot ∧
      rhoPairStoppedLeftEnvironment.atomValue leftSlot =
        rhoPairStoppedRightEnvironment.atomValue rightSlot := by
  have membership : costRegionBoundaryVariableName
      rhoBreadthBoundaryWitnessA.typed.boundary ∈
        rhoBreadthLeftProcessNode.skeleton.1.freeFvarNames := by
    rw [rhoBreadthLeftProcessNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  obtain ⟨leftOccurrence, leftOccurrenceName⟩ :=
    rhoBreadthLeftProcessNode.skeleton_fvar_covered _ membership
  obtain ⟨rightOccurrence, rightOccurrenceName⟩ :=
    rhoBreadthLeftProcessNode.skeleton_fvar_covered _ membership
  obtain ⟨leftSlot, leftSelected⟩ := Option.isSome_iff_exists.mp
    (rhoPairStoppedLeftEnvironment.slotOfName?_isSome_of_occurrence
      leftOccurrence)
  obtain ⟨rightSlot, rightSelected⟩ := Option.isSome_iff_exists.mp
    (rhoPairStoppedRightEnvironment.slotOfName?_isSome_of_occurrence
      rightOccurrence)
  have leftNameEq : leftOccurrence.name = costRegionBoundaryVariableName
      (rhoPairStoppedPair.selectedSourceEntry ⟨0, by decide⟩).boundary := by
    rw [rhoPair_stopped_selectedSourceEntry_eq]
    exact leftOccurrenceName
  have rightNameEq : rightOccurrence.name = costRegionBoundaryVariableName
      (rhoPairStoppedPair.right.view.retainedEntries.get
        ⟨0, by decide⟩).boundary := by
    rw [rhoPair_stopped_selectedTargetEntry_eq]
    exact rightOccurrenceName
  refine ⟨leftOccurrence, leftSlot, rightOccurrence, rightSlot,
    leftNameEq, leftSelected, rightNameEq, rightSelected, ?_⟩
  exact rhoPairStoppedPair.selectedEnvironmentAtom_eq
    CostCanonicalLaws.rho_unambiguousStaticDecomposition
    rhoBreadthLeftProcessChildren rhoBreadthLeftProcessChildren
    rhoPairStoppedLeftEnvironment rhoPairStoppedRightEnvironment
    ⟨0, by decide⟩ leftOccurrence leftNameEq rightOccurrence rightNameEq
    leftSlot leftSelected rightSlot rightSelected
    rhoPairStoppedForestChildrenAlignment

/-- The same stopped-site canary through the common restoration apex.  The
two atom names are local to independently constructed parent environments;
the theorem states that their restored meanings nevertheless agree at every
binder depth. -/
theorem rhoPair_stopped_exists_restoring_atom_names :
    ∃ (leftSlot : Fin rhoPairStoppedLeftEnvironment.atomCount)
      (rightSlot : Fin rhoPairStoppedRightEnvironment.atomCount),
      let cospan := rhoPairStoppedLeftEnvironment.semanticKeyCospan
        rhoPairStoppedRightEnvironment
      ∀ depth,
        ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment depth
            (cospan.reifyWith rhoPairStoppedLeftEnvironment.lookupAtom?
              cospan.leftSlot
              (.fvar (rhoPairStoppedLeftEnvironment.atomName leftSlot))) =
          ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment depth
            (cospan.reifyWith rhoPairStoppedRightEnvironment.lookupAtom?
              cospan.rightSlot
              (.fvar (rhoPairStoppedRightEnvironment.atomName rightSlot))) := by
  have membership : costRegionBoundaryVariableName
      rhoBreadthBoundaryWitnessA.typed.boundary ∈
        rhoBreadthLeftProcessNode.skeleton.1.freeFvarNames := by
    rw [rhoBreadthLeftProcessNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  obtain ⟨leftOccurrence, leftOccurrenceName⟩ :=
    rhoBreadthLeftProcessNode.skeleton_fvar_covered _ membership
  obtain ⟨rightOccurrence, rightOccurrenceName⟩ :=
    rhoBreadthLeftProcessNode.skeleton_fvar_covered _ membership
  obtain ⟨leftSlot, leftSelected⟩ := Option.isSome_iff_exists.mp
    (rhoPairStoppedLeftEnvironment.slotOfName?_isSome_of_occurrence
      leftOccurrence)
  obtain ⟨rightSlot, rightSelected⟩ := Option.isSome_iff_exists.mp
    (rhoPairStoppedRightEnvironment.slotOfName?_isSome_of_occurrence
      rightOccurrence)
  have leftNameEq : leftOccurrence.name = costRegionBoundaryVariableName
      (rhoPairStoppedPair.selectedSourceEntry ⟨0, by decide⟩).boundary := by
    rw [rhoPair_stopped_selectedSourceEntry_eq]
    exact leftOccurrenceName
  have rightNameEq : rightOccurrence.name = costRegionBoundaryVariableName
      (rhoPairStoppedPair.right.view.retainedEntries.get
        ⟨0, by decide⟩).boundary := by
    rw [rhoPair_stopped_selectedTargetEntry_eq]
    exact rightOccurrenceName
  refine ⟨leftSlot, rightSlot, ?_⟩
  dsimp only
  intro depth
  exact rhoPairStoppedPair.selectedEnvironmentAtoms_restore_eq
    CostCanonicalLaws.rho_unambiguousStaticDecomposition
    rhoBreadthLeftProcessChildren rhoBreadthLeftProcessChildren
    rhoPairStoppedLeftEnvironment rhoPairStoppedRightEnvironment
    ⟨0, by decide⟩ leftOccurrence leftNameEq rightOccurrence rightNameEq
    leftSlot leftSelected rightSlot rightSelected
    rhoPairStoppedForestChildrenAlignment depth

/-- The right parent environment of the mixed stopped/reached breadth cell:
the boundary has disappeared and the same normalized value is represented by
the direct source variable `a`. -/
noncomputable def rhoPairReachedRightValues :=
  rhoBreadthRightProcessChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)

noncomputable def rhoPairReachedRightPackedEnvironment :=
  rhoBreadthRightProcessNode.semanticAtomEnvironment
    rhoPairReachedRightValues

noncomputable def rhoPairReachedRightEnvironment :=
  rhoPairReachedRightPackedEnvironment.2

/-- Positive mixed stopped/reached canary.  The exact child selected by the
left stopped view normalizes to `a`; the generic restoration theorem then
identifies it with the direct source-variable atom in the right parent at
every binder depth. -/
theorem rhoPair_mixed_exists_restoring_atom_names :
    ∃ (leftSlot : Fin rhoPairStoppedLeftEnvironment.atomCount)
      (rightSlot : Fin rhoPairReachedRightEnvironment.atomCount),
      let cospan := rhoPairStoppedLeftEnvironment.semanticKeyCospan
        rhoPairReachedRightEnvironment
      ∀ depth,
        ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment depth
            (cospan.reifyWith rhoPairStoppedLeftEnvironment.lookupAtom?
              cospan.leftSlot
              (.fvar (rhoPairStoppedLeftEnvironment.atomName leftSlot))) =
          ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment depth
            (cospan.reifyWith rhoPairReachedRightEnvironment.lookupAtom?
              cospan.rightSlot
              (.fvar (rhoPairReachedRightEnvironment.atomName rightSlot))) := by
  have leftMembership : costRegionBoundaryVariableName
      rhoBreadthBoundaryWitnessA.typed.boundary ∈
        rhoBreadthLeftProcessNode.skeleton.1.freeFvarNames := by
    rw [rhoBreadthLeftProcessNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  obtain ⟨leftOccurrence, leftOccurrenceName⟩ :=
    rhoBreadthLeftProcessNode.skeleton_fvar_covered _ leftMembership
  obtain ⟨leftSlot, leftSelected⟩ := Option.isSome_iff_exists.mp
    (rhoPairStoppedLeftEnvironment.slotOfName?_isSome_of_occurrence
      leftOccurrence)
  have rightMembership : costRegionSourceVariableName "a" ∈
      rhoBreadthRightProcessNode.skeleton.1.freeFvarNames := by
    rw [rhoBreadthRightProcessNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  obtain ⟨rightOccurrence, rightOccurrenceName⟩ :=
    rhoBreadthRightProcessNode.skeleton_fvar_covered _ rightMembership
  obtain ⟨rightSlot, rightSelected⟩ := Option.isSome_iff_exists.mp
    (rhoPairReachedRightEnvironment.slotOfName?_isSome_of_occurrence
      rightOccurrence)
  let selectedIndex : Fin rhoPairStoppedView.view.retainedEntries.length :=
    ⟨0, by decide⟩
  have leftNameEq : leftOccurrence.name = costRegionBoundaryVariableName
      (rhoPairStoppedView.view.retainedEntries.get selectedIndex).boundary := by
    exact leftOccurrenceName
  have targetSupportEmpty :
      (rhoPairStoppedView.view.retainedEntries.get
        selectedIndex).boundary.targetSupport = [] := by
    change rhoBreadthBoundaryWitnessA.typed.boundary.targetSupport = []
    exact rhoBreadthBoundaryWitnessA.targetSupport_eq
  have childNormal :
      ((rhoPairStoppedView.selectedTreeFromForest
        rhoBreadthLeftProcessChildren selectedIndex).normalizedBoundaryValue
          rhoHereditaryNormalizationKernel).1 = .fvar "a" := by
    change (CostRegionTree.normalizeHereditary
      rhoBreadthBoundaryChildA).pattern = .fvar "a"
    exact rhoBreadthBoundaryChildA_normalizeHereditary
  refine ⟨leftSlot, rightSlot, ?_⟩
  dsimp only
  intro depth
  exact rhoPairStoppedView.selectedBoundaryAtom_restoresAsSourceVariable
    CostCanonicalLaws.rho_unambiguousStaticDecomposition
    rhoBreadthLeftProcessChildren rhoPairStoppedLeftEnvironment
    rhoPairReachedRightEnvironment selectedIndex leftOccurrence leftNameEq
    rightOccurrence "a" rightOccurrenceName leftSlot leftSelected rightSlot
    rightSelected targetSupportEmpty childNormal depth

/-- The stopped context view retains exactly its one certified boundary. -/
theorem rhoPairStoppedPair_retainedEntries_length :
    rhoPairStoppedPair.right.view.retainedEntries.length = 1 := rfl

/-- The singleton stopped view as a dependent family of full-inventory source
children. -/
noncomputable def rhoPairStoppedSourceTrees :
    ∀ index : Fin rhoPairStoppedPair.right.view.retainedEntries.length,
      CostRegionTree rhoCIGSLT rhoCutOrderFree
        (rhoPairStoppedPair.selectedSourceEntry index).boundary.targetSupport []
        (rhoPairStoppedPair.selectedSourceEntry index).boundary.content
        (rhoPairStoppedPair.selectedSourceEntry index).boundary.targetType := by
  intro index
  have index_eq : index = ⟨0, by decide⟩ := by
    have inBounds : index.1 < 1 := by
      simpa only [rhoPairStoppedPair_retainedEntries_length] using index.isLt
    apply Fin.ext
    exact Nat.lt_one_iff.mp inBounds
  cases index_eq
  exact rhoPairStoppedSourceTree

/-- Target-child companion of `rhoPairStoppedSourceTrees`. -/
noncomputable def rhoPairStoppedTargetTrees :
    ∀ index : Fin rhoPairStoppedPair.right.view.retainedEntries.length,
      CostRegionTree rhoCIGSLT rhoCutOrderFree
        (rhoPairStoppedPair.right.view.retainedEntries.get
          index).boundary.targetSupport []
        (rhoPairStoppedPair.right.view.retainedEntries.get
          index).boundary.content
        (rhoPairStoppedPair.right.view.retainedEntries.get
          index).boundary.targetType := by
  intro index
  have index_eq : index = ⟨0, by decide⟩ := by
    have inBounds : index.1 < 1 := by
      simpa only [rhoPairStoppedPair_retainedEntries_length] using index.isLt
    apply Fin.ext
    exact Nat.lt_one_iff.mp inBounds
  cases index_eq
  exact rhoPairStoppedTargetTree

/-- Every child in the stopped singleton family is aligned after exact
boundary reindexing. -/
noncomputable def rhoPairStoppedChildrenAlignments :
    ∀ index : Fin rhoPairStoppedPair.right.view.retainedEntries.length,
      CostRegionTreeNormalizationAlignment rhoCIGSLT
        rhoHereditaryNormalizationKernel rhoCutOrderFree
        (rhoPairStoppedSourceTrees index) (rhoPairStoppedTargetTrees index) := by
  intro index
  have index_eq : index = ⟨0, by decide⟩ := by
    have inBounds : index.1 < 1 := by
      simpa only [rhoPairStoppedPair_retainedEntries_length] using index.isLt
    apply Fin.ext
    exact Nat.lt_one_iff.mp inBounds
  cases index_eq
  exact rhoPairStoppedChildrenAlignment

/-- The stopped-site joint holds for the entire retained target-indexed atom
list, not merely for a chosen occurrence. -/
theorem rhoPair_stopped_selectedAtomLists_eq :
    rhoPairStoppedPair.selectedSourceNormalizedAtoms
        (kernel := rhoHereditaryNormalizationKernel)
        rhoPairStoppedSourceTrees =
      rhoPairStoppedPair.selectedTargetNormalizedAtoms
        (kernel := rhoHereditaryNormalizationKernel)
        rhoPairStoppedTargetTrees :=
  Mettapedia.GSLT.LanguageDef.CostStaticPlanContextPair.selectedSourceNormalizedAtoms_eq_selectedTargetNormalizedAtoms
    rhoPairStoppedPair rhoPairStoppedSourceTrees rhoPairStoppedTargetTrees
    rhoPairStoppedChildrenAlignments

/-- Mixed stopped/reached pair on the boundary-carrying edge: the left
view stops at the certified boundary while the right view reaches the whole
region root.  Endpoint states are independent, and both endpoint positions
land in the edge's finite inventories. -/
noncomputable def rhoPairMixedPair :
    CostStaticPlanContextPair rhoCIGSLT .wrapped rhoCutOrderFree
      rhoPairBoundaryEdge (rhoCutOrderBaseDrop (.fvar "a"))
      rhoBreadthLeftProcess
      rhoBreadthLeftProcessPlan.abstractPattern
      rhoBreadthLeftProcessPlan.abstractPattern
      rhoBreadthLeftProcessPlan.boundaryTable.entries
      rhoBreadthLeftProcessPlan.boundaryTable.entries where
  left := rhoPairStoppedView
  right :=
    { view := .reached
        { sourceBound := _, targetBound := _, thinning := _
          sourceAvailable := _, outer := _, sourceType := _
          plan := rhoBreadthLeftProcessPlan
          skeletonContext := .hole
          abstract_eq := rfl }
      entryEmbedding := CostStaticPlanEntryEmbedding.refl _ }
  leftRoot_eq := rhoBreadthLeftProcessPlan.decoration_abstractPattern
  rightRoot_eq := rhoBreadthLeftProcessPlan.decoration_abstractPattern
  leftTable_eq := rfl
  rightTable_eq := rfl

/-! ## The breadth witness as a two-cell sibling family -/

/-- The name-argument cell of the breadth occurrence. -/
noncomputable def rhoPairNameCell :
    CostStaticPlanSiblingPairCell rhoCIGSLT rhoCutOrderFree where
  color := .base
  first := rhoBreadthBaseRedexAPlan.decoration
  second := rhoPairFvarAPlan.decoration
  sourceBoundaries := []
  targetBoundaries := []
  edge := rhoPairCollapseEdge
  sourceDeclaration :=
    .reflective rhoReflectivePresentation.toReflectivePresentationDecl
  sourceDeclaration_eq := rfl
  leftPayload := rhoBreadthRedexA
  rightPayload := .fvar "a"
  leftRootAbstract := rhoBreadthBaseRedexAPlan.abstractPattern
  rightRootAbstract := rhoPairFvarAPlan.abstractPattern
  leftEntries := rhoBreadthBaseRedexAPlan.boundaryTable.entries
  rightEntries := rhoPairFvarAPlan.boundaryTable.entries
  pair := Classical.choice rhoPair_collapse_pair_root

@[simp] theorem rhoPairNameCell_second_pattern :
    rhoPairNameCell.second.pattern = (.fvar "a" : Pattern) := rfl

theorem rhoPairNameCell_continuation_leftLocal :
    rhoBreadthLeftProcess =
      (OneHoleContext.apply (costWrappedConstructorName "PDrop") [] .hole []).fill
        rhoPairNameCell.first.pattern := rfl

theorem rhoPairNameCell_continuation_rightLocal :
    rhoBreadthRightProcess =
      (OneHoleContext.apply (costWrappedConstructorName "PDrop") [] .hole []).fill
        rhoPairNameCell.second.pattern := rfl

/-- The continuation-localized view of the name cell.  Keeping this next to
the transparent cell construction prevents downstream modules from replaying
the cell's dependent plan indices merely to check the two localization
equalities. -/
noncomputable def rhoPairNameCell_continuationWitness :
    CostChangedSiteWitness rhoCIGSLT rhoCutOrderFree
      rhoBreadthLeftProcess rhoBreadthRightProcess where
  cell := rhoPairNameCell
  context := .apply (costWrappedConstructorName "PDrop") [] .hole []
  leftLocal := rhoPairNameCell_continuation_leftLocal
  rightLocal := rhoPairNameCell_continuation_rightLocal

/-- The continuation cell of the breadth occurrence: the same Quote/Drop
content collapses inside the wrapped sibling's certified boundary, reached
through the quote frame.  The decoration-level route for the enclosing
wrapped region is refuted below, so the cell closes at the content. -/
noncomputable def rhoPairContinuationCell :
    CostStaticPlanSiblingPairCell rhoCIGSLT rhoCutOrderFree where
  color := .base
  first := rhoBreadthBaseRedexAPlan.decoration
  second := rhoPairFvarAPlan.decoration
  sourceBoundaries := []
  targetBoundaries := []
  edge := rhoPairCollapseEdge
  sourceDeclaration :=
    .reflective rhoReflectivePresentation.toReflectivePresentationDecl
  sourceDeclaration_eq := rfl
  leftPayload := rhoCutOrderBaseDrop (.fvar "a")
  rightPayload := .fvar "a"
  leftRootAbstract := rhoBreadthBaseRedexAPlan.abstractPattern
  rightRootAbstract := rhoPairFvarAPlan.abstractPattern
  leftEntries := rhoBreadthBaseRedexAPlan.boundaryTable.entries
  rightEntries := rhoPairFvarAPlan.boundaryTable.entries
  pair := Classical.choice rhoPair_collapse_pair_quoteReset

/-- The two-sibling breadth occurrence carried as a two-cell family: one
cell per changed sibling, sharing the single authored reflective
occurrence. -/
noncomputable def rhoBreadthPairCandidates :
    CostStaticPlanGeneratorPairCandidates rhoCIGSLT rhoCutOrderFree
      rhoBreadthGeneratorWitness where
  cells := [rhoPairNameCell, rhoPairContinuationCell]

/-- This concrete candidate list contains both changed siblings.  Coverage is
not a property of the raw carrier, as the empty canary below demonstrates. -/
theorem rhoBreadthPairCandidates_two_cells :
    rhoBreadthPairCandidates.cells.length = 2 := rfl

/-- Negative completeness canary: the raw candidate carrier also admits an
empty family for the same two-sibling occurrence.  Cell coverage and erasure
to the enclosing occurrence are therefore genuine missing theorems, not
consequences of this carrier. -/
theorem rhoBreadthPairCandidates_empty_is_inhabited :
    Nonempty (CostStaticPlanGeneratorPairCandidates rhoCIGSLT rhoCutOrderFree
      rhoBreadthGeneratorWitness) :=
  ⟨CostStaticPlanGeneratorPairCandidates.empty rhoCIGSLT rhoCutOrderFree
    rhoBreadthGeneratorWitness⟩

/-! ## Duplication, discard, and no-creation over the rho boundary -/

/-- Duplication: two target occurrences of the certified boundary pull back
to one source occurrence. -/
noncomputable def rhoPairDuplicatingMap :
    CostBoundaryFiberMap rhoCIGSLT [rhoPairBoundaryEntry]
      [rhoPairBoundaryEntry, rhoPairBoundaryEntry] where
  pullback := fun _index => ⟨0, by decide⟩
  preservesFiber := fun index => by
    rcases index with ⟨_ | _ | _, inBounds⟩
    · exact CostRegionBoundary.sameFiber_refl _
    · exact CostRegionBoundary.sameFiber_refl _
    · exact absurd inBounds (by simp)

/-- The duplicating pullback is genuinely non-injective: two distinct target
occurrences share one source occurrence. -/
theorem rhoPair_duplication :
    rhoPairDuplicatingMap.pullback ⟨0, by decide⟩ =
        rhoPairDuplicatingMap.pullback ⟨1, by decide⟩ ∧
      (⟨0, by decide⟩ : Fin 2) ≠ ⟨1, by decide⟩ :=
  ⟨rfl, by decide⟩

/-- Discard: with two source occurrences and one target occurrence, the
second source occurrence has no target image; no surjectivity is demanded
anywhere. -/
noncomputable def rhoPairDiscardingMap :
    CostBoundaryFiberMap rhoCIGSLT
      [rhoPairBoundaryEntry, rhoPairBoundaryEntry] [rhoPairBoundaryEntry]
      where
  pullback := fun _index => ⟨0, by decide⟩
  preservesFiber := fun index => by
    rcases index with ⟨_ | _, inBounds⟩
    · exact CostRegionBoundary.sameFiber_refl _
    · exact absurd inBounds (by simp)

/-- The discarded source occurrence is outside the pullback image. -/
theorem rhoPair_discard (targetIndex : Fin 1) :
    rhoPairDiscardingMap.pullback targetIndex ≠ ⟨1, by decide⟩ := by
  rcases targetIndex with ⟨_ | _, inBounds⟩
  · exact fun impossible => by cases impossible
  · exact absurd inBounds (by simp)

/-- No creation at the actual edge interface: no lawful edge can present a
target boundary occurrence over an empty source inventory. -/
theorem rhoPair_noCreation
    (first second : CostStaticPlanDecoration rhoCIGSLT) :
    IsEmpty (CostStaticPlanEdge rhoCIGSLT first second []
      [rhoPairBoundaryEntry]) :=
  CostStaticPlanLift.noCreationFromEmpty rhoCIGSLT.costStaticPlanLift
    (first := first) (second := second) ⟨0, by decide⟩

/-! ## Repeated equal typed entries retain distinct replayable positions -/

/-- Retaining the first of two equal entries. -/
noncomputable def rhoPairKeepFirst :
    CostStaticPlanEntryEmbedding rhoCIGSLT .wrapped rhoCutOrderFree
      [rhoBreadthBoundaryWitnessA.typed]
      [rhoBreadthBoundaryWitnessA.typed, rhoBreadthBoundaryWitnessA.typed] :=
  .keep (.nil [rhoBreadthBoundaryWitnessA.typed])

/-- Retaining the second of two equal entries. -/
noncomputable def rhoPairKeepSecond :
    CostStaticPlanEntryEmbedding rhoCIGSLT .wrapped rhoCutOrderFree
      [rhoBreadthBoundaryWitnessA.typed]
      [rhoBreadthBoundaryWitnessA.typed, rhoBreadthBoundaryWitnessA.typed] :=
  .skip rhoBreadthBoundaryWitnessA.typed (.keep (.nil []))

/-- The two retentions are distinct embeddings and select distinct
positions, although the retained entry values are equal.  Proof irrelevance
can never conflate them because the keep/skip path is data. -/
theorem rhoPair_repeatedEntries_distinct :
    rhoPairKeepFirst ≠ rhoPairKeepSecond ∧
      rhoPairKeepFirst.position ⟨0, by decide⟩ ≠
        rhoPairKeepSecond.position ⟨0, by decide⟩ := by
  constructor
  · intro impossible
    cases impossible
  · intro impossible
    cases impossible

/-! ## Boundary respelling refutes the decoration-level route -/

/-- A changed boundary content re-spells the content-keyed boundary
variable, and the retagged source variable can never canonicalize equal to
it: the reflective canonicalizer leaves a bare drop application intact on
both sides, so the skeletons differ exactly in the two free-variable
namespaces, which are disjoint.  A stopped cell therefore admits no
decoration-level reflective witness and must close at the restored
semantic apex. -/
theorem rhoPair_boundaryRespelling_blocks_reflective
    (boundary : CostRegionBoundary) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        rhoReflectivePresentation.toReflectivePresentationDecl
        (.apply "PDrop" [.fvar (costRegionBoundaryVariableName boundary)]) ≠
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        rhoReflectivePresentation.toReflectivePresentationDecl
        (.apply "PDrop" [.fvar (costRegionSourceVariableName "a")]) := by
  intro collapsed
  simp only [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
    rhoReflectivePresentation] at collapsed
  obtain ⟨-, argumentsEq⟩ := Pattern.apply.inj collapsed
  exact costRegionSourceVariableName_ne_boundary "a" boundary
    (Pattern.fvar.inj (List.cons.inj argumentsEq).1).symm

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanPairCanary
