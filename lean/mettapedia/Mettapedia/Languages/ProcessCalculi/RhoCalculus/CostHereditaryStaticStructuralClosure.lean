import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRestorationClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalReachableDomain
import Mettapedia.GSLT.LanguageDef.CostCanonicalStructuralAlignment
import Mettapedia.GSLT.LanguageDef.CostStaticRootView
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalRootDichotomy

/-!
# Static-to-structural hereditary closure for rho Cost

Reflective collapse can expose one recursively normalized semantic atom as
the complete result of a static region.  The exposed value may elaborate as
a structural tree: Quote/Drop can reveal a free name, and parallel singleton
collapse can reveal a neutral process application.  The bridge below covers
both forms without inspecting the atom's compact shape.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionNode

/-- A structural rho Cost tree at the generated base Name sort is necessarily
a bound or free variable.  Static quotation roots have already been excluded;
the remaining neutral constructors cannot return Name, and substitution is
excluded by the checked object-pattern carrier. -/
inductive RhoStructuralNameLeaf : Pattern → Type where
  | bvar (index : Nat) : RhoStructuralNameLeaf (.bvar index)
  | fvar (name : String) : RhoStructuralNameLeaf (.fvar name)

/-- In a generated rho reflective-name fibre, a canonical root can collapse
only through quotation.  The other generic collapsing form is a bare
parallel collection, but no collection inhabits either generated rho name
fibre.  This is the typed exclusion that blocks the untyped quote/parallel
depth-reset counterexample in the common-apex recursion. -/
theorem rhoCollapsingRoot_quote_of_typed_reflectiveName
    (declaration : ReflectivePresentationDecl)
    (declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern}
    (typed : HasType rhoCIGSLT.costWholeLanguage free bound pattern
      (.base declaration.nameSort))
    (collapsing : CollapsingRoot declaration pattern) :
    ∃ arguments, pattern = .apply declaration.quoteConstructor arguments := by
  rcases collapsing with quoted | parallel
  · exact quoted
  · obtain ⟨elements, shape⟩ := parallel
    subst pattern
    exact False.elim
      (rho_no_collection_at_reflectiveNameSort declaration
        declarationMembership typed)

/-- Two typed collapsing roots in one generated reflective-name fibre cannot
form a quote/parallel straddle: both are quotation applications. -/
theorem rhoCollapsingRoots_quotes_of_typed_reflectiveName
    (declaration : ReflectivePresentationDecl)
    (declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {left right : Pattern}
    (leftTyped : HasType rhoCIGSLT.costWholeLanguage free bound left
      (.base declaration.nameSort))
    (rightTyped : HasType rhoCIGSLT.costWholeLanguage free bound right
      (.base declaration.nameSort))
    (leftCollapsing : CollapsingRoot declaration left)
    (rightCollapsing : CollapsingRoot declaration right) :
    (∃ arguments, left = .apply declaration.quoteConstructor arguments) ∧
      ∃ arguments, right = .apply declaration.quoteConstructor arguments :=
  ⟨rhoCollapsingRoot_quote_of_typed_reflectiveName declaration
      declarationMembership leftTyped leftCollapsing,
    rhoCollapsingRoot_quote_of_typed_reflectiveName declaration
      declarationMembership rightTyped rightCollapsing⟩

/-- Typing inversion for a generated rho Quote/Drop shell without imposing a
particular restoration support.  Empty support is available for every typing
derivation, so the support-aware inversion theorem yields the exact generated
name fibre while this wrapper exposes only the semantic typing fact needed by
the recursive common-apex construction. -/
theorem rho_costStatic_quoteDrop_inner_hasType
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {inner : Pattern} {type : TypeExpr}
    (typed : HasType rhoCIGSLT.costWholeLanguage free bound
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor
        [.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).dropConstructor [inner]]) type) :
    HasType rhoCIGSLT.costWholeLanguage free bound inner
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).nameSort) := by
  obtain ⟨innerTyped, _⟩ :=
    rho_costStatic_quoteDrop_inner_typed color typed
      (typed.reflectiveSupportSafeAt_empty bound)
  exact innerTyped

/-- Construct the exact leaf view from the retained tree and the object
carrier.  Quotation status is read from the authored reflective declarations,
then intrinsic constructor decoding proves that any quoted application has a
static role; no rho rule enumeration is duplicated here. -/
theorem nonempty_rhoStructuralNameLeaf
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree rhoCIGSLT targetFree available outer pattern
      type)
    (structural : tree.rootIsStatic = false)
    (object : WellSorted.isObjectPattern pattern = true)
    (typeEq : type = .base (costBaseSortName "Name")) :
    Nonempty (RhoStructuralNameLeaf pattern) := by
  let view := tree.structuralRootView structural
  cases view with
  | bvar lookup => exact ⟨.bvar _⟩
  | fvar lookup => exact ⟨.fvar _⟩
  | neutralApplicationOrdinary membership notBare constructor materializes
      neutral ordinary children =>
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl
      have sourceMembership :
          rhoReflectivePresentation.toReflectivePresentationDecl ∈
            rhoCIGSLT.reflection.1.presentations := by
        change rhoReflectivePresentation.toReflectivePresentationDecl ∈
          ReflectionExtension.rhoReflectionProfile.presentations
        simp [ReflectionExtension.rhoReflectionProfile]
      have declarationMembership : declaration ∈
          rhoCIGSLT.costWholeReflectionProfile.presentations := by
        simpa [declaration] using
          costStaticReflectivePresentationDecl_mem rhoCIGSLT .base
            rhoReflectivePresentation.toReflectivePresentationDecl
            sourceMembership
      have quoted :=
        (rho_costReflectiveNameResultsQuoted declaration declarationMembership
          _ membership (TypeExpr.base.inj typeEq)).1
      rw [quoted] at ordinary
      contradiction
  | neutralApplicationQuote membership notBare constructor materializes
      neutral quoted children =>
      have decoded : rhoCIGSLT.decodeDeclaredCostConstructor
          (rhoCIGSLT.materializeDeclaredCostConstructor constructor).label =
          some constructor := by
        rw [rhoCIGSLT.materializeDeclaredCostConstructor_label]
        exact rhoCIGSLT.decodeDeclaredCostConstructor_render constructor
      have quotedAtRendered : ReflectiveContextSupport.isQuoteConstructor
          rhoCIGSLT.costWholeReflectionProfile
            (rhoCIGSLT.materializeDeclaredCostConstructor constructor).label =
          true := by
        simpa [materializes] using quoted
      obtain ⟨color, staticRole⟩ :=
        rhoCIGSLT.exists_static_role_of_isQuoteConstructor_of_decode
          constructor decoded quotedAtRendered
      rcases neutral with neutralRole | ⟨kind, neutralRole⟩ <;>
        rw [neutralRole] at staticRole <;> contradiction
  | lambda bodyTree => cases typeEq
  | multiLambda bodyTree => cases typeEq
  | subst bodyTree replacementTree =>
      simp [WellSorted.isObjectPattern] at object
  | collection children => cases typeEq

/-- A reified Quote/Drop shell canonicalizes to its selected semantic atom,
independently of the target binder context. -/
theorem CostStaticRegionNode.canonicalizeReifiedTargetFrame_quoteDrop_atom
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (slot : Fin environment.atomCount)
    (reifiedFrame : (node.reifiedSourceFrame environment).1 =
      .apply rhoReflectivePresentation.quoteConstructor
        [.apply rhoReflectivePresentation.dropConstructor
          [.fvar (environment.atomName slot)]]) :
    node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      .fvar (environment.atomName slot) := by
  rw [canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize node
    environment, reifiedFrame]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
    rhoReflectivePresentation, mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars]

/-- A reified bare-parallel singleton canonicalizes to its selected semantic
atom, independently of the semantic key: sorting a singleton has no choice. -/
theorem CostStaticRegionNode.canonicalizeReifiedTargetFrame_parallelSingleton_atom
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (slot : Fin environment.atomCount)
    (reifiedFrame : (node.reifiedSourceFrame environment).1 =
      .collection rhoReflectivePresentation.parallelCollection
        [.fvar (environment.atomName slot)] none) :
    node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      .fvar (environment.atomName slot) := by
  rw [canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize node
    environment, reifiedFrame]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy,
    rhoReflectivePresentation, mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars]

/-- A reified bare-parallel singleton whose payload is a bound variable
canonicalizes to the mapped, binder-reinserted variable itself.  Unlike the
atom theorem above, this case has no finite free-variable slot. -/
theorem CostStaticRegionNode.canonicalizeReifiedTargetFrame_parallelSingleton_bvar
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (sourceIndex : Nat)
    (reifiedFrame : (node.reifiedSourceFrame environment).1 =
      .collection rhoReflectivePresentation.parallelCollection
        [.bvar sourceIndex] none) :
    node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      node.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT) (.bvar sourceIndex)) := by
  rw [canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize node
    environment, reifiedFrame]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy,
    rhoReflectivePresentation]

/-- Hereditary evaluation of the same rigid singleton restores no semantic
atom: supported substitution preserves the surviving bound index. -/
theorem CostStaticRegionNode.normalizeHereditaryRawWithInventory_parallelSingleton_bvar
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (sourceIndex : Nat)
    (reifiedFrame : (node.reifiedSourceFrame
        (CostStaticAtomEnvironment.ofInventory inventory)).1 =
      .collection rhoReflectivePresentation.parallelCollection
        [.bvar sourceIndex] none) :
    node.normalizeHereditaryRawWithInventory values inventory
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      node.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT) (.bvar sourceIndex)) := by
  unfold CostStaticRegionNode.normalizeHereditaryRawWithInventory
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  change environment.restore node.targetBound
      (node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)) = _
  have frame : (node.reifiedSourceFrame environment).1 =
      .collection rhoReflectivePresentation.parallelCollection
        [.bvar sourceIndex] none := by
    simpa only [environment] using reifiedFrame
  rw [CostStaticRegionNode.canonicalizeReifiedTargetFrame_parallelSingleton_bvar
    node environment sourceIndex frame]
  simp [CostStaticAtomEnvironment.restore,
    CostStaticAtomEnvironment.restoreAt,
    ReflectiveContextSupport.substituteAt, mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars]

/-- A selected rho frame consisting of one bare-parallel semantic atom
evaluates to restoration of that atom.  Unlike the Quote/Drop companion, no
availability reset occurs; the exact target binder depth is retained by the
restoration operation. -/
theorem CostStaticRegionNode.normalizeHereditaryRawWithInventory_parallelSingleton_restore
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount)
    (reifiedFrame : (node.reifiedSourceFrame
        (CostStaticAtomEnvironment.ofInventory inventory)).1 =
      .collection rhoReflectivePresentation.parallelCollection
        [.fvar ((CostStaticAtomEnvironment.ofInventory inventory).atomName
          slot)] none) :
    node.normalizeHereditaryRawWithInventory values inventory
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      (CostStaticAtomEnvironment.ofInventory inventory).restore
        node.targetBound
        (.fvar ((CostStaticAtomEnvironment.ofInventory inventory).atomName
          slot)) := by
  rw [normalizeHereditaryRawWithInventory_eq_sourceAction node values
    inventory, reifiedFrame]
  unfold rhoCostStaticActionAt
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy,
    rhoReflectivePresentation]
  unfold CostStaticAtomEnvironment.restore
    CostStaticAtomEnvironment.restoreAt
  change ReflectiveContextSupport.substituteAt
      rhoCIGSLT.costWholeReflectionProfile
      (CostStaticAtomEnvironment.ofInventory inventory).restorationSupport
      (CostStaticAtomEnvironment.ofInventory inventory).restorationAssignment
      node.targetBound.length
      (node.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT)
          (.fvar ((CostStaticAtomEnvironment.ofInventory inventory).atomName
            slot)))) = _
  simp [mapPattern, CostStaticBinderThinning.thickenAmbientBVars]

/-- Total-inventory form of the bare-parallel singleton atom exposure. -/
theorem CostStaticRegionNode.normalizeHereditary_parallelSingleton_restore
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory
      (node.semanticAtomEnvironment values).1).atomCount)
    (reifiedFrame : (node.reifiedSourceFrame
        (CostStaticAtomEnvironment.ofInventory
          (node.semanticAtomEnvironment values).1)).1 =
      .collection rhoReflectivePresentation.parallelCollection
        [.fvar ((CostStaticAtomEnvironment.ofInventory
          (node.semanticAtomEnvironment values).1).atomName slot)] none) :
    (normalizeHereditary node values).1 =
      (CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1).restore node.targetBound
          (.fvar ((CostStaticAtomEnvironment.ofInventory
            (node.semanticAtomEnvironment values).1).atomName slot)) := by
  unfold normalizeHereditary
  rw [normalizeHereditaryWithInventory_pattern]
  exact normalizeHereditaryRawWithInventory_parallelSingleton_restore node
    values (node.semanticAtomEnvironment values).1 slot reifiedFrame

/-- A rho static frame whose canonical target frame is one selected atom
meets any result that factors through restoration of that same atom.

The finite inventory and atom position are retained.  Equality of the two
results is consequently derived by `PackedCostSemanticAtomJoin.results_eq`;
it is not stored as a premise. -/
def rhoCanonicalAtomSemanticJoinWithInventory
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount)
    (canonicalFrame :
      node.canonicalizeReifiedTargetFrame
          (CostStaticAtomEnvironment.ofInventory inventory)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar ((CostStaticAtomEnvironment.ofInventory inventory).atomName
          slot))
    {rightResult : Pattern}
    (rightFactors : rightResult =
      (CostStaticAtomEnvironment.ofInventory inventory).restore
        node.targetBound
        (.fvar ((CostStaticAtomEnvironment.ofInventory inventory).atomName
          slot))) :
    PackedCostSemanticAtomJoin rhoCIGSLT
      (normalizeHereditaryWithInventory node values inventory).1
      rightResult where
  color := color
  targetFree := targetFree
  occurrences := node.plan.occurrences
  table := node.boundaryTable
  values := values
  root := node.skeleton.1
  inventory := inventory
  environment := CostStaticAtomEnvironment.ofInventory inventory
  bound := node.targetBound
  slot := slot
  leftFactors := by
    rw [normalizeHereditaryWithInventory_pattern]
    unfold Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.normalizeHereditaryRawWithInventory
    exact congrArg
      ((CostStaticAtomEnvironment.ofInventory inventory).restore
        node.targetBound) canonicalFrame
  rightFactors := rightFactors

/-- Total-inventory specialization of
`rhoCanonicalAtomSemanticJoinWithInventory`. -/
def rhoCanonicalAtomSemanticJoin
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory
      (node.semanticAtomEnvironment values).1).atomCount)
    (canonicalFrame :
      node.canonicalizeReifiedTargetFrame
          (CostStaticAtomEnvironment.ofInventory
            (node.semanticAtomEnvironment values).1)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar ((CostStaticAtomEnvironment.ofInventory
          (node.semanticAtomEnvironment values).1).atomName slot))
    {rightResult : Pattern}
    (rightFactors : rightResult =
      (CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1).restore node.targetBound
        (.fvar ((CostStaticAtomEnvironment.ofInventory
          (node.semanticAtomEnvironment values).1).atomName slot))) :
    PackedCostSemanticAtomJoin rhoCIGSLT
      (normalizeHereditary node values).1 rightResult := by
  unfold normalizeHereditary
  exact rhoCanonicalAtomSemanticJoinWithInventory node values
    (node.semanticAtomEnvironment values).1 slot canonicalFrame rightFactors

/-- Lift a selected canonical atom of one static rho root to the general
root-bridge carrier against an arbitrary structural tree. -/
noncomputable def rhoStaticRootBridgeOfCanonicalAtom
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOuter rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {rightPattern : Pattern} {rightType : TypeExpr}
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory
      (node.semanticAtomEnvironment
        (children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1).atomCount)
    (canonicalFrame :
      let values := children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let environment := CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1
      node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar (environment.atomName slot))
    (rightFactors :
      let values := children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let environment := CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1
      (right.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        environment.restore node.targetBound
          (.fvar (environment.atomName slot))) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) node children) right := by
  let values := children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let join := rhoCanonicalAtomSemanticJoin node values slot canonicalFrame
    rightFactors
  refine .semanticAtom _ _ ?_
  exact join.transport (by
    rw [CostRegionTree.normalize_static_pattern]
    rfl) rfl

/-- Quote/Drop specialization of `rhoStaticRootBridgeOfCanonicalAtom`.
Callers supply the proof-relevant selected slot and the structural endpoint's
restoration factorization; the canonical-frame equation is derived here. -/
noncomputable def rhoStaticRootBridgeOfQuoteDropAtom
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOuter rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {rightPattern : Pattern} {rightType : TypeExpr}
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory
      (node.semanticAtomEnvironment
        (children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1).atomCount)
    (reifiedFrame :
      let values := children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let environment := CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1
      (node.reifiedSourceFrame environment).1 =
        .apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor
            [.fvar (environment.atomName slot)]])
    (rightFactors :
      let values := children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let environment := CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1
      (right.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        environment.restore node.targetBound
          (.fvar (environment.atomName slot))) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) node children) right := by
  apply rhoStaticRootBridgeOfCanonicalAtom node children right slot
  · exact CostStaticRegionNode.canonicalizeReifiedTargetFrame_quoteDrop_atom
      node _ slot reifiedFrame
  · exact rightFactors

/-- Bare-parallel singleton specialization of
`rhoStaticRootBridgeOfCanonicalAtom`.  This is the asymmetric terminal used
when a static process frame exposes a neutral recursively normalized child. -/
noncomputable def rhoStaticRootBridgeOfParallelSingletonAtom
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOuter rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {rightPattern : Pattern} {rightType : TypeExpr}
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory
      (node.semanticAtomEnvironment
        (children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1).atomCount)
    (reifiedFrame :
      let values := children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let environment := CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1
      (node.reifiedSourceFrame environment).1 =
        .collection rhoReflectivePresentation.parallelCollection
          [.fvar (environment.atomName slot)] none)
    (rightFactors :
      let values := children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let environment := CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1
      (right.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        environment.restore node.targetBound
          (.fvar (environment.atomName slot))) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) node children) right := by
  apply rhoStaticRootBridgeOfCanonicalAtom node children right slot
  · exact
      CostStaticRegionNode.canonicalizeReifiedTargetFrame_parallelSingleton_atom
        node _ slot reifiedFrame
  · exact rightFactors

/-- Static-to-structural terminal for a collapse that exposes a rigid compact
leaf rather than a finite semantic atom.

Bound variables are the motivating case: they are preserved by supported
substitution at every depth but are deliberately absent from the free-variable
atom inventory.  The two factorization equations are supplied by the rho
collapse inversion, while `rigid` independently certifies that the common leaf
does not depend on a support assignment. -/
def rhoStaticRootBridgeOfRigidLeaf
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOuter rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {rightPattern : Pattern} {rightType : TypeExpr}
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (leaf : Pattern)
    (rigid : ∀ support assignment depth,
      ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
        support assignment depth leaf = leaf)
    (leftFactors :
      ((CostRegionTree.static (outer := leftOuter) node children).normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern = leaf)
    (rightFactors :
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern = leaf) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) node children) right :=
  .rigidLeaf _ _
    { leaf := leaf
      rigid := rigid
      leftFactors := leftFactors
      rightFactors := rightFactors }

/-! ## Corrected collapsing-leaf exposure

A collapsing static rho root need not expose a finite semantic atom.  A bound
variable has no free-variable occurrence and therefore no atom slot.  The
following carrier records exactly the two reachable terminal shapes without
forgetting the proof-relevant static node, its normalized boundary children,
or the structural endpoint tree.
-/

/-- Proof-relevant terminal data for an oriented static-to-structural rho
collapse.

The atom branch retains an actual finite semantic slot.  The rigid branch is
deliberately restricted to a bound variable, the only admitted rigid leaf in
the rho Name/Proc fibres.  Neither branch stores the desired root bridge or
the equality of the two final results as a field. -/
inductive RhoCollapsingLeafExposure
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {rightPattern : Pattern} {rightType : TypeExpr}
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType) : Type where
  | atom
      (slot : Fin (CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment
          (children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1).atomCount)
      (staticFrame :
        let values := children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)
        let environment := CostStaticAtomEnvironment.ofInventory
          (node.semanticAtomEnvironment values).1
        node.canonicalizeReifiedTargetFrame environment
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation) =
          .fvar (environment.atomName slot))
      (structuralNormal :
        let values := children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)
        let environment := CostStaticAtomEnvironment.ofInventory
          (node.semanticAtomEnvironment values).1
        (right.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          environment.restore node.targetBound
            (.fvar (environment.atomName slot))) :
      RhoCollapsingLeafExposure node children right
  | rigidBVar
      (index : Nat)
      (staticNormal :
        (rhoHereditaryStaticNormalizer node
          (children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1 =
          .bvar index)
      (structuralNormal :
        (right.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
            .bvar index) :
      RhoCollapsingLeafExposure node children right

namespace RhoCollapsingLeafExposure

/-- Eliminate corrected atom-or-rigid exposure to the exact hereditary root
bridge.  The result equality is derived by the selected terminal: semantic
atoms use their stored typed normal value, whereas bound variables are rigid
under every supported assignment. -/
noncomputable def toRootBridge
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOuter rightAvailable rightOuter : List TypeExpr}
    {node : CostStaticRegionNode rhoCIGSLT color targetFree}
    {children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable}
    {rightPattern : Pattern} {rightType : TypeExpr}
    {right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType}
    (exposure : RhoCollapsingLeafExposure node children right) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) node children) right := by
  cases exposure with
  | atom slot staticFrame structuralNormal =>
      exact rhoStaticRootBridgeOfCanonicalAtom node children right slot
        staticFrame structuralNormal
  | rigidBVar index staticNormal structuralNormal =>
      apply rhoStaticRootBridgeOfRigidLeaf node children right (.bvar index)
      · intro support assignment depth
        simp [ReflectiveContextSupport.substituteAt]
      · rw [CostRegionTree.normalize_static_pattern]
        exact staticNormal
      · exact structuralNormal

/-- Construct atom exposure from equality with the selected atom's normalized
value.  Binder support remains proof-relevant in the atom key, but a
binder-closed normal value restores unchanged at every ambient depth. -/
noncomputable def atomOfNormal
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {rightPattern : Pattern} {rightType : TypeExpr}
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (slot : Fin (node.normalizationEnvironment rhoHereditaryStaticNormalizer
      children).atomCount)
    (staticFrame :
      node.canonicalizeReifiedTargetFrame
          (node.normalizationEnvironment rhoHereditaryStaticNormalizer
            children)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar ((node.normalizationEnvironment
          rhoHereditaryStaticNormalizer children).atomName slot))
    (normalEq :
      ((node.normalizationEnvironment rhoHereditaryStaticNormalizer children
        ).atomValue slot).key.normal =
        (right.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern)
    (normalScoped :
      ((node.normalizationEnvironment rhoHereditaryStaticNormalizer children
        ).atomValue slot).key.normal.isWellScopedAt 0 = true) :
    RhoCollapsingLeafExposure node children right := by
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have restored :
      environment.restore node.targetBound
          (.fvar (environment.atomName slot)) =
        (environment.atomValue slot).key.normal :=
    environment.restore_atomName_eq_normal_of_scoped slot normalScoped
      node.targetBound
  exact .atom slot staticFrame (normalEq.symm.trans restored.symm)

/-- Same-support counterpart of `atomOfNormal`.  No binder-closedness is
needed: when the semantic atom's retained target support has the exact root
depth, restoration performs zero weakening.  This is the terminal used by
ordinary bare-parallel boundaries under binders. -/
noncomputable def atomOfSameSupportNormal
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {rightPattern : Pattern} {rightType : TypeExpr}
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (slot : Fin (node.normalizationEnvironment rhoHereditaryStaticNormalizer
      children).atomCount)
    (staticFrame :
      node.canonicalizeReifiedTargetFrame
          (node.normalizationEnvironment rhoHereditaryStaticNormalizer
            children)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar ((node.normalizationEnvironment
          rhoHereditaryStaticNormalizer children).atomName slot))
    (normalEq :
      ((node.normalizationEnvironment rhoHereditaryStaticNormalizer children
        ).atomValue slot).key.normal =
        (right.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern)
    (supportLength :
      ((node.normalizationEnvironment rhoHereditaryStaticNormalizer children
        ).atomValue slot).key.targetSupport.length = node.targetBound.length) :
    RhoCollapsingLeafExposure node children right := by
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have restored :
      environment.restore node.targetBound
          (.fvar (environment.atomName slot)) =
        (environment.atomValue slot).key.normal :=
    environment.restore_atomName_eq_normal_of_support_length_eq slot
      node.targetBound supportLength
  exact .atom slot staticFrame (normalEq.symm.trans restored.symm)

/-- Construct atom exposure when a retained recursive boundary child aligns
with a structural free-name leaf.  The child is recovered from the context
view's finite position, so duplicate boundary spellings are resolved by
static-decomposition unambiguity rather than equality search.  Alignment
supplies the semantic fact; binder-closed restoration then removes any
dependence on the boundary's retained target support. -/
noncomputable def boundarySourceVariable
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {payload : Pattern}
    (view : CostStaticPlanContextInventoryView rhoCIGSLT color targetFree
      payload node.skeleton.1 node.finiteBoundaryTable.entries)
    (index : Fin view.view.retainedEntries.length)
    (occurrence : CostStaticFVarOccurrence node.skeleton.1)
    (occurrenceName : occurrence.name = costRegionBoundaryVariableName
      (view.view.retainedEntries.get index).boundary)
    (name : String)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      (.fvar name) (.base (costBaseSortName "Name")))
    (slot : Fin (node.normalizationEnvironment rhoHereditaryStaticNormalizer
      children).atomCount)
    (selected :
      (node.normalizationEnvironment rhoHereditaryStaticNormalizer children
        ).slotOfName? occurrence.name = some slot)
    (staticFrame :
      node.canonicalizeReifiedTargetFrame
          (node.normalizationEnvironment rhoHereditaryStaticNormalizer
            children)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar ((node.normalizationEnvironment
          rhoHereditaryStaticNormalizer children).atomName slot))
    (childAlignment : CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (view.selectedTreeFromForest children index) right) :
    RhoCollapsingLeafExposure node children right := by
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have rightNormal :
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          .fvar name := by
    let rightView := right.structuralRootView
      right.rootIsStatic_eq_false_of_fvar
    cases rightView with
    | fvar lookup => simp [CostRegionTree.normalize]
  have atomNormal : (environment.atomValue slot).key.normal =
      ((view.selectedTreeFromForest children index).normalizedBoundaryValue
        rhoHereditaryNormalizationKernel).1 :=
    view.selectedBoundaryAtom_normal_eq
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition children
      (environment := environment) index occurrence occurrenceName slot
      selected
  have selectedNormal :
      ((view.selectedTreeFromForest children index).normalizedBoundaryValue
        rhoHereditaryNormalizationKernel).1 = .fvar name := by
    rw [CostRegionTree.normalizedBoundaryValue_pattern]
    exact childAlignment.normalize_pattern_eq.trans rightNormal
  have normalEq : (environment.atomValue slot).key.normal =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    atomNormal.trans (selectedNormal.trans rightNormal.symm)
  apply atomOfNormal node children right slot staticFrame normalEq
  rw [atomNormal, selectedNormal]
  rfl

/-- Construct the support-independent source-variable exposure through any
proof-relevant elaboration of the selected boundary endpoint.

The recursive elaborator is allowed to choose a different admissible tree
for the boundary content.  Static-decomposition unambiguity identifies that
tree's normalized pattern with the exact occurrence-selected forest child;
the supplied alignment then proves that the common value is the structural
free name.  No equality search through the boundary table and no equality of
target-support lengths is used. -/
noncomputable def boundaryElaborationSourceVariable
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {alignedAvailable alignedOuter rightAvailable rightOuter : List TypeExpr}
    {alignedType rightType : TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {payload : Pattern}
    (view : CostStaticPlanContextInventoryView rhoCIGSLT color targetFree
      payload node.skeleton.1 node.finiteBoundaryTable.entries)
    (index : Fin view.view.retainedEntries.length)
    (occurrence : CostStaticFVarOccurrence node.skeleton.1)
    (occurrenceName : occurrence.name = costRegionBoundaryVariableName
      (view.view.retainedEntries.get index).boundary)
    (name : String)
    (leftElaboration : CostRegionTree rhoCIGSLT targetFree
      (view.view.retainedEntries.get index).boundary.targetSupport []
      (view.view.retainedEntries.get index).boundary.content
      (view.view.retainedEntries.get index).boundary.targetType)
    (alignedRight : CostRegionTree rhoCIGSLT targetFree alignedAvailable
      alignedOuter (.fvar name) alignedType)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      (.fvar name) rightType)
    (slot : Fin (node.normalizationEnvironment rhoHereditaryStaticNormalizer
      children).atomCount)
    (selected :
      (node.normalizationEnvironment rhoHereditaryStaticNormalizer children
        ).slotOfName? occurrence.name = some slot)
    (staticFrame :
      node.canonicalizeReifiedTargetFrame
          (node.normalizationEnvironment rhoHereditaryStaticNormalizer
            children)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar ((node.normalizationEnvironment
          rhoHereditaryStaticNormalizer children).atomName slot))
    (childAlignment : CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree leftElaboration
        alignedRight) :
    RhoCollapsingLeafExposure node children right := by
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have alignedRightNormal :
      (alignedRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          .fvar name := by
    let alignedRightView := alignedRight.structuralRootView
      alignedRight.rootIsStatic_eq_false_of_fvar
    cases alignedRightView with
    | fvar lookup => simp [CostRegionTree.normalize]
  have rightNormal :
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          .fvar name := by
    let rightView := right.structuralRootView
      right.rootIsStatic_eq_false_of_fvar
    cases rightView with
    | fvar lookup => simp [CostRegionTree.normalize]
  have atomNormal : (environment.atomValue slot).key.normal =
      ((view.selectedTreeFromForest children index).normalizedBoundaryValue
        rhoHereditaryNormalizationKernel).1 :=
    view.selectedBoundaryAtom_normal_eq
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition children
      (environment := environment) index occurrence occurrenceName slot
      selected
  have selectedToElaboration :
      ((view.selectedTreeFromForest children index).normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (leftElaboration.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel
      (view.selectedTreeFromForest children index) leftElaboration
      (view.view.retainedEntries.get index).contentObjectPattern
  have selectedNormal :
      ((view.selectedTreeFromForest children index).normalizedBoundaryValue
        rhoHereditaryNormalizationKernel).1 = .fvar name := by
    rw [CostRegionTree.normalizedBoundaryValue_pattern]
    exact selectedToElaboration.trans
      (childAlignment.normalize_pattern_eq.trans alignedRightNormal)
  have normalEq : (environment.atomValue slot).key.normal =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    atomNormal.trans (selectedNormal.trans rightNormal.symm)
  apply atomOfNormal node children right slot staticFrame normalEq
  rw [atomNormal, selectedNormal]
  rfl

/-- Construct atom exposure when a retained recursive boundary child aligns
with an arbitrary structural endpoint at the same ambient binder depth.

The selected occurrence supplies both the child's hereditary normal value and
its exact target support.  The alignment supplies equality with the structural
normal form.  When the retained support has the root node's length, supported
restoration performs zero weakening, so the result does not require the
structural endpoint to be binder-closed.  This is the general terminal for a
bare-parallel singleton exposed below ordinary binders. -/
noncomputable def boundaryAlignedSameSupport
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {payload : Pattern}
    (view : CostStaticPlanContextInventoryView rhoCIGSLT color targetFree
      payload node.skeleton.1 node.finiteBoundaryTable.entries)
    (index : Fin view.view.retainedEntries.length)
    (occurrence : CostStaticFVarOccurrence node.skeleton.1)
    (occurrenceName : occurrence.name = costRegionBoundaryVariableName
      (view.view.retainedEntries.get index).boundary)
    {rightPattern : Pattern} {rightType : TypeExpr}
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (slot : Fin (node.normalizationEnvironment rhoHereditaryStaticNormalizer
      children).atomCount)
    (selected :
      (node.normalizationEnvironment rhoHereditaryStaticNormalizer children
        ).slotOfName? occurrence.name = some slot)
    (staticFrame :
      node.canonicalizeReifiedTargetFrame
          (node.normalizationEnvironment rhoHereditaryStaticNormalizer
            children)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar ((node.normalizationEnvironment
          rhoHereditaryStaticNormalizer children).atomName slot))
    (childAlignment : CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (view.selectedTreeFromForest children index) right)
    (sameSupport :
      (view.view.retainedEntries.get index).boundary.targetSupport.length =
        node.targetBound.length) :
    RhoCollapsingLeafExposure node children right := by
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have atomNormal : (environment.atomValue slot).key.normal =
      ((view.selectedTreeFromForest children index).normalizedBoundaryValue
        rhoHereditaryNormalizationKernel).1 :=
    view.selectedBoundaryAtom_normal_eq
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition children
      (environment := environment) index occurrence occurrenceName slot
      selected
  have selectedNormal :
      ((view.selectedTreeFromForest children index).normalizedBoundaryValue
        rhoHereditaryNormalizationKernel).1 =
          (right.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    rw [CostRegionTree.normalizedBoundaryValue_pattern]
    exact childAlignment.normalize_pattern_eq
  have atomSupport : (environment.atomValue slot).key.targetSupport =
      (view.view.retainedEntries.get index).boundary.targetSupport :=
    view.selectedBoundaryAtom_targetSupport_eq
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition children
      (environment := environment) index occurrence occurrenceName slot
      selected
  apply atomOfSameSupportNormal node children right slot staticFrame
    (atomNormal.trans selectedNormal)
  exact congrArg List.length atomSupport |>.trans sameSupport

/-- Construct the same-support atom exposure through any proof-relevant
elaboration of the selected boundary endpoint.

The recursively constructed left tree need not be definitionally the tree
stored at the retained forest position.  Rho's checked static-decomposition
unambiguity identifies their normalized patterns, after which the supplied
hereditary alignment transports to the structural endpoint.  Thus recursive
closure may choose its own admissible tree without replacing occurrence
identity by an equality search through the boundary table. -/
noncomputable def boundaryElaborationAlignedSameSupport
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {alignedAvailable alignedOuter rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {payload : Pattern}
    (view : CostStaticPlanContextInventoryView rhoCIGSLT color targetFree
      payload node.skeleton.1 node.finiteBoundaryTable.entries)
    (index : Fin view.view.retainedEntries.length)
    (occurrence : CostStaticFVarOccurrence node.skeleton.1)
    (occurrenceName : occurrence.name = costRegionBoundaryVariableName
      (view.view.retainedEntries.get index).boundary)
    {alignedPattern rightPattern : Pattern}
    {alignedType rightType : TypeExpr}
    (leftElaboration : CostRegionTree rhoCIGSLT targetFree
      (view.view.retainedEntries.get index).boundary.targetSupport []
      (view.view.retainedEntries.get index).boundary.content
      (view.view.retainedEntries.get index).boundary.targetType)
    (alignedRight : CostRegionTree rhoCIGSLT targetFree alignedAvailable
      alignedOuter alignedPattern alignedType)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (slot : Fin (node.normalizationEnvironment rhoHereditaryStaticNormalizer
      children).atomCount)
    (selected :
      (node.normalizationEnvironment rhoHereditaryStaticNormalizer children
        ).slotOfName? occurrence.name = some slot)
    (staticFrame :
      node.canonicalizeReifiedTargetFrame
          (node.normalizationEnvironment rhoHereditaryStaticNormalizer
            children)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar ((node.normalizationEnvironment
          rhoHereditaryStaticNormalizer children).atomName slot))
    (childAlignment : CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree leftElaboration alignedRight)
    (alignedToRight :
      (alignedRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern)
    (sameSupport :
      (view.view.retainedEntries.get index).boundary.targetSupport.length =
        node.targetBound.length) :
    RhoCollapsingLeafExposure node children right := by
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have atomNormal : (environment.atomValue slot).key.normal =
      ((view.selectedTreeFromForest children index).normalizedBoundaryValue
        rhoHereditaryNormalizationKernel).1 :=
    view.selectedBoundaryAtom_normal_eq
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition children
      (environment := environment) index occurrence occurrenceName slot
      selected
  have selectedToElaboration :
      ((view.selectedTreeFromForest children index).normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (leftElaboration.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel
      (view.selectedTreeFromForest children index) leftElaboration
      (view.view.retainedEntries.get index).contentObjectPattern
  have selectedNormal :
      ((view.selectedTreeFromForest children index).normalizedBoundaryValue
        rhoHereditaryNormalizationKernel).1 =
          (right.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    rw [CostRegionTree.normalizedBoundaryValue_pattern]
    exact selectedToElaboration.trans
      (childAlignment.normalize_pattern_eq.trans alignedToRight)
  have atomSupport : (environment.atomValue slot).key.targetSupport =
      (view.view.retainedEntries.get index).boundary.targetSupport :=
    view.selectedBoundaryAtom_targetSupport_eq
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition children
      (environment := environment) index occurrence occurrenceName slot
      selected
  apply atomOfSameSupportNormal node children right slot staticFrame
    (atomNormal.trans selectedNormal)
  exact congrArg List.length atomSupport |>.trans sameSupport

/-- Close a stopped context traversal through its exact intercepted boundary.

The stopped state already stores both a one-hole occurrence context in the
root skeleton and the sole retained boundary entry.  This wrapper replays
those proof-relevant positions, recovers the corresponding semantic-atom
slot, and applies `boundaryElaborationAlignedSameSupport`.  In particular it
never searches the root table for an equal boundary value, so duplicate
boundary values remain distinct occurrences even when their semantic atoms
coincide. -/
noncomputable def stoppedBoundaryElaborationAlignedSameSupport
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {payload : Pattern}
    {alignedAvailable alignedOuter rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] node.finiteBoundaryTable.entries)
    {alignedPattern rightPattern : Pattern}
    {alignedType rightType : TypeExpr}
    (leftElaboration : CostRegionTree rhoCIGSLT targetFree
      state.certified.typed.boundary.targetSupport []
      state.certified.typed.boundary.content
      state.certified.typed.boundary.targetType)
    (alignedRight : CostRegionTree rhoCIGSLT targetFree alignedAvailable
      alignedOuter alignedPattern alignedType)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (staticFrame :
      ∀ slot : Fin (node.normalizationEnvironment
        rhoHereditaryStaticNormalizer children).atomCount,
        (node.normalizationEnvironment rhoHereditaryStaticNormalizer children
          ).slotOfName? state.boundaryOccurrence.name = some slot →
        node.canonicalizeReifiedTargetFrame
            (node.normalizationEnvironment rhoHereditaryStaticNormalizer
              children)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation) =
          .fvar ((node.normalizationEnvironment
            rhoHereditaryStaticNormalizer children).atomName slot))
    (childAlignment : CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree leftElaboration alignedRight)
    (alignedToRight :
      (alignedRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern)
    (sameSupport : state.certified.typed.boundary.targetSupport.length =
      node.targetBound.length) :
    RhoCollapsingLeafExposure node children right := by
  let view : CostStaticPlanContextInventoryView rhoCIGSLT color targetFree
      payload node.skeleton.1 node.finiteBoundaryTable.entries :=
    { view := .stopped state
      entryEmbedding := entryEmbedding }
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have slotExists := environment.slotOfName?_isSome_of_occurrence
    state.boundaryOccurrence
  let slot := (environment.slotOfName? state.boundaryOccurrence.name).get
    slotExists
  have selected : environment.slotOfName? state.boundaryOccurrence.name =
      some slot :=
    (Option.some_get slotExists).symm
  have retainedEntryEq :
      view.view.retainedEntries.get state.retainedIndex =
        state.certified.typed := by
    simpa only [view] using state.retainedEntries_get_retainedIndex
  have occurrenceName : state.boundaryOccurrence.name =
      costRegionBoundaryVariableName
        (view.view.retainedEntries.get state.retainedIndex).boundary := by
    calc
      state.boundaryOccurrence.name =
          costRegionBoundaryVariableName state.certified.typed.boundary := rfl
      _ = costRegionBoundaryVariableName
          (view.view.retainedEntries.get state.retainedIndex).boundary :=
        congrArg
          (fun entry : TypedCostRegionBoundary rhoCIGSLT color targetFree =>
            costRegionBoundaryVariableName entry.boundary)
          retainedEntryEq.symm
  have retainedSupportLength :
      (view.view.retainedEntries.get state.retainedIndex).boundary.targetSupport.length =
        node.targetBound.length :=
    (congrArg
      (fun entry : TypedCostRegionBoundary rhoCIGSLT color targetFree =>
        entry.boundary.targetSupport.length)
      retainedEntryEq).trans sameSupport
  exact boundaryElaborationAlignedSameSupport node children view
    state.retainedIndex state.boundaryOccurrence occurrenceName
    leftElaboration alignedRight right slot selected (staticFrame slot selected)
    childAlignment alignedToRight retainedSupportLength

/-- Close a stopped context traversal whose recursively elaborated boundary
normalizes to a structural source variable.

The stopped certificate and entry embedding replay the exact intercepted
occurrence.  Recursive closure may choose its own boundary-content tree; rho
unambiguity transports that tree back to the selected forest child before the
support-independent free-variable terminal is applied. -/
noncomputable def stoppedBoundaryElaborationSourceVariable
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {payload : Pattern}
    {alignedAvailable alignedOuter rightAvailable rightOuter : List TypeExpr}
    {alignedType rightType : TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] node.finiteBoundaryTable.entries)
    (name : String)
    (leftElaboration : CostRegionTree rhoCIGSLT targetFree
      state.certified.typed.boundary.targetSupport []
      state.certified.typed.boundary.content
      state.certified.typed.boundary.targetType)
    (alignedRight : CostRegionTree rhoCIGSLT targetFree alignedAvailable
      alignedOuter (.fvar name) alignedType)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      (.fvar name) rightType)
    (staticFrame :
      ∀ slot : Fin (node.normalizationEnvironment
        rhoHereditaryStaticNormalizer children).atomCount,
        (node.normalizationEnvironment rhoHereditaryStaticNormalizer children
          ).slotOfName? state.boundaryOccurrence.name = some slot →
        node.canonicalizeReifiedTargetFrame
            (node.normalizationEnvironment rhoHereditaryStaticNormalizer
              children)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation) =
          .fvar ((node.normalizationEnvironment
            rhoHereditaryStaticNormalizer children).atomName slot))
    (childAlignment : CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree leftElaboration
        alignedRight) :
    RhoCollapsingLeafExposure node children right := by
  let view : CostStaticPlanContextInventoryView rhoCIGSLT color targetFree
      payload node.skeleton.1 node.finiteBoundaryTable.entries :=
    { view := .stopped state
      entryEmbedding := entryEmbedding }
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have slotExists := environment.slotOfName?_isSome_of_occurrence
    state.boundaryOccurrence
  let slot := (environment.slotOfName? state.boundaryOccurrence.name).get
    slotExists
  have selected : environment.slotOfName? state.boundaryOccurrence.name =
      some slot :=
    (Option.some_get slotExists).symm
  have occurrenceName : state.boundaryOccurrence.name =
      costRegionBoundaryVariableName
        (view.view.retainedEntries.get state.retainedIndex).boundary := by
    rfl
  exact boundaryElaborationSourceVariable node children view
    state.retainedIndex state.boundaryOccurrence occurrenceName name
    leftElaboration alignedRight right slot selected (staticFrame slot selected)
    childAlignment

/-- Close a stopped foreign boundary beneath one exact authored Quote/Drop
shell.

The stopped view already identifies the intercepted occurrence and retains
the executable boundary-certification receipt.  The shell equation determines
the complete atomized source frame, so the selected semantic slot and its
target-frame collapse are derived here rather than supplied by a caller.  The
only semantic input left is the recursive alignment of the certified boundary
content with the opposite endpoint. -/
noncomputable def stoppedQuoteDropBoundaryElaborationAlignedSameSupport
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {payload : Pattern}
    {alignedAvailable alignedOuter rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] node.finiteBoundaryTable.entries)
    (shell : state.skeletonContext =
      .apply rhoReflectivePresentation.quoteConstructor []
        (.apply rhoReflectivePresentation.dropConstructor [] .hole []) [])
    {alignedPattern rightPattern : Pattern}
    {alignedType rightType : TypeExpr}
    (leftElaboration : CostRegionTree rhoCIGSLT targetFree
      state.certified.typed.boundary.targetSupport []
      state.certified.typed.boundary.content
      state.certified.typed.boundary.targetType)
    (alignedRight : CostRegionTree rhoCIGSLT targetFree alignedAvailable
      alignedOuter alignedPattern alignedType)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (childAlignment : CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree leftElaboration alignedRight)
    (alignedToRight :
      (alignedRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern)
    (sameSupport : state.certified.typed.boundary.targetSupport.length =
      node.targetBound.length) :
    RhoCollapsingLeafExposure node children right := by
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have slotExists := environment.slotOfName?_isSome_of_occurrence
    state.boundaryOccurrence
  let slot := (environment.slotOfName? state.boundaryOccurrence.name).get
    slotExists
  have selected : environment.slotOfName? state.boundaryOccurrence.name =
      some slot := (Option.some_get slotExists).symm
  have reifiedFrame :
      (node.reifiedSourceFrame environment).1 =
        .apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor
            [.fvar (environment.atomName slot)]] := by
    rw [node.reifiedSourceFrame_pattern]
    calc
      environment.reify node.skeleton.1 =
          environment.reify
            (state.skeletonContext.fill
              (.fvar (costRegionBoundaryVariableName
                state.certified.typed.boundary))) :=
        congrArg environment.reify state.abstract_eq
      _ = _ := by
        rw [shell]
        simp only [
          Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
          List.nil_append, List.map_singleton,
          CostStaticAtomEnvironment.reify]
        simp only [Pattern.apply.injEq, true_and, List.cons.injEq,
          and_true, Pattern.fvar.injEq]
        change environment.reifyName state.boundaryOccurrence.name =
          environment.atomName slot
        unfold CostStaticAtomEnvironment.reifyName
        rw [selected]
  have staticFrame :
      node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar (environment.atomName slot) :=
    CostStaticRegionNode.canonicalizeReifiedTargetFrame_quoteDrop_atom
      node environment slot reifiedFrame
  exact stoppedBoundaryElaborationAlignedSameSupport node children state
    entryEmbedding leftElaboration alignedRight right
    (fun candidate candidateSelected => by
      have candidateEq : candidate = slot := by
        exact Option.some.inj
          (candidateSelected.symm.trans selected)
      subst candidate
      exact staticFrame)
    childAlignment alignedToRight sameSupport

/-- Support-independent Quote/Drop terminal for a stopped boundary whose
recursive elaboration normalizes to a structural source variable.  The exact
stopped occurrence determines the semantic slot; the authored shell proves
that Quote/Drop exposes precisely that slot. -/
noncomputable def stoppedQuoteDropBoundaryElaborationSourceVariable
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {payload : Pattern}
    {alignedAvailable alignedOuter rightAvailable rightOuter : List TypeExpr}
    {alignedType rightType : TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] node.finiteBoundaryTable.entries)
    (shell : state.skeletonContext =
      .apply rhoReflectivePresentation.quoteConstructor []
        (.apply rhoReflectivePresentation.dropConstructor [] .hole []) [])
    (name : String)
    (leftElaboration : CostRegionTree rhoCIGSLT targetFree
      state.certified.typed.boundary.targetSupport []
      state.certified.typed.boundary.content
      state.certified.typed.boundary.targetType)
    (alignedRight : CostRegionTree rhoCIGSLT targetFree alignedAvailable
      alignedOuter (.fvar name) alignedType)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      (.fvar name) rightType)
    (childAlignment : CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree leftElaboration
        alignedRight) :
    RhoCollapsingLeafExposure node children right := by
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have slotExists := environment.slotOfName?_isSome_of_occurrence
    state.boundaryOccurrence
  let slot := (environment.slotOfName? state.boundaryOccurrence.name).get
    slotExists
  have selected : environment.slotOfName? state.boundaryOccurrence.name =
      some slot := (Option.some_get slotExists).symm
  have reifiedFrame :
      (node.reifiedSourceFrame environment).1 =
        .apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor
            [.fvar (environment.atomName slot)]] := by
    rw [node.reifiedSourceFrame_pattern]
    calc
      environment.reify node.skeleton.1 =
          environment.reify
            (state.skeletonContext.fill
              (.fvar (costRegionBoundaryVariableName
                state.certified.typed.boundary))) :=
        congrArg environment.reify state.abstract_eq
      _ = _ := by
        rw [shell]
        simp only [
          Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
          List.nil_append, List.map_singleton,
          CostStaticAtomEnvironment.reify]
        simp only [Pattern.apply.injEq, true_and, List.cons.injEq,
          and_true, Pattern.fvar.injEq]
        change environment.reifyName state.boundaryOccurrence.name =
          environment.atomName slot
        unfold CostStaticAtomEnvironment.reifyName
        rw [selected]
  have staticFrame :
      node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar (environment.atomName slot) :=
    CostStaticRegionNode.canonicalizeReifiedTargetFrame_quoteDrop_atom
      node environment slot reifiedFrame
  exact stoppedBoundaryElaborationSourceVariable node children state
    entryEmbedding name leftElaboration alignedRight right
    (fun candidate candidateSelected => by
      have candidateEq : candidate = slot := by
        exact Option.some.inj
          (candidateSelected.symm.trans selected)
      subst candidate
      exact staticFrame)
    childAlignment

/-- Close a stopped foreign boundary beneath one bare-parallel singleton
shell.

As in the Quote/Drop terminal, the stopped view supplies the exact authored
occurrence and its certification receipt.  The singleton shell determines the
complete atomized source frame; singleton collapse then exposes the selected
semantic atom without requiring the caller to name a slot or a canonical
frame. -/
noncomputable def stoppedParallelSingletonBoundaryElaborationAlignedSameSupport
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {payload : Pattern}
    {alignedAvailable alignedOuter rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] node.finiteBoundaryTable.entries)
    (shell : state.skeletonContext =
      .collection rhoReflectivePresentation.parallelCollection
        [] .hole [] none)
    {alignedPattern rightPattern : Pattern}
    {alignedType rightType : TypeExpr}
    (leftElaboration : CostRegionTree rhoCIGSLT targetFree
      state.certified.typed.boundary.targetSupport []
      state.certified.typed.boundary.content
      state.certified.typed.boundary.targetType)
    (alignedRight : CostRegionTree rhoCIGSLT targetFree alignedAvailable
      alignedOuter alignedPattern alignedType)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (childAlignment : CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree leftElaboration alignedRight)
    (alignedToRight :
      (alignedRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern)
    (sameSupport : state.certified.typed.boundary.targetSupport.length =
      node.targetBound.length) :
    RhoCollapsingLeafExposure node children right := by
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have slotExists := environment.slotOfName?_isSome_of_occurrence
    state.boundaryOccurrence
  let slot := (environment.slotOfName? state.boundaryOccurrence.name).get
    slotExists
  have selected : environment.slotOfName? state.boundaryOccurrence.name =
      some slot := (Option.some_get slotExists).symm
  have reifiedFrame :
      (node.reifiedSourceFrame environment).1 =
        .collection rhoReflectivePresentation.parallelCollection
          [.fvar (environment.atomName slot)] none := by
    rw [node.reifiedSourceFrame_pattern]
    calc
      environment.reify node.skeleton.1 =
          environment.reify
            (state.skeletonContext.fill
              (.fvar (costRegionBoundaryVariableName
                state.certified.typed.boundary))) :=
        congrArg environment.reify state.abstract_eq
      _ = _ := by
        rw [shell]
        simp only [
          Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
          List.nil_append, List.map_singleton,
          CostStaticAtomEnvironment.reify]
        simp only [Pattern.collection.injEq, true_and, List.cons.injEq,
          and_true, Pattern.fvar.injEq]
        change environment.reifyName state.boundaryOccurrence.name =
          environment.atomName slot
        unfold CostStaticAtomEnvironment.reifyName
        rw [selected]
  have staticFrame :
      node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar (environment.atomName slot) :=
    CostStaticRegionNode.canonicalizeReifiedTargetFrame_parallelSingleton_atom
      node environment slot reifiedFrame
  exact stoppedBoundaryElaborationAlignedSameSupport node children state
    entryEmbedding leftElaboration alignedRight right
    (fun candidate candidateSelected => by
      have candidateEq : candidate = slot := by
        exact Option.some.inj
          (candidateSelected.symm.trans selected)
      subst candidate
      exact staticFrame)
    childAlignment alignedToRight sameSupport

/-- Support-independent bare-parallel singleton terminal for a stopped
boundary whose recursive elaboration normalizes to a structural source
variable.  Multiplicity is retained by the stopped occurrence and entry
embedding until the selected semantic slot has been fixed. -/
noncomputable def stoppedParallelSingletonBoundaryElaborationSourceVariable
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {payload : Pattern}
    {alignedAvailable alignedOuter rightAvailable rightOuter : List TypeExpr}
    {alignedType rightType : TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] node.finiteBoundaryTable.entries)
    (shell : state.skeletonContext =
      .collection rhoReflectivePresentation.parallelCollection
        [] .hole [] none)
    (name : String)
    (leftElaboration : CostRegionTree rhoCIGSLT targetFree
      state.certified.typed.boundary.targetSupport []
      state.certified.typed.boundary.content
      state.certified.typed.boundary.targetType)
    (alignedRight : CostRegionTree rhoCIGSLT targetFree alignedAvailable
      alignedOuter (.fvar name) alignedType)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      (.fvar name) rightType)
    (childAlignment : CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree leftElaboration
        alignedRight) :
    RhoCollapsingLeafExposure node children right := by
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have slotExists := environment.slotOfName?_isSome_of_occurrence
    state.boundaryOccurrence
  let slot := (environment.slotOfName? state.boundaryOccurrence.name).get
    slotExists
  have selected : environment.slotOfName? state.boundaryOccurrence.name =
      some slot := (Option.some_get slotExists).symm
  have reifiedFrame :
      (node.reifiedSourceFrame environment).1 =
        .collection rhoReflectivePresentation.parallelCollection
          [.fvar (environment.atomName slot)] none := by
    rw [node.reifiedSourceFrame_pattern]
    calc
      environment.reify node.skeleton.1 =
          environment.reify
            (state.skeletonContext.fill
              (.fvar (costRegionBoundaryVariableName
                state.certified.typed.boundary))) :=
        congrArg environment.reify state.abstract_eq
      _ = _ := by
        rw [shell]
        simp only [
          Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
          List.nil_append, List.map_singleton,
          CostStaticAtomEnvironment.reify]
        simp only [Pattern.collection.injEq, true_and, List.cons.injEq,
          and_true, Pattern.fvar.injEq]
        change environment.reifyName state.boundaryOccurrence.name =
          environment.atomName slot
        unfold CostStaticAtomEnvironment.reifyName
        rw [selected]
  have staticFrame :
      node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar (environment.atomName slot) :=
    CostStaticRegionNode.canonicalizeReifiedTargetFrame_parallelSingleton_atom
      node environment slot reifiedFrame
  exact stoppedBoundaryElaborationSourceVariable node children state
    entryEmbedding name leftElaboration alignedRight right
    (fun candidate candidateSelected => by
      have candidateEq : candidate = slot := by
        exact Option.some.inj
          (candidateSelected.symm.trans selected)
      subst candidate
      exact staticFrame)
    childAlignment

/-- Lift one already-closed boundary pair through an exact stopped Quote/Drop
occurrence.

This is the non-recursive semantic core of the Quote/Drop step.  The child
pair lives in the certified boundary fibre and may use independently chosen
trees.  Its right tree is weakened beneath the root's ambient outer context;
static decomposition unambiguity then relates that choice to the caller's
actual right endpoint. -/
noncomputable def stoppedQuoteDropPairElaboration
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftView : left.StaticRootView color)
    (rightObject : isObjectPattern rightPattern = true)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      leftView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] leftView.node.finiteBoundaryTable.entries)
    (shell : state.skeletonContext =
      .apply rhoReflectivePresentation.quoteConstructor []
        (.apply rhoReflectivePresentation.dropConstructor [] .hole []) [])
    (boundarySupport :
      state.certified.typed.boundary.targetSupport = available)
    (boundaryType : state.certified.typed.boundary.targetType = type)
    (childPair : CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      state.certified.typed.boundary.targetSupport []
      state.certified.typed.boundary.content rightPattern
      state.certified.typed.boundary.targetType) :
    CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree available outer leftPattern
      rightPattern type := by
  let ambientRight : CostRegionTree rhoCIGSLT targetFree available outer
      rightPattern type :=
    ((childPair.rightTree.extendOuter outer).reindexAvailable boundarySupport
      ).reindexType boundaryType
  have childToAmbient :
      (childPair.rightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (ambientRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    have typeReindex := CostRegionTree.reindexType_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer) boundaryType
      ((childPair.rightTree.extendOuter outer).reindexAvailable
        boundarySupport)
    have supportReindex := CostRegionTree.reindexAvailable_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer) boundarySupport
      (childPair.rightTree.extendOuter outer)
    have weakened := childPair.rightTree.extendOuter_normalize_pattern outer
      rhoHereditaryStaticNormalizer
    exact (typeReindex.trans (supportReindex.trans weakened)).symm
  have ambientToRight :
      (ambientRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel ambientRight right
      rightObject
  have exposure := stoppedQuoteDropBoundaryElaborationAlignedSameSupport
    leftView.node leftView.children state entryEmbedding shell
      childPair.leftTree childPair.rightTree right childPair.alignment
      (childToAmbient.trans ambientToRight)
      (congrArg List.length (boundarySupport.trans leftView.availableEq.symm))
  exact
    { leftTree := left
      rightTree := right
      alignment :=
        (leftView.rootBridge_reindex_left
          exposure.toRootBridge).toTreeAlignment }

/-- Recursive Quote/Drop closure at an exact stopped boundary occurrence.

The caller supplies only the local parent pair and the generic strictly-
smaller elaboration interface.  The theorem replays the stopped occurrence,
proves that its certified boundary content is a proper subproblem of the
static root, invokes recursive closure on that content versus the exposed
free name, and feeds the returned proof-relevant alignment into the
support-independent Quote/Drop terminal.  The resulting pair elaboration
uses the actual static tree together with an independently typed structural
free-variable tree; recursive tree choice is therefore never confused with
endpoint identity. -/
noncomputable def stoppedQuoteDropSourceVariablePairElaborationOfCloseSmaller
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (leftView : left.StaticRootView color)
    (name : String)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type (.fvar name))
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      leftView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] leftView.node.finiteBoundaryTable.entries)
    (shell : state.skeletonContext =
      .apply rhoReflectivePresentation.quoteConstructor []
        (.apply rhoReflectivePresentation.dropConstructor [] .hole []) [])
    (boundaryCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          state.certified.typed.boundary.content =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          (.fvar name))
    (boundaryType : state.certified.typed.boundary.targetType = type)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftPattern + sizeOf (Pattern.fvar name) →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree available outer leftPattern
      (Pattern.fvar name) type := by
  have boundaryWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree state.certified.typed.boundary.targetSupport
      state.certified.typed.boundary.targetType
      state.certified.typed.boundary.content :=
    ⟨⟨state.certified.typed.contentTyped,
        state.certified.typed.contentCanonicalBinderMetadata,
        state.certified.typed.contentObjectPattern,
        state.certified.typed.contentTyped.isWellScopedAt⟩,
      state.certified.typed.contentReflectiveScopeSafe⟩
  have nameLookup : targetFree name = some type := by
    cases rightWellSorted.1.1 with
    | fvar lookup => exact lookup
  have boundaryNameWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree state.certified.typed.boundary.targetSupport
      state.certified.typed.boundary.targetType (.fvar name) := by
    have boundaryNameLookup : targetFree name =
        some state.certified.typed.boundary.targetType := by
      rw [boundaryType]
      exact nameLookup
    exact ⟨⟨WellSorted.HasType.fvar boundaryNameLookup, rfl, rfl, rfl⟩,
      by
        intro presentation membership
        rfl⟩
  have boundaryMember : state.certified.typed ∈
      leftView.node.plan.boundaryTable.entries :=
    entryEmbedding.subset (by simp)
  have boundarySmaller :
      sizeOf state.certified.typed.boundary.content +
          sizeOf (Pattern.fvar name) <
        sizeOf leftPattern + sizeOf (Pattern.fvar name) := by
    have contentLt :=
      leftView.node.plan.boundary_content_size_lt_of_isStaticRoot
        leftView.node.rootStatic state.certified.typed boundaryMember
    have nodePatternEq : leftView.node.term.1 = leftPattern :=
      leftView.patternEq
    have contentLt' :
        sizeOf state.certified.typed.boundary.content < sizeOf leftPattern := by
      calc
        sizeOf state.certified.typed.boundary.content <
            sizeOf leftView.node.term.1 := contentLt
        _ = sizeOf leftPattern := congrArg sizeOf nodePatternEq
    omega
  have childAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      state.certified.typed.boundary.targetType := by
    exact (leftView.typeEq.trans boundaryType.symm) ▸
      rhoCanonicalRecursiveTypeDomain.base _
  let childPair := Classical.choice
    (closeSmaller (childOuter := []) boundaryWellSorted
      boundaryNameWellSorted boundaryCanonical boundarySmaller
        childAdmissible)
  let rightTree : CostRegionTree rhoCIGSLT targetFree available outer
      (Pattern.fvar name) type := CostRegionTree.fvar nameLookup
  have exposure := stoppedQuoteDropBoundaryElaborationSourceVariable
    leftView.node leftView.children state entryEmbedding shell name
      childPair.leftTree childPair.rightTree rightTree childPair.alignment
  exact
    { leftTree := left
      rightTree := rightTree
      alignment :=
        (leftView.rootBridge_reindex_left
          exposure.toRootBridge).toTreeAlignment }

/-- Recursive Quote/Drop closure at an exact stopped boundary occurrence.

Unlike the source-variable specialization above, the opposite endpoint may be
an arbitrary well-sorted canonical pattern.  Recursive closure is performed in
the certified boundary fibre.  Its chosen right tree is then weakened beneath
the ambient outer context and compared with the actual endpoint using static
decomposition unambiguity.  Consequently neither recursive tree choice nor an
equality of endpoints is smuggled into the enclosing root bridge. -/
noncomputable def stoppedQuoteDropPairElaborationOfCloseSmaller
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftView : left.StaticRootView color)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      leftView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] leftView.node.finiteBoundaryTable.entries)
    (shell : state.skeletonContext =
      .apply rhoReflectivePresentation.quoteConstructor []
        (.apply rhoReflectivePresentation.dropConstructor [] .hole []) [])
    (boundaryCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          state.certified.typed.boundary.content =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          rightPattern)
    (boundarySupport :
      state.certified.typed.boundary.targetSupport = available)
    (boundaryType : state.certified.typed.boundary.targetType = type)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftPattern + sizeOf rightPattern →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree available outer leftPattern
      rightPattern type := by
  have boundaryWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree state.certified.typed.boundary.targetSupport
      state.certified.typed.boundary.targetType
      state.certified.typed.boundary.content :=
    ⟨⟨state.certified.typed.contentTyped,
        state.certified.typed.contentCanonicalBinderMetadata,
        state.certified.typed.contentObjectPattern,
        state.certified.typed.contentTyped.isWellScopedAt⟩,
      state.certified.typed.contentReflectiveScopeSafe⟩
  have boundaryRightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree state.certified.typed.boundary.targetSupport
      state.certified.typed.boundary.targetType rightPattern := by
    simpa only [boundarySupport, boundaryType] using rightWellSorted
  have boundaryMember : state.certified.typed ∈
      leftView.node.plan.boundaryTable.entries :=
    entryEmbedding.subset (by simp)
  have boundarySmaller :
      sizeOf state.certified.typed.boundary.content + sizeOf rightPattern <
        sizeOf leftPattern + sizeOf rightPattern := by
    have contentLt :=
      leftView.node.plan.boundary_content_size_lt_of_isStaticRoot
        leftView.node.rootStatic state.certified.typed boundaryMember
    have nodePatternEq : leftView.node.term.1 = leftPattern :=
      leftView.patternEq
    have contentLt' :
        sizeOf state.certified.typed.boundary.content < sizeOf leftPattern := by
      calc
        sizeOf state.certified.typed.boundary.content <
            sizeOf leftView.node.term.1 := contentLt
        _ = sizeOf leftPattern := congrArg sizeOf nodePatternEq
    omega
  have childAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      state.certified.typed.boundary.targetType := by
    exact (leftView.typeEq.trans boundaryType.symm) ▸
      rhoCanonicalRecursiveTypeDomain.base _
  let childPair := Classical.choice
    (closeSmaller (childOuter := []) boundaryWellSorted
      boundaryRightWellSorted boundaryCanonical boundarySmaller
        childAdmissible)
  exact stoppedQuoteDropPairElaboration left right leftView
    rightWellSorted.1.2.2.1 state entryEmbedding shell boundarySupport
    boundaryType childPair

/-- Recursive singleton-parallel closure at an exact stopped boundary
occurrence.

The boundary support equality is stronger than the length equality needed by
restoration: it lets recursive closure compare the intercepted child with the
structural endpoint in one exact typed fibre.  The recursive right tree is
then weakened beneath the ambient outer context and compared with the actual
endpoint by decomposition unambiguity.  Thus the exact stopped occurrence is
retained while the recursive elaborator remains free to choose its own trees. -/
noncomputable def stoppedParallelSingletonPairElaborationOfCloseSmaller
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftView : left.StaticRootView color)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      leftView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] leftView.node.finiteBoundaryTable.entries)
    (shell : state.skeletonContext =
      .collection rhoReflectivePresentation.parallelCollection
        [] .hole [] none)
    (boundaryCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          state.certified.typed.boundary.content =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          rightPattern)
    (boundarySupport :
      state.certified.typed.boundary.targetSupport = available)
    (boundaryType : state.certified.typed.boundary.targetType = type)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftPattern + sizeOf rightPattern →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree available outer leftPattern
      rightPattern type := by
  have boundaryWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree state.certified.typed.boundary.targetSupport
      state.certified.typed.boundary.targetType
      state.certified.typed.boundary.content :=
    ⟨⟨state.certified.typed.contentTyped,
        state.certified.typed.contentCanonicalBinderMetadata,
        state.certified.typed.contentObjectPattern,
        state.certified.typed.contentTyped.isWellScopedAt⟩,
      state.certified.typed.contentReflectiveScopeSafe⟩
  have boundaryRightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree state.certified.typed.boundary.targetSupport
      state.certified.typed.boundary.targetType rightPattern := by
    simpa only [boundarySupport, boundaryType] using rightWellSorted
  have boundaryMember : state.certified.typed ∈
      leftView.node.plan.boundaryTable.entries :=
    entryEmbedding.subset (by simp)
  have boundarySmaller :
      sizeOf state.certified.typed.boundary.content + sizeOf rightPattern <
        sizeOf leftPattern + sizeOf rightPattern := by
    have contentLt :=
      leftView.node.plan.boundary_content_size_lt_of_isStaticRoot
        leftView.node.rootStatic state.certified.typed boundaryMember
    have nodePatternEq : leftView.node.term.1 = leftPattern :=
      leftView.patternEq
    have contentLt' :
        sizeOf state.certified.typed.boundary.content < sizeOf leftPattern := by
      calc
        sizeOf state.certified.typed.boundary.content <
            sizeOf leftView.node.term.1 := contentLt
        _ = sizeOf leftPattern := congrArg sizeOf nodePatternEq
    omega
  have childAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      state.certified.typed.boundary.targetType := by
    exact (leftView.typeEq.trans boundaryType.symm) ▸
      rhoCanonicalRecursiveTypeDomain.base _
  let childPair := Classical.choice
    (closeSmaller (childOuter := []) boundaryWellSorted
      boundaryRightWellSorted boundaryCanonical boundarySmaller
        childAdmissible)
  let ambientRight : CostRegionTree rhoCIGSLT targetFree available outer
      rightPattern type :=
    ((childPair.rightTree.extendOuter outer).reindexAvailable boundarySupport
      ).reindexType boundaryType
  have childToAmbient :
      (childPair.rightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (ambientRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    have typeReindex := CostRegionTree.reindexType_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer) boundaryType
      ((childPair.rightTree.extendOuter outer).reindexAvailable
        boundarySupport)
    have supportReindex := CostRegionTree.reindexAvailable_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer) boundarySupport
      (childPair.rightTree.extendOuter outer)
    have weakened := childPair.rightTree.extendOuter_normalize_pattern outer
      rhoHereditaryStaticNormalizer
    exact (typeReindex.trans (supportReindex.trans weakened)).symm
  have ambientToRight :
      (ambientRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel ambientRight right
      rightWellSorted.1.2.2.1
  have alignedToRight := childToAmbient.trans ambientToRight
  have exposure := stoppedParallelSingletonBoundaryElaborationAlignedSameSupport
    leftView.node leftView.children state entryEmbedding shell
      childPair.leftTree childPair.rightTree right childPair.alignment
      alignedToRight
      (congrArg List.length (boundarySupport.trans leftView.availableEq.symm))
  exact
    { leftTree := left
      rightTree := right
      alignment :=
        (leftView.rootBridge_reindex_left
          exposure.toRootBridge).toTreeAlignment }

/-- Construct the atom branch when a collapsing static frame exposes an
authored source-variable occurrence as its complete canonical result.

The collapsing shell is deliberately absent from this theorem: Quote/Drop
and singleton parallel collapse supply only `staticFrame`.  Restoration of
the selected semantic atom to the structural free-variable tree follows
uniformly from the occurrence-indexed inventory. -/
noncomputable def sourceVariable
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {rightAvailable rightOuter : List TypeExpr}
    {rightType : TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (occurrence : CostStaticFVarOccurrence node.skeleton.1)
    (name : String)
    (occurrenceName : occurrence.name = costRegionSourceVariableName name)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      (.fvar name) rightType)
    (slot : Fin (node.normalizationEnvironment rhoHereditaryStaticNormalizer
      children).atomCount)
    (selected :
      (node.normalizationEnvironment rhoHereditaryStaticNormalizer children
        ).slotOfName? occurrence.name = some slot)
    (staticFrame :
      node.canonicalizeReifiedTargetFrame
          (node.normalizationEnvironment rhoHereditaryStaticNormalizer
            children)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar ((node.normalizationEnvironment
          rhoHereditaryStaticNormalizer children).atomName slot)) :
    RhoCollapsingLeafExposure node children right := by
  let values := children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have rightNormal :
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          .fvar name := by
    let view := right.structuralRootView right.rootIsStatic_eq_false_of_fvar
    cases view with
    | fvar lookup => simp [CostRegionTree.normalize]
  have restored :
      environment.restore node.targetBound
          (.fvar (environment.atomName slot)) =
        .fvar name := by
    unfold CostStaticAtomEnvironment.restore CostStaticAtomEnvironment.restoreAt
    rw [environment.substituteAt_atomName_eq_substituteAt_occurrence
      occurrence slot selected node.targetBound.length]
    simp [occurrenceName, ReflectiveContextSupport.substituteAt,
      TypedCostRegionBoundaryTable.Values.assignment,
      Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]
  exact .atom slot staticFrame (rightNormal.trans restored.symm)

/-- Construct the atom branch for the direct source-variable subcase of a
rho Quote/Drop collapse.  The finite slot is recovered from an actual
occurrence in the static node's certified skeleton; the endpoint
factorization is then derived from the existing semantic-atom join. -/
noncomputable def quoteDropSourceVariable
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {rightAvailable rightOuter : List TypeExpr}
    {rightType : TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (occurrence : CostStaticFVarOccurrence node.skeleton.1)
    (name : String)
    (occurrenceName : occurrence.name = costRegionSourceVariableName name)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      (.fvar name) rightType)
    (slot : Fin (node.normalizationEnvironment rhoHereditaryStaticNormalizer
      children).atomCount)
    (selected :
      (node.normalizationEnvironment rhoHereditaryStaticNormalizer children
        ).slotOfName? occurrence.name = some slot)
    (reifiedFrame :
      (node.reifiedSourceFrame
        (node.normalizationEnvironment rhoHereditaryStaticNormalizer
          children)).1 =
        .apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor
            [.fvar ((node.normalizationEnvironment
              rhoHereditaryStaticNormalizer children).atomName slot)]]) :
    RhoCollapsingLeafExposure node children right := by
  let values := children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have staticFrame :
      node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar (environment.atomName slot) :=
    CostStaticRegionNode.canonicalizeReifiedTargetFrame_quoteDrop_atom
      node environment slot reifiedFrame
  exact sourceVariable node children occurrence name occurrenceName right slot
    selected staticFrame

end RhoCollapsingLeafExposure

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
