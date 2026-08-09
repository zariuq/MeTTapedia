import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRestorationClosure
import Mettapedia.GSLT.LanguageDef.CostCanonicalStructuralAlignment
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

/-- Construct the atom branch when a collapsing static frame exposes an
authored source-variable occurrence as its complete canonical result.

The collapsing shell is deliberately absent from this theorem: Quote/Drop
and singleton parallel collapse supply only `staticFrame`.  Restoration of
the selected semantic atom to the structural free-variable tree follows
uniformly from the occurrence-indexed inventory. -/
noncomputable def sourceVariable
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (occurrence : CostStaticFVarOccurrence node.skeleton.1)
    (name : String)
    (occurrenceName : occurrence.name = costRegionSourceVariableName name)
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
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (occurrence : CostStaticFVarOccurrence node.skeleton.1)
    (name : String)
    (occurrenceName : occurrence.name = costRegionSourceVariableName name)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      (.fvar name) (.base (costBaseSortName "Name")))
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

end RhoCollapsingLeafExposure

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
