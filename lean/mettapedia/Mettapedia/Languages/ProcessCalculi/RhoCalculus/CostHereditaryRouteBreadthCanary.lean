import Mettapedia.GSLT.LanguageDef.CostHereditaryContextRoute
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonical
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalCanary

/-!
# Breadth preflight: a two-sibling reflective rho Cost occurrence

A reflective generator identifies any two patterns with equal canonical
representatives under one generated declaration.  Because rho's interaction
cut makes the base copies of `PInput` and `POutput` genuine neutral
constructors, a single reflective occurrence can change two sibling arguments
of one neutral frame independently.

This file compiles the smallest such witness: a base-colour `POutput` whose
name argument and whose wrapped continuation argument each carry their own
base Quote/Drop collapse.  The single-occurrence normalization route permits
exactly one active child through a neutral frame, so this witness refutes
structural single-path descent: every route between trees of the two
endpoints is forced into a root cell spanning the whole neutral frame.  The
route carrier does not index root cells by static-root admissibility, so
this is deliberately not a non-inhabitation theorem for the unrestricted
route type; a literal exclusion would first strengthen `.root` with an
admissibility witness.  The multi-child
`CostRegionTreeNormalizationAlignment` carrier accommodates the witness
directly, so the total classifier obligation is
`CostOpenGeneratorTreeAlignable`, with routes retained for single-path
occurrence classes.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalCanary

/-- Left continuation sibling: a wrapped drop whose base-sorted name argument
carries its own base Quote/Drop cell. -/
def rhoBreadthLeftProcess : Pattern :=
  rhoCutOrderWrappedDrop
    (rhoCutOrderBaseQuote (rhoCutOrderBaseDrop (.fvar "a")))

/-- Right continuation sibling: the same wrapped drop after the inner base
Quote/Drop collapse. -/
def rhoBreadthRightProcess : Pattern :=
  rhoCutOrderWrappedDrop (.fvar "a")

/-- Wire name of the neutral base-colour output frame. -/
def rhoBreadthOutputName : String := costBaseConstructorName "POutput"

/-- Left endpoint: both siblings of the neutral frame carry an uncollapsed
base Quote/Drop cell. -/
def rhoBreadthLeftPattern : Pattern :=
  .apply rhoBreadthOutputName [rhoCutOrderRedex, rhoBreadthLeftProcess]

/-- Right endpoint: both sibling cells are collapsed. -/
def rhoBreadthRightPattern : Pattern :=
  .apply rhoBreadthOutputName [.fvar "0", rhoBreadthRightProcess]

private theorem rhoBreadthRule_mem (index : Nat) (inBounds : index < 6) :
    rhoCalc.terms[index]'(by simp [rhoCalc]; omega) ∈ rhoCalc.terms :=
  List.getElem_mem _

private theorem rhoBreadthZero_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      (.fvar "0") (.base (costBaseSortName "Name")) :=
  .fvar (by simp [rhoCutOrderFree, FreeTypeContext.ofList])

private theorem rhoBreadthA_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      (.fvar "a") (.base (costBaseSortName "Name")) :=
  .fvar (by simp [rhoCutOrderFree, FreeTypeContext.ofList])

private theorem rhoBreadthBaseDrop_typed (name : Pattern)
    (typed : HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree [] name
      (.base (costBaseSortName "Name"))) :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      (rhoCutOrderBaseDrop name) (.base (costBaseSortName "Proc")) := by
  apply HasType.constructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[1])
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _
      (rhoBreadthRule_mem 1 (by omega))
  · rw [usesBareCollection_costBaseConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costBaseDropConstructor_params]
    exact .cons (by trivial) rfl typed .nil

private theorem rhoBreadthBaseQuote_typed (process : Pattern)
    (typed : HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree [] process
      (.base (costBaseSortName "Proc"))) :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      (rhoCutOrderBaseQuote process) (.base (costBaseSortName "Name")) := by
  apply HasType.constructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[2])
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _
      (rhoBreadthRule_mem 2 (by omega))
  · rw [usesBareCollection_costBaseConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costBaseQuoteConstructor_params]
    exact .cons (by trivial) rfl typed .nil

private def rhoBreadthDropConstructor :
    AuthoredConstructor rhoIGSLT.presentation.presentation :=
  ⟨rhoCalc.terms[1], rhoBreadthRule_mem 1 (by omega)⟩

private theorem rhoBreadthDrop_selected :
    rhoBreadthDropConstructor ∈
      rhoContinuationRetyping.wrappedConstructors := by
  apply (rhoContinuationRetyping.mem_wrappedConstructors_iff
    rhoBreadthDropConstructor).2
  constructor <;> decide

private theorem rhoBreadthWrappedDrop_mem :
    costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[1] ∈
      rhoCIGSLT.costWholeLanguage.terms := by
  change costWrappedConstructor (theory := rhoCIGSLT.theory)
      rhoBreadthDropConstructor.1 ∈ rhoCIGSLT.costWholeLanguage.terms
  exact rhoCIGSLT.costWrappedConstructor_mem_costWhole
    rhoBreadthDropConstructor rhoBreadthDrop_selected

private theorem rhoBreadthWrappedDrop_typed (name : Pattern)
    (typed : HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree [] name
      (.base (costBaseSortName "Name"))) :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      (rhoCutOrderWrappedDrop name) (.base costWrappedSortName) := by
  apply HasType.constructor
      (rule := costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[1])
  · exact rhoBreadthWrappedDrop_mem
  · rw [usesBareCollection_costWrappedConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costWrappedDropConstructor_params]
    exact .cons (by trivial) rfl typed .nil

theorem rhoBreadthLeft_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      rhoBreadthLeftPattern (.base (costBaseSortName "Proc")) := by
  apply HasType.constructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[4])
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _
      (rhoBreadthRule_mem 4 (by omega))
  · rw [usesBareCollection_costBaseConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costBaseOutputConstructor_params]
    exact .cons (by trivial) rfl
      (rhoBreadthBaseQuote_typed _
        (rhoBreadthBaseDrop_typed _ rhoBreadthZero_typed))
      (.cons (by trivial) rfl
        (rhoBreadthWrappedDrop_typed _
          (rhoBreadthBaseQuote_typed _
            (rhoBreadthBaseDrop_typed _ rhoBreadthA_typed)))
        .nil)

theorem rhoBreadthRight_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      rhoBreadthRightPattern (.base (costBaseSortName "Proc")) := by
  apply HasType.constructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[4])
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _
      (rhoBreadthRule_mem 4 (by omega))
  · rw [usesBareCollection_costBaseConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costBaseOutputConstructor_params]
    exact .cons (by trivial) rfl rhoBreadthZero_typed
      (.cons (by trivial) rfl
        (rhoBreadthWrappedDrop_typed _ rhoBreadthA_typed) .nil)

/-- Generated base process sort of the breadth witness. -/
def rhoBreadthBaseProcSort : LangSort rhoCIGSLT.costWholeLanguage :=
  CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc

/-- Checked left endpoint. -/
def rhoBreadthLeft : OpenTerm rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
    rhoBreadthBaseProcSort := by
  exact ⟨rhoBreadthLeftPattern, rhoBreadthLeft_typed, rfl, rfl, by
    intro declaration membership
    simp [rhoBreadthLeftPattern, rhoBreadthLeftProcess,
      rhoBreadthOutputName, rhoCutOrderRedex, rhoCutOrderBaseQuote,
      rhoCutOrderBaseDrop, rhoCutOrderWrappedDrop, binderSafeAt,
      binderSafeListAt]⟩

/-- Checked right endpoint. -/
def rhoBreadthRight : OpenTerm rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
    rhoBreadthBaseProcSort := by
  exact ⟨rhoBreadthRightPattern, rhoBreadthRight_typed, rfl, rfl, by
    intro declaration membership
    simp [rhoBreadthRightPattern, rhoBreadthRightProcess,
      rhoBreadthOutputName, rhoCutOrderWrappedDrop, binderSafeAt,
      binderSafeListAt]⟩

/-- Two independently canonicalized sibling collapses beneath one neutral
frame form a single authored reflective occurrence. -/
def rhoBreadthGeneratorWitness :
    EquationSemantics.AuthoredGeneratorWitness defaultBasePremises
      rhoCIGSLT.costWholeLanguage rhoBreadthLeft.1 rhoBreadthRight.1 := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT .base
    rhoReflectivePresentation.toReflectivePresentationDecl
  have membership : declaration ∈
      rhoCIGSLT.costWholeLanguage.reflectivePresentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl
        (by simp [rhoCIGSLT, rhoIGSLT, rhoInteractivePresentation,
          rhoValidatedLanguageDef, rhoCalc])
  have representatives :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          rhoBreadthLeftPattern =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          rhoBreadthRightPattern := by
    simp [declaration, rhoBreadthLeftPattern, rhoBreadthRightPattern,
      rhoBreadthLeftProcess, rhoBreadthRightProcess, rhoBreadthOutputName,
      rhoCutOrderRedex, rhoCutOrderBaseQuote, rhoCutOrderBaseDrop,
      rhoCutOrderWrappedDrop,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
      Mettapedia.GSLT.LanguageDef.mapReflectivePresentation,
      rhoReflectivePresentation, CostStaticColor.constructorTag,
      costBaseConstructorName, costBaseConstructorTag,
      costWrappedConstructorName, costWrappedConstructorTag]
  exact EquationSemantics.AuthoredGeneratorWitness.reflective .hole
    ⟨declaration, membership⟩ representatives

/-- The breadth witness is a genuine generated edge in its typed fibre. -/
theorem rhoBreadth_generator :
    openEquationGenerator rhoCIGSLT.costIGSLT rhoCutOrderFree []
      rhoBreadthBaseProcSort rhoBreadthLeft rhoBreadthRight :=
  rhoBreadthGeneratorWitness.erase

/-- A single-active-child spine route through a two-argument frame forces at
least one sibling's compact pattern to coincide on both sides. -/
theorem spineRoute_sibling_eq
    {available outer : List TypeExpr}
    {leftFirst leftSecond rightFirst rightSecond : Pattern}
    {parameters : List TermParam}
    {leftTrees : CostRegionArgumentTrees rhoCIGSLT rhoCutOrderFree available
      outer [leftFirst, leftSecond] parameters}
    {rightTrees : CostRegionArgumentTrees rhoCIGSLT rhoCutOrderFree available
      outer [rightFirst, rightSecond] parameters}
    (route : CostRegionArgumentTreesNormalizationRoute rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree leftTrees rightTrees) :
    leftFirst = rightFirst ∨ leftSecond = rightSecond := by
  cases route with
  | head leftRepresentation rightRepresentation parameterType left right tail
      active =>
      exact Or.inr rfl
  | tail representation parameterType head left right active =>
      exact Or.inl rfl

/-- Neither sibling of the breadth witness coincides across the generated
edge, so the neutral output frame admits no single-active-child spine route. -/
theorem rhoBreadth_spineRoute_empty
    {available outer : List TypeExpr}
    {parameters : List TermParam}
    {leftTrees : CostRegionArgumentTrees rhoCIGSLT rhoCutOrderFree available
      outer [rhoCutOrderRedex, rhoBreadthLeftProcess] parameters}
    {rightTrees : CostRegionArgumentTrees rhoCIGSLT rhoCutOrderFree available
      outer [.fvar "0", rhoBreadthRightProcess] parameters} :
    IsEmpty (CostRegionArgumentTreesNormalizationRoute rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree leftTrees
        rightTrees) := by
  constructor
  intro route
  rcases spineRoute_sibling_eq route with names | processes
  · exact absurd names (by decide)
  · exact absurd processes (by decide)

/-- Every normalization route between endpoint trees of the breadth witness
degenerates to one root cell over the whole neutral frame: the structural
congruence layer cannot carry two changed siblings, and no other structural
constructor matches the neutral application.

This refutes structural single-path descent only.  The route carrier's
`.root` accepts a bridge over arbitrary endpoint trees without a static-root
admissibility index, so route non-inhabitation is not claimed here. -/
theorem rhoBreadth_route_forces_root
    {leftAvailable leftOuter rightAvailable rightOuter : List TypeExpr}
    {leftPattern rightPattern : Pattern} {leftType rightType : TypeExpr}
    {left : CostRegionTree rhoCIGSLT rhoCutOrderFree leftAvailable leftOuter
      leftPattern leftType}
    {right : CostRegionTree rhoCIGSLT rhoCutOrderFree rightAvailable
      rightOuter rightPattern rightType}
    (route : CostRegionTreeNormalizationRoute rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree left right)
    (leftPatternEq : leftPattern = rhoBreadthLeftPattern)
    (rightPatternEq : rightPattern = rhoBreadthRightPattern) :
    ∃ bridge, route = .root bridge := by
  cases route with
  | root bridge => exact ⟨bridge, rfl⟩
  | neutralApplicationOrdinary membership notBare constructor materializes
      neutral ordinary leftChildren rightChildren arguments =>
      obtain ⟨-, leftArgumentsEq⟩ := Pattern.apply.inj
        (leftPatternEq.trans (by rfl))
      obtain ⟨-, rightArgumentsEq⟩ := Pattern.apply.inj
        (rightPatternEq.trans (by rfl))
      subst leftArgumentsEq
      subst rightArgumentsEq
      exact (rhoBreadth_spineRoute_empty.false arguments).elim
  | neutralApplicationQuote membership notBare constructor materializes
      neutral quoted leftChildren rightChildren arguments =>
      obtain ⟨-, leftArgumentsEq⟩ := Pattern.apply.inj
        (leftPatternEq.trans (by rfl))
      obtain ⟨-, rightArgumentsEq⟩ := Pattern.apply.inj
        (rightPatternEq.trans (by rfl))
      subst leftArgumentsEq
      subst rightArgumentsEq
      exact (rhoBreadth_spineRoute_empty.false arguments).elim
  | lambda left right body =>
      exact absurd leftPatternEq (by
        simp [rhoBreadthLeftPattern])
  | multiLambda left right body =>
      exact absurd leftPatternEq (by
        simp [rhoBreadthLeftPattern])
  | substBody leftBodyTree rightBodyTree replacementTree body =>
      exact absurd leftPatternEq (by
        simp [rhoBreadthLeftPattern])
  | substReplacement bodyTree left right replacement =>
      exact absurd leftPatternEq (by
        simp [rhoBreadthLeftPattern])
  | collection leftChildren rightChildren elements =>
      exact absurd leftPatternEq (by
        simp [rhoBreadthLeftPattern])

/-! ## Positive control, part 1: the inner base redex over `a`

The multi-child alignment closes each changed sibling with its own root
certificate.  The first sibling reuses the established selected Quote/Drop
cell.  The second sibling needs the base-colour machinery for the same
Quote/Drop shape over `a`, mirrored from the cut-order fixture. -/

/-- Inner base Quote/Drop redex of the second sibling. -/
def rhoBreadthRedexA : Pattern :=
  rhoCutOrderBaseQuote (rhoCutOrderBaseDrop (.fvar "a"))

theorem rhoBreadthLeftProcess_eq :
    rhoBreadthLeftProcess = rhoCutOrderWrappedDrop rhoBreadthRedexA := rfl

private def rhoBreadthBaseDropDeclared :
    rhoCIGSLT.DeclaredCostConstructor :=
  ⟨.base ⟨rhoCalc.terms[1], rhoBreadthRule_mem 1 (by omega)⟩, True.intro⟩

private theorem rhoBreadthBaseDropRole :
    rhoCIGSLT.declaredCostConstructorRole rhoBreadthBaseDropDeclared =
      .static .base := by
  rfl

private def rhoBreadthBaseDropPreimage :
    CostStaticConstructorPreimage rhoCIGSLT .base rhoBreadthBaseDropDeclared :=
  costStaticConstructorPreimage rhoCIGSLT .base rhoBreadthBaseDropDeclared
    rhoBreadthBaseDropRole

private theorem rhoBreadthBaseDrop_notBare :
    ¬ UsesBareCollection rhoBreadthBaseDropPreimage.sourceConstructor.1 := by
  simp [rhoBreadthBaseDropPreimage, costStaticConstructorPreimage,
    rhoBreadthBaseDropDeclared, UsesBareCollection, rhoCalc, TypeExpr.name,
    TypeExpr.proc, TypeExpr.baseType]

private def rhoBreadthBaseQuoteDeclared :
    rhoCIGSLT.DeclaredCostConstructor :=
  ⟨.base ⟨rhoCalc.terms[2], rhoBreadthRule_mem 2 (by omega)⟩, True.intro⟩

private theorem rhoBreadthBaseQuoteRole :
    rhoCIGSLT.declaredCostConstructorRole rhoBreadthBaseQuoteDeclared =
      .static .base := by
  rfl

private def rhoBreadthBaseQuotePreimage :
    CostStaticConstructorPreimage rhoCIGSLT .base rhoBreadthBaseQuoteDeclared :=
  costStaticConstructorPreimage rhoCIGSLT .base rhoBreadthBaseQuoteDeclared
    rhoBreadthBaseQuoteRole

private theorem rhoBreadthBaseQuote_notBare :
    ¬ UsesBareCollection rhoBreadthBaseQuotePreimage.sourceConstructor.1 := by
  simp [rhoBreadthBaseQuotePreimage, costStaticConstructorPreimage,
    rhoBreadthBaseQuoteDeclared, UsesBareCollection, rhoCalc, TypeExpr.name,
    TypeExpr.proc, TypeExpr.baseType]

private def rhoBreadthBaseFvarAPlan (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .base rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] outer (.fvar "a") (.base "Name") :=
  .fvar (by
    simp [rhoCutOrderFree, FreeTypeContext.ofList, mapTypeExpr,
      CostStaticColor.symbols, costBaseStaticSymbols,
      costBasePresentationSymbols])

private def rhoBreadthBaseDropAPlan (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .base rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] outer (rhoCutOrderBaseDrop (.fvar "a")) (.base "Proc") := by
  apply CostStaticRegionPlan.application rhoBreadthBaseDropDeclared rfl
    rhoBreadthBaseDropRole rhoBreadthBaseDropPreimage
  · exact rhoBreadthBaseDrop_notBare
  · exact .cons (by trivial) rfl
      (rhoBreadthBaseFvarAPlan
        (outer.comp
          (.apply (costBaseConstructorName "PDrop") [] .hole [])))
      .nil

private def rhoBreadthBaseRedexAPlan :
    CostStaticRegionPlan rhoCIGSLT .base rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] .hole rhoBreadthRedexA (.base "Name") := by
  apply CostStaticRegionPlan.application rhoBreadthBaseQuoteDeclared rfl
    rhoBreadthBaseQuoteRole rhoBreadthBaseQuotePreimage
  · exact rhoBreadthBaseQuote_notBare
  · exact .cons (by trivial) rfl
      (rhoBreadthBaseDropAPlan
        (OneHoleContext.hole.comp
          (.apply (costBaseConstructorName "NQuote") [] .hole [])))
      .nil

private def rhoBreadthBaseNameSort : LangSort rhoCIGSLT.costWholeLanguage :=
  CostStaticColor.base.mapLangSort rhoCIGSLT rhoName

private theorem rhoBreadthRedexA_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      rhoBreadthRedexA (.base (costBaseSortName "Name")) :=
  rhoBreadthBaseQuote_typed _ (rhoBreadthBaseDrop_typed _ rhoBreadthA_typed)

private theorem rhoBreadthRedexA_wellSorted :
    OpenPatternWellSorted rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      (mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
        (.base "Name"))
      rhoBreadthRedexA := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · simpa [mapTypeExpr, CostStaticColor.symbols,
      costWrappedStaticSymbols, rhoCIGSLT, rhoIGSLT,
      rhoInteractivePresentation, rhoCalc, TypeDecl.plain,
      show "Name" ≠ "Proc" by decide] using rhoBreadthRedexA_typed
  · intro declaration membership
    simp [rhoBreadthRedexA, rhoCutOrderBaseQuote, rhoCutOrderBaseDrop,
      binderSafeAt, binderSafeListAt]

private def rhoBreadthRedexATerm :
    OpenTerm rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      rhoBreadthBaseNameSort :=
  ⟨rhoBreadthRedexA, rhoBreadthRedexA_wellSorted⟩

def rhoBreadthBaseRedexANode :
    CostStaticRegionNode rhoCIGSLT .base rhoCutOrderFree :=
  CostStaticRegionNode.ofPlan rhoBreadthRedexATerm rhoBreadthBaseRedexAPlan
    (by unfold rhoBreadthBaseRedexAPlan; rfl)

def rhoBreadthBaseRedexAChildren :
    CostRegionBoundaryTrees rhoCIGSLT rhoCutOrderFree .base
      rhoBreadthBaseRedexANode.finiteBoundaryTable := by
  apply CostRegionBoundaryTrees.ofEntriesEqNil
  rfl

def rhoBreadthBaseRedexAStaticTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree
      rhoBreadthBaseRedexANode.targetBound []
      rhoBreadthBaseRedexANode.term.1
      (.base (CostStaticColor.base.mapLangSort rhoCIGSLT
        rhoBreadthBaseRedexANode.sourceSort).1) :=
  .static rhoBreadthBaseRedexANode rhoBreadthBaseRedexAChildren

theorem rhoBreadthBaseRedexANode_targetBound :
    rhoBreadthBaseRedexANode.targetBound = [] := by
  rfl

theorem rhoBreadthBaseRedexANode_term_pattern :
    rhoBreadthBaseRedexANode.term.1 = rhoBreadthRedexA := by
  rfl

theorem rhoBreadthBaseRedexANode_resultType :
    (.base (CostStaticColor.base.mapLangSort rhoCIGSLT
      rhoBreadthBaseRedexANode.sourceSort).1 : TypeExpr) =
        .base (costBaseSortName "Name") := by
  rfl

def rhoBreadthBaseRedexATree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] [] rhoBreadthRedexA
      (.base (costBaseSortName "Name")) :=
  CostRegionTree.reindexType rhoBreadthBaseRedexANode_resultType
    (CostRegionTree.reindexPattern rhoBreadthBaseRedexANode_term_pattern
      (CostRegionTree.reindexAvailable rhoBreadthBaseRedexANode_targetBound
        rhoBreadthBaseRedexAStaticTree))

theorem rhoBreadthBaseRedexANode_skeleton_pattern :
    rhoBreadthBaseRedexANode.skeleton.1 =
      .apply "NQuote"
        [.apply "PDrop"
          [.fvar (costRegionSourceVariableName "a")]] := by
  rfl

/-- The typed base Quote/Drop frame over `a` and its structural source
variable meet at one retained semantic atom. -/
noncomputable def rhoBreadthBaseRedexANodeSemanticAtomJoin :
    PackedCostSemanticAtomJoin rhoCIGSLT
      (CostStaticRegionNode.normalizeHereditary rhoBreadthBaseRedexANode
        (TypedCostRegionBoundaryTable.Values.original
          rhoBreadthBaseRedexANode.finiteBoundaryTable)).1
      (.fvar "a") := by
  let values := TypedCostRegionBoundaryTable.Values.original
    rhoBreadthBaseRedexANode.finiteBoundaryTable
  let packed := rhoBreadthBaseRedexANode.semanticAtomEnvironment values
  let inventory := packed.1
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  have sourceMembership : costRegionSourceVariableName "a" ∈
      rhoBreadthBaseRedexANode.skeleton.1.freeFvarNames := by
    rw [rhoBreadthBaseRedexANode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  have occurrenceExists := rhoBreadthBaseRedexANode.skeleton_fvar_covered
    (costRegionSourceVariableName "a") sourceMembership
  let occurrence := Classical.choose occurrenceExists
  have occurrenceName := Classical.choose_spec occurrenceExists
  have slotExists := environment.slotOfName?_isSome_of_occurrence occurrence
  let slot := (environment.slotOfName? occurrence.name).get slotExists
  have selectedAtOccurrence : environment.slotOfName? occurrence.name =
      some slot := (Option.some_get slotExists).symm
  have reifiedFrame :
      (rhoBreadthBaseRedexANode.reifiedSourceFrame environment).1 =
        .apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor
            [.fvar (environment.atomName slot)]] := by
    rw [rhoBreadthBaseRedexANode.reifiedSourceFrame_pattern]
    have selected : environment.slotOfName?
        (costRegionSourceVariableName "a") = some slot := by
      rw [← occurrenceName]
      exact selectedAtOccurrence
    change environment.reify
        (.apply "NQuote"
          [.apply "PDrop" [.fvar (costRegionSourceVariableName "a")]]) = _
    simp [CostStaticAtomEnvironment.reify,
      CostStaticAtomEnvironment.reifyName, selected,
      rhoReflectivePresentation]
  exact CostStaticRegionNode.quoteDropSourceVariableSemanticAtomJoin
    rhoBreadthBaseRedexANode values occurrence "a" occurrenceName slot
      selectedAtOccurrence reifiedFrame

theorem rhoBreadthBaseRedexANode_normalizeHereditary :
    (CostStaticRegionNode.normalizeHereditary rhoBreadthBaseRedexANode
      (TypedCostRegionBoundaryTable.Values.original
        rhoBreadthBaseRedexANode.finiteBoundaryTable)).1 =
      .fvar "a" := by
  exact rhoBreadthBaseRedexANodeSemanticAtomJoin.results_eq

theorem rhoBreadthBaseRedexATree_normalizeHereditary :
    (CostRegionTree.normalizeHereditary rhoBreadthBaseRedexATree).pattern =
      .fvar "a" := by
  unfold CostRegionTree.normalizeHereditary rhoBreadthBaseRedexATree
  rw [CostRegionTree.reindexType_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer),
    CostRegionTree.reindexPattern_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer),
    CostRegionTree.reindexAvailable_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)]
  unfold rhoBreadthBaseRedexAStaticTree
  rw [CostRegionTree.normalize_static_pattern]
  rw [rhoBreadthBaseRedexAChildren.normalizeValues_eq_original_of_entries_eq_nil
    (normalizeStatic := rhoHereditaryStaticNormalizer) (empty := by rfl)]
  exact rhoBreadthBaseRedexANode_normalizeHereditary

/-! ## Positive control, part 2: the wrapped single-drop frames -/

private theorem rhoBreadthBoundaryCertificateA_exists :
    ∃ certificate,
      certifyCostRegionBoundary? rhoCIGSLT .wrapped rhoCutOrderFree []
          (mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
            (.base "Name"))
          rhoBreadthRedexA =
        some certificate := by
  apply exists_certifyCostRegionBoundary?_eq_some
  · exact ⟨.base "Name", decodeCostStaticTypeExpr_mapTypeExpr _ _ _⟩
  · exact rhoBreadthRedexA_wellSorted

/-- Certified wrapped-colour boundary carrying the inner base redex over
`a`.  The executable certifier remains the sole witness source. -/
noncomputable def rhoBreadthBoundaryWitnessA :
    CertifiedCostRegionBoundary rhoCIGSLT .wrapped rhoCutOrderFree []
      (mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
        (.base "Name")) rhoBreadthRedexA :=
  Classical.choose rhoBreadthBoundaryCertificateA_exists

theorem rhoBreadthBoundaryWitnessA_spec :
    certifyCostRegionBoundary? rhoCIGSLT .wrapped rhoCutOrderFree []
        (mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
          (.base "Name")) rhoBreadthRedexA =
      some rhoBreadthBoundaryWitnessA :=
  Classical.choose_spec rhoBreadthBoundaryCertificateA_exists

private theorem rhoBreadthBaseQuoteOutsideWrapped :
    rhoCIGSLT.declaredCostConstructorRole rhoBreadthBaseQuoteDeclared ≠
      .static .wrapped := by
  rw [rhoBreadthBaseQuoteRole]
  decide

private noncomputable def rhoBreadthWrappedBoundaryAPlan
    (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .wrapped rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .wrapped []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .wrapped [])
      [] outer rhoBreadthRedexA (.base "Name") :=
  .boundaryApplication rhoBreadthBaseQuoteDeclared rfl
    rhoBreadthBaseQuoteOutsideWrapped rhoBreadthBoundaryWitnessA
    rhoBreadthBoundaryWitnessA_spec

private def rhoBreadthWrappedDropDeclared :
    rhoCIGSLT.DeclaredCostConstructor :=
  ⟨.wrapped rhoBreadthDropConstructor, rhoBreadthDrop_selected⟩

private theorem rhoBreadthWrappedDropRole :
    rhoCIGSLT.declaredCostConstructorRole rhoBreadthWrappedDropDeclared =
      .static .wrapped := by
  rfl

private def rhoBreadthWrappedDropPreimage :
    CostStaticConstructorPreimage rhoCIGSLT .wrapped
      rhoBreadthWrappedDropDeclared :=
  costStaticConstructorPreimage rhoCIGSLT .wrapped
    rhoBreadthWrappedDropDeclared rhoBreadthWrappedDropRole

private theorem rhoBreadthWrappedDrop_notBare :
    ¬ UsesBareCollection
      rhoBreadthWrappedDropPreimage.sourceConstructor.1 := by
  simp [rhoBreadthWrappedDropPreimage, costStaticConstructorPreimage,
    rhoBreadthWrappedDropDeclared, rhoBreadthDropConstructor,
    UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
    TypeExpr.baseType]

private noncomputable def rhoBreadthLeftProcessPlan :
    CostStaticRegionPlan rhoCIGSLT .wrapped rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .wrapped []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .wrapped [])
      [] .hole rhoBreadthLeftProcess (.base "Proc") := by
  apply CostStaticRegionPlan.application rhoBreadthWrappedDropDeclared rfl
    rhoBreadthWrappedDropRole rhoBreadthWrappedDropPreimage
  · exact rhoBreadthWrappedDrop_notBare
  · exact .cons (by trivial) rfl
      (rhoBreadthWrappedBoundaryAPlan
        (OneHoleContext.hole.comp
          (.apply (costWrappedConstructorName "PDrop") [] .hole [])))
      .nil

private def rhoBreadthWrappedFvarAPlan (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .wrapped rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .wrapped []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .wrapped [])
      [] outer (.fvar "a") (.base "Name") :=
  .fvar (by
    simp [rhoCutOrderFree, FreeTypeContext.ofList, mapTypeExpr,
      CostStaticColor.symbols, costWrappedStaticSymbols, rhoCIGSLT, rhoIGSLT,
      rhoInteractivePresentation, rhoCalc, TypeDecl.plain,
      show "Name" ≠ "Proc" by decide])

private def rhoBreadthRightProcessPlan :
    CostStaticRegionPlan rhoCIGSLT .wrapped rhoCutOrderFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .wrapped []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .wrapped [])
      [] .hole rhoBreadthRightProcess (.base "Proc") := by
  apply CostStaticRegionPlan.application rhoBreadthWrappedDropDeclared rfl
    rhoBreadthWrappedDropRole rhoBreadthWrappedDropPreimage
  · exact rhoBreadthWrappedDrop_notBare
  · exact .cons (by trivial) rfl
      (rhoBreadthWrappedFvarAPlan
        (OneHoleContext.hole.comp
          (.apply (costWrappedConstructorName "PDrop") [] .hole [])))
      .nil

private theorem rhoBreadthWrappedProc_wellSorted (process : Pattern)
    (typed : HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree [] process
      (.base costWrappedSortName))
    (scope : ∀ declaration ∈
      rhoCIGSLT.costWholeLanguage.reflectivePresentations,
      binderSafeAt declaration.quoteConstructor 0 process = true)
    (canonical : process.hasCanonicalBinderMetadata = true)
    (object : isObjectPattern process = true) :
    OpenPatternWellSorted rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      (mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
        (.base "Proc"))
      process := by
  refine ⟨?_, canonical, object, ?_⟩
  · simpa [mapTypeExpr, CostStaticColor.symbols,
      costWrappedStaticSymbols, rhoCIGSLT, rhoIGSLT,
      rhoInteractivePresentation, rhoCalc, TypeDecl.plain] using typed
  · intro declaration membership
    exact scope declaration membership

private def rhoBreadthLeftProcessTerm :
    OpenTerm rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      (CostStaticColor.wrapped.mapLangSort rhoCIGSLT rhoProc) :=
  ⟨rhoBreadthLeftProcess,
    rhoBreadthWrappedProc_wellSorted _
      (rhoBreadthWrappedDrop_typed _ rhoBreadthRedexA_typed)
      (by
        intro declaration membership
        simp [rhoBreadthLeftProcess, rhoCutOrderWrappedDrop,
          rhoCutOrderBaseQuote, rhoCutOrderBaseDrop, binderSafeAt,
          binderSafeListAt])
      rfl rfl⟩

private def rhoBreadthRightProcessTerm :
    OpenTerm rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      (CostStaticColor.wrapped.mapLangSort rhoCIGSLT rhoProc) :=
  ⟨rhoBreadthRightProcess,
    rhoBreadthWrappedProc_wellSorted _
      (rhoBreadthWrappedDrop_typed _ rhoBreadthA_typed)
      (by
        intro declaration membership
        simp [rhoBreadthRightProcess, rhoCutOrderWrappedDrop, binderSafeAt,
          binderSafeListAt])
      rfl rfl⟩

noncomputable def rhoBreadthLeftProcessNode :
    CostStaticRegionNode rhoCIGSLT .wrapped rhoCutOrderFree :=
  CostStaticRegionNode.ofPlan rhoBreadthLeftProcessTerm
    rhoBreadthLeftProcessPlan
    (by unfold rhoBreadthLeftProcessPlan; rfl)

def rhoBreadthRightProcessNode :
    CostStaticRegionNode rhoCIGSLT .wrapped rhoCutOrderFree :=
  CostStaticRegionNode.ofPlan rhoBreadthRightProcessTerm
    rhoBreadthRightProcessPlan
    (by unfold rhoBreadthRightProcessPlan; rfl)

private theorem rhoBreadthWrappedNameType :
    (.base (costBaseSortName "Name") : TypeExpr) =
      mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
        (.base "Name") := by
  simp [mapTypeExpr, CostStaticColor.symbols,
    costWrappedStaticSymbols, rhoCIGSLT, rhoIGSLT,
    rhoInteractivePresentation, rhoCalc, TypeDecl.plain,
    show "Name" ≠ "Proc" by decide]

noncomputable def rhoBreadthBoundaryChildA :
    CostRegionTree rhoCIGSLT rhoCutOrderFree
      rhoBreadthBoundaryWitnessA.typed.boundary.targetSupport []
      rhoBreadthBoundaryWitnessA.typed.boundary.content
      rhoBreadthBoundaryWitnessA.typed.boundary.targetType :=
  CostRegionTree.reindexType
    (rhoBreadthWrappedNameType.trans
      rhoBreadthBoundaryWitnessA.targetType_eq.symm)
    (CostRegionTree.reindexPattern
      rhoBreadthBoundaryWitnessA.content_eq.symm
      (CostRegionTree.reindexAvailable
        rhoBreadthBoundaryWitnessA.targetSupport_eq.symm
        rhoBreadthBaseRedexATree))

theorem rhoBreadthBoundaryChildA_normalizeHereditary :
    (CostRegionTree.normalizeHereditary rhoBreadthBoundaryChildA).pattern =
      .fvar "a" := by
  unfold CostRegionTree.normalizeHereditary rhoBreadthBoundaryChildA
  rw [CostRegionTree.reindexType_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer),
    CostRegionTree.reindexPattern_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer),
    CostRegionTree.reindexAvailable_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)]
  exact rhoBreadthBaseRedexATree_normalizeHereditary

noncomputable def rhoBreadthLeftProcessChildren :
    CostRegionBoundaryTrees rhoCIGSLT rhoCutOrderFree .wrapped
      rhoBreadthLeftProcessNode.finiteBoundaryTable :=
  .cons rhoBreadthBoundaryChildA .nil

def rhoBreadthRightProcessChildren :
    CostRegionBoundaryTrees rhoCIGSLT rhoCutOrderFree .wrapped
      rhoBreadthRightProcessNode.finiteBoundaryTable := by
  apply CostRegionBoundaryTrees.ofEntriesEqNil
  rfl

theorem rhoBreadthLeftProcessNode_skeleton_pattern :
    rhoBreadthLeftProcessNode.skeleton.1 =
      .apply "PDrop"
        [.fvar (costRegionBoundaryVariableName
          rhoBreadthBoundaryWitnessA.typed.boundary)] := by
  rfl

theorem rhoBreadthRightProcessNode_skeleton_pattern :
    rhoBreadthRightProcessNode.skeleton.1 =
      .apply "PDrop" [.fvar (costRegionSourceVariableName "a")] := by
  rfl

/-- Source-variable parameters are restored literally by the hereditary
value vector. -/
theorem rhoBreadthValues_assignment_sourceVariable
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      table)
    (name : String) :
    values.assignment table (costRegionSourceVariableName name) =
      .fvar name := by
  simp [TypedCostRegionBoundaryTable.Values.assignment]

/-- The left wrapped frame receives the hereditary normal form of its unique
opposite-colour child at the exact proof-relevant boundary slot. -/
theorem rhoBreadthLeftProcessHereditaryValues_boundaryAssignment :
    (rhoBreadthLeftProcessChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)).assignment
        rhoBreadthLeftProcessNode.boundaryTable
        (costRegionBoundaryVariableName
          rhoBreadthBoundaryWitnessA.typed.boundary) =
      .fvar "a" := by
  change
    ((CostRegionBoundaryTrees.cons rhoBreadthBoundaryChildA
      CostRegionBoundaryTrees.nil).normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)).assignment
          (.cons rhoBreadthBoundaryWitnessA.typed
            rhoBreadthBoundaryWitnessA.content_eq .nil)
          (costRegionBoundaryVariableName
            rhoBreadthBoundaryWitnessA.typed.boundary) =
      .fvar "a"
  simp only [CostRegionBoundaryTrees.normalizeValues]
  unfold TypedCostRegionBoundaryTable.Values.assignment
  rw [decodeCostRegionSourceVariableName_boundary]
  unfold TypedCostRegionBoundaryTable.Values.resolve
  simp only [if_pos]
  exact rhoBreadthBoundaryChildA_normalizeHereditary

/-- The single wrapped frame of each process sibling canonicalizes to the
drop of its unique semantic atom.  The atom may certify a foreign boundary or
a source variable; the frame computation is identical. -/
theorem rhoBreadthProcess_canonicalFrame
    (node : CostStaticRegionNode rhoCIGSLT .wrapped rhoCutOrderFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT .wrapped
      rhoCutOrderFree node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT .wrapped
      rhoCutOrderFree node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT .wrapped
      rhoCutOrderFree inventory)
    (name : String)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? name = some slot)
    (skeleton : node.skeleton.1 = .apply "PDrop" [.fvar name])
    (closed : node.targetBound = []) :
    node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
          rhoReflectivePresentation) =
      .apply (costWrappedConstructorName "PDrop")
        [.fvar (environment.atomName slot)] := by
  have reifiedFrame : (node.reifiedSourceFrame environment).1 =
      .apply "PDrop" [.fvar (environment.atomName slot)] := by
    rw [node.reifiedSourceFrame_pattern]
    calc
      environment.reify node.skeleton.1 =
          environment.reify (.apply "PDrop" [.fvar name]) :=
        congrArg environment.reify skeleton
      _ = _ := by
        simp [CostStaticAtomEnvironment.reify,
          CostStaticAtomEnvironment.reifyName, selected]
  rw [CostStaticRegionNode.canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize
    node environment]
  rw [CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
    node.thinning closed]
  rw [reifiedFrame]
  have targetDepth : node.targetBound.length = 0 := by simp [closed]
  rw [targetDepth]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
    rhoReflectivePresentation, mapPattern, mapPatternList_eq_map,
    CostStaticColor.symbols_constructor, CostStaticColor.constructorTag,
    costWrappedConstructorName]

/-- The two wrapped process siblings restore to the same compact drop of `a`
at the independently constructed common semantic apex.  The left atom is a
certified foreign boundary; the right atom is a direct source variable; only
their complete restored meanings are compared. -/
theorem rhoBreadth_process_commonRestoredCanonicalFrames_eq :
    let leftValues := rhoBreadthLeftProcessChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer)
    let rightValues := rhoBreadthRightProcessChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer)
    let leftInventory :=
      (rhoBreadthLeftProcessNode.semanticAtomEnvironment leftValues).1
    let rightInventory :=
      (rhoBreadthRightProcessNode.semanticAtomEnvironment rightValues).1
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
    let rightEnvironment :=
      CostStaticAtomEnvironment.ofInventory rightInventory
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeLanguage
        cospan.commonSupport cospan.commonAssignment
        rhoBreadthLeftProcessNode.targetBound.length
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (rhoBreadthLeftProcessNode.canonicalizeReifiedTargetFrame
            leftEnvironment
            (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
              rhoReflectivePresentation))) =
      ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeLanguage
        cospan.commonSupport cospan.commonAssignment
        rhoBreadthLeftProcessNode.targetBound.length
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rhoBreadthRightProcessNode.canonicalizeReifiedTargetFrame
            rightEnvironment
            (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
              rhoReflectivePresentation))) := by
  let leftValues := rhoBreadthLeftProcessChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rhoBreadthRightProcessChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (rhoBreadthLeftProcessNode.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rhoBreadthRightProcessNode.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  -- left atom slot
  have leftMembership : costRegionBoundaryVariableName
      rhoBreadthBoundaryWitnessA.typed.boundary ∈
        rhoBreadthLeftProcessNode.skeleton.1.freeFvarNames := by
    rw [rhoBreadthLeftProcessNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  obtain ⟨leftOccurrence, leftOccurrenceName⟩ :=
    rhoBreadthLeftProcessNode.skeleton_fvar_covered _ leftMembership
  obtain ⟨leftSlot, leftSelectedAtOccurrence⟩ := Option.isSome_iff_exists.mp
    (leftEnvironment.slotOfName?_isSome_of_occurrence leftOccurrence)
  have leftSelected : leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName
        rhoBreadthBoundaryWitnessA.typed.boundary) = some leftSlot := by
    simpa [leftOccurrenceName] using leftSelectedAtOccurrence
  -- right atom slot
  have rightMembership : costRegionSourceVariableName "a" ∈
      rhoBreadthRightProcessNode.skeleton.1.freeFvarNames := by
    rw [rhoBreadthRightProcessNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  obtain ⟨rightOccurrence, rightOccurrenceName⟩ :=
    rhoBreadthRightProcessNode.skeleton_fvar_covered _ rightMembership
  obtain ⟨rightSlot, rightSelectedAtOccurrence⟩ := Option.isSome_iff_exists.mp
    (rightEnvironment.slotOfName?_isSome_of_occurrence rightOccurrence)
  have rightSelected : rightEnvironment.slotOfName?
      (costRegionSourceVariableName "a") = some rightSlot := by
    simpa [rightOccurrenceName] using rightSelectedAtOccurrence
  -- restored atom meanings
  have leftNormal : (leftEnvironment.atomValue leftSlot).key.normal =
      .fvar "a" := by
    calc
      (leftEnvironment.atomValue leftSlot).key.normal =
          leftValues.assignment rhoBreadthLeftProcessNode.boundaryTable
            leftOccurrence.name :=
        leftEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
          leftOccurrence leftSlot leftSelectedAtOccurrence
      _ = .fvar "a" := by
        simpa [leftOccurrenceName] using
          rhoBreadthLeftProcessHereditaryValues_boundaryAssignment
  have rightNormal : (rightEnvironment.atomValue rightSlot).key.normal =
      .fvar "a" := by
    calc
      (rightEnvironment.atomValue rightSlot).key.normal =
          rightValues.assignment rhoBreadthRightProcessNode.boundaryTable
            rightOccurrence.name :=
        rightEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
          rightOccurrence rightSlot rightSelectedAtOccurrence
      _ = .fvar "a" := by
        simpa [rightOccurrenceName] using
          rhoBreadthValues_assignment_sourceVariable
            rhoBreadthRightProcessNode.boundaryTable rightValues "a"
  -- canonical frames
  have leftFrame := rhoBreadthProcess_canonicalFrame
    rhoBreadthLeftProcessNode leftEnvironment _ leftSlot leftSelected
    rhoBreadthLeftProcessNode_skeleton_pattern rfl
  have rightFrame := rhoBreadthProcess_canonicalFrame
    rhoBreadthRightProcessNode rightEnvironment _ rightSlot rightSelected
    rhoBreadthRightProcessNode_skeleton_pattern rfl
  -- restored common values
  have leftCommonValue : cospan.commonAssignment
      (cospan.commonAtomName (cospan.leftSlot leftSlot)) = .fvar "a" := by
    rw [cospan.commonAssignment_commonAtomName]
    rw [show cospan.commonKeys.get (cospan.leftSlot leftSlot) =
        (leftEnvironment.atomValue leftSlot).key from
      cospan.leftCommutes leftSlot]
    exact leftNormal
  have rightCommonValue : cospan.commonAssignment
      (cospan.commonAtomName (cospan.rightSlot rightSlot)) = .fvar "a" := by
    rw [cospan.commonAssignment_commonAtomName]
    rw [show cospan.commonKeys.get (cospan.rightSlot rightSlot) =
        (rightEnvironment.atomValue rightSlot).key from
      cospan.rightCommutes rightSlot]
    exact rightNormal
  calc
    ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeLanguage
        cospan.commonSupport cospan.commonAssignment
        rhoBreadthLeftProcessNode.targetBound.length
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (rhoBreadthLeftProcessNode.canonicalizeReifiedTargetFrame
            leftEnvironment
            (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
              rhoReflectivePresentation))) =
        .apply (costWrappedConstructorName "PDrop") [.fvar "a"] := by
      rw [leftFrame]
      simp [CostStaticAtomKeyCospan.reifyWith,
        ReflectiveContextSupport.substituteAt, leftCommonValue,
        show rhoBreadthLeftProcessNode.targetBound.length = 0 from rfl,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
    _ = ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeLanguage
        cospan.commonSupport cospan.commonAssignment
        rhoBreadthLeftProcessNode.targetBound.length
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rhoBreadthRightProcessNode.canonicalizeReifiedTargetFrame
            rightEnvironment
            (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
              rhoReflectivePresentation))) := by
      rw [rightFrame]
      simp [CostStaticAtomKeyCospan.reifyWith,
        ReflectiveContextSupport.substituteAt, rightCommonValue,
        show rhoBreadthLeftProcessNode.targetBound.length = 0 from rfl,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]

/-- Root certificate joining the two wrapped process siblings through the
tie-tolerant common-restoration terminal. -/
noncomputable def rhoBreadthProcessRootBridge :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
      (CostRegionTree.static (outer := []) rhoBreadthLeftProcessNode
        rhoBreadthLeftProcessChildren)
      (CostRegionTree.static (outer := []) rhoBreadthRightProcessNode
        rhoBreadthRightProcessChildren) :=
  rhoStaticRootBridgeOfCommonRestoredCanonicalFrame
    rhoBreadthLeftProcessNode rhoBreadthRightProcessNode
    rhoBreadthLeftProcessChildren rhoBreadthRightProcessChildren rfl
    rhoBreadth_process_commonRestoredCanonicalFrames_eq

/-! ## Positive control, part 3: the multi-child alignment itself -/

noncomputable def rhoBreadthLeftProcessTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] [] rhoBreadthLeftProcess
      (.base costWrappedSortName) :=
  .static rhoBreadthLeftProcessNode rhoBreadthLeftProcessChildren

def rhoBreadthRightProcessTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] [] rhoBreadthRightProcess
      (.base costWrappedSortName) :=
  .static rhoBreadthRightProcessNode rhoBreadthRightProcessChildren

/-- Both wrapped process siblings close under one root cell of the
multi-child alignment. -/
noncomputable def rhoBreadthProcessAlignment :
    CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
      rhoBreadthLeftProcessTree rhoBreadthRightProcessTree :=
  rhoBreadthProcessRootBridge.toTreeAlignment

private def rhoBreadthOutputRule : GrammarRule :=
  costBaseConstructor rhoInteractionCut rhoCalc.terms[4]

private theorem rhoBreadthOutputMembership :
    rhoBreadthOutputRule ∈ rhoCIGSLT.costWholeLanguage.terms :=
  rhoCIGSLT.costBaseConstructor_mem_costWhole _
    (rhoBreadthRule_mem 4 (by omega))

private theorem rhoBreadthOutput_notBare :
    ¬ UsesBareCollection rhoBreadthOutputRule := by
  rw [rhoBreadthOutputRule, usesBareCollection_costBaseConstructor_iff]
  simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
    TypeExpr.baseType]

private def rhoBreadthOutputDeclared : rhoCIGSLT.DeclaredCostConstructor :=
  ⟨.base ⟨rhoCalc.terms[4], rhoBreadthRule_mem 4 (by omega)⟩, True.intro⟩

private theorem rhoBreadthOutput_materializes :
    rhoCIGSLT.materializeDeclaredCostConstructor rhoBreadthOutputDeclared =
      rhoBreadthOutputRule := by
  rfl

private theorem rhoBreadthOutputRole :
    rhoCIGSLT.declaredCostConstructorRole rhoBreadthOutputDeclared =
      .interactionPrincipal := by
  simp only [CIGSLT.declaredCostConstructorRole, rhoBreadthOutputDeclared]
  rw [if_pos]
  right
  apply Subtype.ext
  exact rhoInteractionCut_environment_constructor_value.symm

private theorem rhoBreadthOutput_notQuote :
    ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.costWholeLanguage
      rhoBreadthOutputRule.label = false := by
  decide

private theorem rhoBreadthOutputFirstParam :
    costBaseParameter rhoInteractionCut rhoCalc.terms[4]
      (TermParam.simple "n" TypeExpr.name, 0) =
      .simple "n" (.base (costBaseSortName "Name")) := by
  simp [costBaseParameter, isSelectedContinuation, rhoCalc, mapParameterType,
    costBaseTypeExpr,
    rhoInteractionCut_program_constructor_value,
    rhoInteractionCut_environment_constructor_value,
    rhoInteractionCut_program_continuation_index,
    rhoInteractionCut_environment_continuation_index,
    rhoIGSLT, rhoInteractivePresentation, TypeDecl.plain,
    TypeExpr.name, TypeExpr.proc, TypeExpr.baseType]

private theorem rhoBreadthOutputSecondParam :
    costBaseParameter rhoInteractionCut rhoCalc.terms[4]
      (TermParam.simple "q" TypeExpr.proc, 0 + 1) =
      .simple "q" (.base costWrappedSortName) := by
  simp [costBaseParameter, isSelectedContinuation, rhoCalc, mapParameterType,
    costWrappedTypeExpr,
    rhoInteractionCut_program_constructor_value,
    rhoInteractionCut_environment_constructor_value,
    rhoInteractionCut_program_continuation_index,
    rhoInteractionCut_environment_continuation_index,
    rhoIGSLT, rhoInteractivePresentation, TypeDecl.plain,
    TypeExpr.name, TypeExpr.proc, TypeExpr.baseType]

noncomputable def rhoBreadthLeftSpine :
    CostRegionArgumentTrees rhoCIGSLT rhoCutOrderFree [] []
      [rhoCutOrderRedex, rhoBreadthLeftProcess] rhoBreadthOutputRule.params :=
  .cons (by rw [rhoBreadthOutputFirstParam]; exact True.intro)
    (by rw [rhoBreadthOutputFirstParam]; rfl) rhoCutOrderBaseRedexTree
    (.cons (by rw [rhoBreadthOutputSecondParam]; exact True.intro)
      (by rw [rhoBreadthOutputSecondParam]; rfl) rhoBreadthLeftProcessTree .nil)

def rhoBreadthRightSpine :
    CostRegionArgumentTrees rhoCIGSLT rhoCutOrderFree [] []
      [.fvar "0", rhoBreadthRightProcess] rhoBreadthOutputRule.params :=
  .cons (by rw [rhoBreadthOutputFirstParam]; exact True.intro)
    (by rw [rhoBreadthOutputFirstParam]; rfl) rhoCutOrderZeroStructuralTree
    (.cons (by rw [rhoBreadthOutputSecondParam]; exact True.intro)
      (by rw [rhoBreadthOutputSecondParam]; rfl) rhoBreadthRightProcessTree .nil)

noncomputable def rhoBreadthLeftTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] [] rhoBreadthLeftPattern
      (.base (costBaseSortName "Proc")) :=
  .neutralApplicationOrdinary rhoBreadthOutputMembership
    rhoBreadthOutput_notBare rhoBreadthOutputDeclared
    rhoBreadthOutput_materializes (Or.inl rhoBreadthOutputRole)
    rhoBreadthOutput_notQuote rhoBreadthLeftSpine

def rhoBreadthRightTree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] [] rhoBreadthRightPattern
      (.base (costBaseSortName "Proc")) :=
  .neutralApplicationOrdinary rhoBreadthOutputMembership
    rhoBreadthOutput_notBare rhoBreadthOutputDeclared
    rhoBreadthOutput_materializes (Or.inl rhoBreadthOutputRole)
    rhoBreadthOutput_notQuote rhoBreadthRightSpine

/-- Both changed siblings carry their own sub-alignment beneath one shared
neutral frame: exactly the multi-child closure the single-path route cannot
express. -/
noncomputable def rhoBreadthTreeAlignment :
    CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
      rhoBreadthLeftTree rhoBreadthRightTree :=
  .neutralApplicationOrdinary rhoBreadthOutputMembership
    rhoBreadthOutput_notBare rhoBreadthOutputDeclared
    rhoBreadthOutput_materializes (Or.inl rhoBreadthOutputRole)
    rhoBreadthOutput_notQuote rhoBreadthLeftSpine rhoBreadthRightSpine
    (.cons (by rw [rhoBreadthOutputFirstParam]; exact True.intro)
      (by rw [rhoBreadthOutputFirstParam]; exact True.intro)
      (by rw [rhoBreadthOutputFirstParam]; rfl)
      rhoCutOrderBaseRedexTree rhoCutOrderZeroStructuralTree
      (.cons (by rw [rhoBreadthOutputSecondParam]; exact True.intro)
        (by rw [rhoBreadthOutputSecondParam]; rfl) rhoBreadthLeftProcessTree .nil)
      (.cons (by rw [rhoBreadthOutputSecondParam]; exact True.intro)
        (by rw [rhoBreadthOutputSecondParam]; rfl) rhoBreadthRightProcessTree .nil)
      rhoCutOrderBaseSelectedTreeNormalizationAlignment
      (.cons (by rw [rhoBreadthOutputSecondParam]; exact True.intro)
        (by rw [rhoBreadthOutputSecondParam]; exact True.intro)
        (by rw [rhoBreadthOutputSecondParam]; rfl)
        rhoBreadthLeftProcessTree rhoBreadthRightProcessTree .nil .nil
        rhoBreadthProcessAlignment .nil))

/-- End-to-end multi-child positive control: the breadth witness, both
checked elaborations, and the alignment closing each changed sibling with
its own semantic root certificate. -/
noncomputable def rhoBreadthGeneratorTreeAlignment :
    CostGeneratorTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoBreadth_generator where
  occurrence := rhoBreadthGeneratorWitness
  erasesTo := Subsingleton.elim _ _
  leftElaboration := ⟨rhoBreadthLeftTree⟩
  rightElaboration := ⟨rhoBreadthRightTree⟩
  treeAlignment := rhoBreadthTreeAlignment

/-- The multi-child alignment derives exact equality of the hereditary tree
results for the two-sibling witness. -/
theorem rhoBreadth_treeAlignment_pattern_eq :
    (rhoBreadthLeftTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (rhoBreadthRightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  simpa [rhoHereditaryNormalizationKernel] using
    rhoBreadthTreeAlignment.normalize_pattern_eq

/-- Positive regression: the repaired hereditary production executor exactly
collapses the two-sibling reflective edge that no single-path route can
carry. -/
theorem rhoBreadth_costNormalizeOpenHereditary_eq :
    rhoCostNormalizeOpenHereditary rhoBreadthLeft =
      rhoCostNormalizeOpenHereditary rhoBreadthRight := by
  apply Subtype.ext
  exact rhoBreadthGeneratorTreeAlignment.toNormalizationLift.span.compiledPatterns_eq
    rhoHereditaryCompactCoherent

/-- The repaired exact collapse is tied to the actual two-sibling authored
generator, not to two independently chosen example terms. -/
theorem rhoBreadth_hereditary_generator_canary :
    openEquationGenerator rhoCIGSLT.costIGSLT
        rhoCutOrderFree [] rhoBreadthBaseProcSort
        rhoBreadthLeft rhoBreadthRight ∧
      rhoCostNormalizeOpenHereditary rhoBreadthLeft =
        rhoCostNormalizeOpenHereditary rhoBreadthRight :=
  ⟨rhoBreadth_generator, rhoBreadth_costNormalizeOpenHereditary_eq⟩

/-! ## Negative key canary: keyed canonicalization does not absorb plain
canonicalization

With a constant ordering key, stable keyed sorting preserves whichever tied
input order it receives, while plain canonicalization has already sorted by
structural code.  Raw keyed absorption of the plain canonicalizer is
therefore false, and the honest general closure is equality after
common-apex restoration (`substituteAt_canonicalizeByAt_parallel_eq_of_perm`)
or ordinary-canonical equivalence — never raw equality without an explicit
key-separation hypothesis.  An origin-based tie-break would reintroduce the
cut-order leak. -/

theorem canonicalizeByAt_not_absorbs_canonicalize :
    ¬ ∀ (key : Nat → Pattern → Nat)
        (declaration : ReflectivePresentationDecl) (pattern : Pattern),
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt key
            declaration 0
            (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              declaration pattern) =
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt key
            declaration 0 pattern := by
  intro absorb
  let declaration := rhoReflectivePresentation.toReflectivePresentationDecl
  have ordered : Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
        (.fvar "a") ≤
      Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode (.fvar "b") := by
    decide
  have swapped :
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns
          [Pattern.fvar "b", Pattern.fvar "a"] =
        [Pattern.fvar "a", Pattern.fvar "b"] := by
    calc
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns
          [Pattern.fvar "b", Pattern.fvar "a"] =
          Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns
            [Pattern.fvar "a", Pattern.fvar "b"] :=
        Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns_eq_of_perm
          (List.Perm.swap (Pattern.fvar "a") (Pattern.fvar "b") [])
      _ = [Pattern.fvar "a", Pattern.fvar "b"] := by
        simpa using
          Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_pair_eq_of_le
            Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
            (.fvar "a") (.fvar "b") ordered
  have plainSide :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          (.collection .hashBag [.fvar "b", .fvar "a"] none) =
        .collection .hashBag [.fvar "a", .fvar "b"] none := by
    simp [declaration, Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
      rhoReflectivePresentation, swapped]
  have sortConst : ∀ x y : Pattern,
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
          (fun _ => (0 : Nat)) [x, y] = [x, y] := by
    intro x y
    exact Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_pair_eq_of_le
      (fun _ => (0 : Nat)) x y (le_refl 0)
  have keyedFvars : ∀ x y : String,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (fun _ _ => (0 : Nat)) declaration 0
          (.collection .hashBag [.fvar x, .fvar y] none) =
        .collection .hashBag [.fvar x, .fvar y] none := by
    intro x y
    simp [declaration,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
      rhoReflectivePresentation, sortConst]
  have contradiction := absorb (fun _ _ => (0 : Nat)) declaration
    (.collection .hashBag [.fvar "b", .fvar "a"] none)
  rw [plainSide, keyedFvars "a" "b", keyedFvars "b" "a"] at contradiction
  simp at contradiction

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary
