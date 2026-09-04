import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorQuadrantCanary

/-!
# Same-view-colour foreign-shell canary

The broad typed mixed-colour counterexample uses an arbitrary semantic
cospan.  Here its syntax is realized by actual Cost trees below a common
base-colour Drop root.  The selected wrapped Quote/Drop shell is opaque to
the base plan on one side, while the exposed base Quote belongs to the base
plan on the other.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ForeignSameColorTypedCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

def processType : TypeExpr := .base (costBaseSortName "Proc")
def nameType : TypeExpr := .base (costBaseSortName "Name")

def targetFree : FreeTypeContext :=
  FreeTypeContext.ofList [("x", processType), ("y", processType)]

def raw : Pattern :=
  .collection .hashBag [.fvar "x", .fvar "y"] none

def foreignQuote : Pattern :=
  .apply (costBaseConstructorName "NQuote") [raw]

def selectedQuoteDrop : Pattern :=
  .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PDrop") [foreignQuote]]

def declaration : ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
    rhoReflectivePresentation.toReflectivePresentationDecl

def leftPattern : Pattern :=
  .apply (costBaseConstructorName "PDrop") [selectedQuoteDrop]

def rightPattern : Pattern :=
  .apply (costBaseConstructorName "PDrop") [foreignQuote]

theorem leftWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree [] processType leftPattern := by
  refine ⟨checkOpenPatternWellSorted_sound (by decide), ?_⟩
  intro reflected _membership
  simp [leftPattern, selectedQuoteDrop, foreignQuote, raw, binderSafeAt,
    binderSafeListAt]

theorem rightWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree [] processType rightPattern := by
  refine ⟨checkOpenPatternWellSorted_sound (by decide), ?_⟩
  intro reflected _membership
  simp [rightPattern, foreignQuote, raw, binderSafeAt, binderSafeListAt]

theorem canonical_eq :
    canonicalize declaration leftPattern =
      canonicalize declaration rightPattern := by
  have outerNe : costBaseConstructorName "PDrop" ≠
      declaration.quoteConstructor := by
    rw [declaration, rhoDecl_quoteConstructor .wrapped]
    decide
  have quoteEq : costWrappedConstructorName "NQuote" =
      declaration.quoteConstructor := by
    rfl
  have dropEq : costWrappedConstructorName "PDrop" =
      declaration.dropConstructor := by
    rfl
  have dropNe : declaration.dropConstructor ≠
      declaration.quoteConstructor := by
    rw [declaration]
    decide
  rw [leftPattern, rightPattern,
    canonicalize_apply_of_ne_quote declaration outerNe,
    canonicalize_apply_of_ne_quote declaration outerNe]
  simp only [List.map_cons, List.map_nil, Pattern.apply.injEq, true_and,
    List.cons.injEq, and_true]
  rw [selectedQuoteDrop, quoteEq, dropEq]
  exact canonicalize_quote_drop declaration dropNe foreignQuote

noncomputable def leftTree :
    CostRegionTree rhoCIGSLT targetFree [] [] leftPattern processType :=
  (CostRegionTree.build? [] [] leftPattern processType).get
    (CostRegionTree.build?_isSome_of_wellSorted leftWellSorted)

noncomputable def rightTree :
    CostRegionTree rhoCIGSLT targetFree [] [] rightPattern processType :=
  (CostRegionTree.build? [] [] rightPattern processType).get
    (CostRegionTree.build?_isSome_of_wellSorted rightWellSorted)

theorem leftTree_rootIsStatic : leftTree.rootIsStatic = true := by decide
theorem rightTree_rootIsStatic : rightTree.rootIsStatic = true := by decide

noncomputable def leftViewPair : Σ color, leftTree.StaticRootView color :=
  leftTree.staticRootView_of_rootIsStatic leftTree_rootIsStatic

noncomputable def rightViewPair : Σ color, rightTree.StaticRootView color :=
  rightTree.staticRootView_of_rootIsStatic rightTree_rootIsStatic

theorem leftViewPair_color : leftViewPair.1 = .base := by decide
theorem rightViewPair_color : rightViewPair.1 = .base := by decide

noncomputable def leftEnv :=
  CostStaticAtomEnvironment.ofInventory
    (leftViewPair.2.node.semanticAtomEnvironment
      (leftViewPair.2.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1

noncomputable def rightEnv :=
  CostStaticAtomEnvironment.ofInventory
    (rightViewPair.2.node.semanticAtomEnvironment
      (rightViewPair.2.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1

noncomputable def leftFrame : Pattern :=
  leftViewPair.2.node.canonicalizeReifiedTargetFrame leftEnv
    (costStaticReflectivePresentationDecl rhoCIGSLT .base
      rhoReflectivePresentation)

noncomputable def rightFrame : Pattern :=
  rightViewPair.2.node.canonicalizeReifiedTargetFrame rightEnv
    (costStaticReflectivePresentationDecl rhoCIGSLT .base
      rhoReflectivePresentation)

end ForeignSameColorTypedCanary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
