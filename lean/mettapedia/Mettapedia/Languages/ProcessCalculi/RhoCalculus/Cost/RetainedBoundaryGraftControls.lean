import Mettapedia.GSLT.LanguageDef.Cost.StaticArgumentBoundaryRefinement
import Mettapedia.GSLT.LanguageDef.CostSemanticSection
import Mettapedia.GSLT.LanguageDef.Cost.CodeAuthority
import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws

/-!
# A real rho principal grafted into a static quotation frame

The supplied retained input subtree is the initial compiler output for an
admitted generated input.  Grafting it as the argument of a static quotation
constructs a new frame and an exact singleton boundary at that occurrence.
The graft does not rerun the compiler on the enclosing quotation.  Its
restoration is exact, and its literal code introduces no current authority.

These controls do not compile every original rho term, interpret complete
source commitments, or assert an unfunded operational communication.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RetainedBoundaryGraftControls

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Framework.ConstructorCategory
open LanguageDefContinuedInteraction CostCanonicalLaws WellSorted
open StaticArgumentBoundaryRefinement

def quoteShell : rhoCIGSLT.DeclaredCostConstructor :=
  ⟨.base rhoQuoteConstructor, trivial⟩

theorem quote_static : rhoCIGSLT.declaredCostConstructorRole quoteShell = .static .base :=
  rhoCIGSLT.declaredCostConstructorRole_base_of_nonprincipal rhoQuoteConstructor
    (by
      intro equal
      have labels := congrArg (fun constructor => constructor.1.label) equal
      have different : ("NQuote" : String) ≠ "PInput" := by decide +kernel
      exact different labels)
    (by
      intro equal
      have labels := congrArg (fun constructor => constructor.1.label) equal
      have different : ("NQuote" : String) ≠ "POutput" := by decide +kernel
      exact different labels)

def quotePreimage : CostStaticConstructorPreimage rhoCIGSLT .base quoteShell :=
  costStaticConstructorPreimage rhoCIGSLT .base quoteShell quote_static

theorem quote_parameter : quotePreimage.sourceConstructor.1.params =
    [.simple "p" (.base "Proc")] := rfl

theorem quote_not_bare : ¬ UsesBareCollection quotePreimage.sourceConstructor.1 := by
  simp [UsesBareCollection, quote_parameter]

theorem quote_category_supported : quotePreimage.sourceConstructor.1.category ∈
    rhoCIGSLT.theory.presentation.presentation.language.types := by decide +kernel

def inputPrincipal : rhoCIGSLT.DeclaredCostConstructor :=
  ⟨.base rhoCIGSLT.cut.program.constructor, trivial⟩

theorem input_not_static : rhoCIGSLT.declaredCostConstructorRole inputPrincipal ≠
    .static .base := by
  unfold inputPrincipal
  rw [rhoCIGSLT.declaredCostConstructorRole_base_of_principal
    rhoCIGSLT.cut.program.constructor (Or.inl rfl)]
  intro equality
  cases equality

def inputArguments : List Pattern :=
  [.apply (costBaseConstructorName "NQuote")
      [.apply (costBaseConstructorName "PZero") []],
    .lambda none (.apply (costWrappedConstructorName "PZero") [])]

def inputPattern : Pattern :=
  .apply (rhoCIGSLT.renderDeclaredCostConstructor inputPrincipal) inputArguments

theorem input_admitted :
    ReflectiveWellSorted.OpenPatternWellSorted rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT) (.base "Proc"))
      inputPattern :=
  (ReflectiveWellSorted.checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _ _).mp
    (by decide +kernel)

/-- This compiler call supplies the initial retained input, before grafting. -/
def inputTree : CostSemanticTree rhoCIGSLT FreeTypeContext.empty [] []
    inputPattern (.base (costBaseSortName "Proc")) :=
  CostSemanticOpenElaboration.compile rhoCIGSLT rho_costStaticCanonicalPathSafe
    (targetSort := CostStaticColor.base.mapLangSort rhoCIGSLT
      rhoCIGSLT.theory.presentation.interactingLangSort)
    ⟨inputPattern, input_admitted⟩

def quotedInput : Pattern := .apply (costBaseConstructorName "NQuote") [inputPattern]

/-- The actual enclosing frame, derived directly from the refined plan. -/
noncomputable def graftedFrame : CostStaticRegionNode rhoCIGSLT .base FreeTypeContext.empty :=
  frame (targetBound := []) quoteShell quote_static quotePreimage quote_not_bare
    "p" (.base "Proc") quote_parameter quote_category_supported inputPrincipal
    input_not_static inputArguments input_admitted

/-- The supplied input tree is grafted into the new enclosing static frame. -/
noncomputable def graftedTree : CostSemanticTree rhoCIGSLT FreeTypeContext.empty [] []
    quotedInput (.base (costBaseSortName "Name")) :=
  semanticTree (targetBound := []) quoteShell quote_static quotePreimage quote_not_bare
    "p" (.base "Proc") quote_parameter quote_category_supported inputPrincipal
    input_not_static inputArguments input_admitted rho_costStaticCanonicalPathSafe inputTree

theorem grafted_tree_inhabited : Nonempty
    (CostSemanticTree rhoCIGSLT FreeTypeContext.empty [] []
      quotedInput (.base (costBaseSortName "Name"))) := ⟨graftedTree⟩

/-- The principal contributes one real boundary at the quotation argument. -/
theorem grafted_boundary_count : graftedFrame.boundaryTable.entries.length = 1 := rfl

theorem grafted_boundary_origin : graftedFrame.plan.occurrences =
    [{ context := .apply (costBaseConstructorName "NQuote") [] .hole [],
       content := inputPattern }] := rfl

theorem grafted_restoration :
    graftedFrame.boundaryTable.restoreSupportedSkeleton []
      graftedFrame.mappedThickenedSkeleton.1 = quotedInput :=
  graftedFrame.restore_mappedThickenedSkeleton_eq_term

/-- Code admission is separate from sorting and from operational funding. -/
theorem grafted_currentLayerCode : CurrentLayerCode quotedInput :=
  (checkCurrentLayerCode_iff quotedInput).mp (by decide +kernel)

theorem current_funding_not_admitted (stack : Pattern) :
    ¬ CurrentLayerCode (.apply costFundingConstructorName [stack]) :=
  funding_not_currentLayerCode stack

#print axioms grafted_tree_inhabited
#print axioms grafted_boundary_count
#print axioms grafted_restoration
#print axioms grafted_currentLayerCode

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RetainedBoundaryGraftControls
