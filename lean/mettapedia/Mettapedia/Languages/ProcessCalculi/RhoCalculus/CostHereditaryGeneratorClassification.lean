import Mettapedia.GSLT.LanguageDef.CostHereditaryContextRoute
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratedOccurrenceAbsorption

/-!
# Root classification for hereditary rho Cost generators

An exact rho generator occurrence carries its authored base-or-wrapped
declaration.  A retained Cost elaboration independently exposes the colour of
its selected static root.  This module joins those two proof-relevant facts
without inspecting compact constructor spellings.

The local semantic certificate is either a complete two-environment atom
cospan or an asymmetric one-atom join.  Exact normalized equality is derived
from that certificate; it is not stored as a field.  Structural lifting away
from the redex remains the generic tree-alignment problem.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- One exact generated rho occurrence classified against the selected colour
of its retained left root, together with the semantic root certificate that
closes that local cell. -/
structure RhoCostGeneratorRootAlignment
    (kernel : CostStaticNormalizationKernel rhoCIGSLT)
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    {left right : OpenTerm rhoCIGSLT.costWholeLanguage targetFree targetBound
      targetSort}
    (generator : openEquationGenerator rhoCIGSLT.costIGSLT targetFree
      targetBound targetSort left right) where
  occurrence : EquationSemantics.AuthoredGeneratorWitness defaultBasePremises
    rhoCIGSLT.costWholeLanguage left.1 right.1
  erasesTo : occurrence.erase = generator
  absorption : RhoCostGeneratorAbsorption occurrence
  leftElaboration : CostOpenElaboration rhoCIGSLT left
  rightElaboration : CostOpenElaboration rhoCIGSLT right
  regionColor : CostStaticColor
  leftRoot : CostRegionTree.StaticRootColor rhoCIGSLT targetFree
    leftElaboration.tree regionColor
  position : RhoCostDeclarationRegionPosition absorption regionColor
  rootBridge : CostRegionRootNormalizationBridge rhoCIGSLT kernel targetFree
    leftElaboration.tree rightElaboration.tree

namespace RhoCostGeneratorRootAlignment

/-- The declaration/root comparison is exhaustive because Cost has exactly
two static colours. -/
def positionCases
    {kernel : CostStaticNormalizationKernel rhoCIGSLT}
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    {left right : OpenTerm rhoCIGSLT.costWholeLanguage targetFree targetBound
      targetSort}
    {generator : openEquationGenerator rhoCIGSLT.costIGSLT targetFree
      targetBound targetSort left right}
    (alignment : RhoCostGeneratorRootAlignment kernel generator) :
    alignment.absorption.color = alignment.regionColor ∨
      alignment.absorption.color = alignment.regionColor.flip :=
  match alignment.position with
  | .selected same => Or.inl same
  | .foreign opposite => Or.inr opposite

/-- Forget the rho-specific declaration/root comparison while retaining the
proof-relevant semantic bridge. -/
def toTreeAlignment
    {kernel : CostStaticNormalizationKernel rhoCIGSLT}
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    {left right : OpenTerm rhoCIGSLT.costWholeLanguage targetFree targetBound
      targetSort}
    {generator : openEquationGenerator rhoCIGSLT.costIGSLT targetFree
      targetBound targetSort left right}
    (alignment : RhoCostGeneratorRootAlignment kernel generator) :
    CostRegionTreeNormalizationAlignment rhoCIGSLT kernel targetFree
      alignment.leftElaboration.tree alignment.rightElaboration.tree :=
  alignment.rootBridge.toTreeAlignment

/-- A classified local root cell is already an exact generic generator-tree
route; occurrence identity survives unchanged. -/
def toGeneratorTreeRoute
    {kernel : CostStaticNormalizationKernel rhoCIGSLT}
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    {left right : OpenTerm rhoCIGSLT.costWholeLanguage targetFree targetBound
      targetSort}
    {generator : openEquationGenerator rhoCIGSLT.costIGSLT targetFree
      targetBound targetSort left right}
    (alignment : RhoCostGeneratorRootAlignment kernel generator) :
    CostGeneratorTreeNormalizationRoute rhoCIGSLT kernel generator where
  occurrence := alignment.occurrence
  erasesTo := alignment.erasesTo
  leftElaboration := alignment.leftElaboration
  rightElaboration := alignment.rightElaboration
  route := .root alignment.rootBridge
  localization := ⟨alignment.occurrence.redexContext, rfl⟩

/-- Forget the unique root route only after it has retained the rho
declaration/root classification. -/
def toGeneratorTreeAlignment
    {kernel : CostStaticNormalizationKernel rhoCIGSLT}
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    {left right : OpenTerm rhoCIGSLT.costWholeLanguage targetFree targetBound
      targetSort}
    {generator : openEquationGenerator rhoCIGSLT.costIGSLT targetFree
      targetBound targetSort left right}
    (alignment : RhoCostGeneratorRootAlignment kernel generator) :
    CostGeneratorTreeNormalizationAlignment rhoCIGSLT kernel generator :=
  alignment.toGeneratorTreeRoute.toAlignment

/-- Exact equality of local hereditary representatives follows from the
semantic root certificate. -/
theorem normalize_patterns_eq
    {kernel : CostStaticNormalizationKernel rhoCIGSLT}
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    {left right : OpenTerm rhoCIGSLT.costWholeLanguage targetFree targetBound
      targetSort}
    {generator : openEquationGenerator rhoCIGSLT.costIGSLT targetFree
      targetBound targetSort left right}
    (alignment : RhoCostGeneratorRootAlignment kernel generator) :
    (alignment.leftElaboration.tree.normalize
        (normalizeStatic := kernel.normalize)).pattern =
      (alignment.rightElaboration.tree.normalize
        (normalizeStatic := kernel.normalize)).pattern :=
  alignment.toTreeAlignment.normalize_pattern_eq

end RhoCostGeneratorRootAlignment

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
