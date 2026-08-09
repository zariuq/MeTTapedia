import Mettapedia.GSLT.LanguageDef.CostReflectiveRootClassification
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratedOccurrenceAbsorption

/-!
# Typed root cases for hereditary rho Cost generators

Every exact rho Cost generator has one generated reflective declaration that
absorbs its retained redex and contractum.  Reflective canonical equality is
first split by the syntax-level root dichotomy.  A collapsing endpoint is
then promoted to an actual proof-relevant static root by the generic typed
classification theorem; the remaining case retains childwise canonical root
alignment.

This is a classifier, not yet a normalization bridge.  Static cases still
require restoration evidence, while the aligned case requires recursive
child alignment.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- Exhaustive typed root cases for the local redex and contractum retained
by one rho Cost absorption witness.  Unlike the raw dichotomy, either
collapsing arm returns an actual static-root certificate for the supplied
tree. -/
theorem RhoCostGeneratorAbsorption.typedRootCases
    {left right : Pattern}
    {witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right}
    (absorption : RhoCostGeneratorAbsorption witness)
    {targetFree : FreeTypeContext} {leftAvailable leftOuter : List TypeExpr}
    {rightAvailable rightOuter : List TypeExpr} {category : String}
    (leftTree : CostRegionTree rhoCIGSLT targetFree leftAvailable leftOuter
      witness.redex (.base category))
    (rightTree : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      witness.contractum (.base category)) :
    Nonempty (Σ color,
        CostRegionTree.StaticRootColor rhoCIGSLT targetFree leftTree color) ∨
      Nonempty (Σ color,
        CostRegionTree.StaticRootColor rhoCIGSLT targetFree rightTree color) ∨
      CanonicalRootAligned absorption.declaration.1 witness.redex
        witness.contractum := by
  rcases canonicalize_eq_root_cases absorption.declaration.1
      absorption.representatives with leftCollapsing | rightOrAligned
  · left
    have declarationEq := absorption.declaration_eq
    rw [declarationEq] at leftCollapsing
    exact leftTree.nonempty_staticRootColor_of_costStatic_collapsingRoot
      rhoCIGSLT absorption.color
      rhoReflectivePresentation.toReflectivePresentationDecl
        (by exact List.mem_cons_self) leftCollapsing
  · rcases rightOrAligned with rightCollapsing | aligned
    · right
      left
      have declarationEq := absorption.declaration_eq
      rw [declarationEq] at rightCollapsing
      exact rightTree.nonempty_staticRootColor_of_costStatic_collapsingRoot
        rhoCIGSLT absorption.color
        rhoReflectivePresentation.toReflectivePresentationDecl
          (by exact List.mem_cons_self) rightCollapsing
    · exact Or.inr (Or.inr aligned)

/-- If neither local endpoint tree is static, the canonicalizer's collapsing
arms are impossible and the two roots align structurally with childwise
canonical equalities.  This is the exact entry condition for multi-child
structural descent. -/
theorem RhoCostGeneratorAbsorption.typedStructuralRootAligned
    {left right : Pattern}
    {witness : ReflectiveEquationSemantics.ReflectiveAuthoredGeneratorWitness
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right}
    (absorption : RhoCostGeneratorAbsorption witness)
    {targetFree : FreeTypeContext} {leftAvailable leftOuter : List TypeExpr}
    {rightAvailable rightOuter : List TypeExpr} {category : String}
    (leftTree : CostRegionTree rhoCIGSLT targetFree leftAvailable leftOuter
      witness.redex (.base category))
    (rightTree : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      witness.contractum (.base category))
    (leftStructural : leftTree.rootIsStatic = false)
    (rightStructural : rightTree.rootIsStatic = false) :
    CanonicalRootAligned absorption.declaration.1 witness.redex
      witness.contractum := by
  rcases absorption.typedRootCases leftTree rightTree with
      leftStatic | rightStatic | aligned
  · exact (leftTree.not_nonempty_staticRootColor_of_rootIsStatic_false
      leftStructural leftStatic).elim
  · exact (rightTree.not_nonempty_staticRootColor_of_rootIsStatic_false
      rightStructural rightStatic).elim
  · exact aligned

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
