import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryGeneratorRootCases
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary

/-!
# Canary checks for typed rho generator root cases

The two positive checks exercise both collapsing forms against real retained
rho trees: a base Quote/Drop application and a wrapped parallel root.  The
negative check records that an ordinary source variable is outside the
collapsing classification.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary

/-- The generic typed classifier recognizes the retained base Quote/Drop
fixture as a static root. -/
theorem rhoBreadthBaseRedexA_rootIsStatic_viaCollapsingClassification :
    CostRegionTree.rootIsStatic rhoBreadthBaseRedexATree = true := by
  apply CostRegionTree.rootIsStatic_of_costStatic_collapsingRoot
    (tree := rhoBreadthBaseRedexATree) rhoCIGSLT .base
    rhoReflectivePresentation.toReflectivePresentationDecl
      (by exact List.mem_cons_self)
  exact Or.inl ⟨[rhoCutOrderBaseDrop (.fvar "a")], rfl⟩

/-- The same classifier recognizes a real wrapped parallel decomposition
without choosing its colour from the collection spelling. -/
theorem rhoCutOrderLeft_rootIsStatic_viaCollapsingClassification :
    CostRegionTree.rootIsStatic rhoCutOrderLeftTree = true := by
  apply CostRegionTree.rootIsStatic_of_costStatic_collapsingRoot
    (tree := rhoCutOrderLeftTree) rhoCIGSLT .wrapped
    rhoReflectivePresentation.toReflectivePresentationDecl
      (by exact List.mem_cons_self)
  exact Or.inr ⟨[
    rhoCutOrderWrappedDrop rhoCutOrderRedex,
    rhoCutOrderWrappedDrop (.fvar "a")], rfl⟩

/-- A source variable is not misclassified as a root-changing reflective
form. -/
theorem rhoSourceVariable_not_collapsingRoot :
    ¬ CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl)
      (.fvar "a") := by
  simp [CollapsingRoot]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
