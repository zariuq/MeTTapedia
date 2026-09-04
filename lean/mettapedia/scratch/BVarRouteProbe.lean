/-
# BVar route — minimal kernel probe (singleton shape)
-/

import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureBridge
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderLeftCollapsing
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticStructuralClosure

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-- A bare parallel collection that canonicalizes to a bound variable must be
a singleton of exactly that variable. -/
theorem singleton_bvar_of_canonicalize_collection_eq_bvar
    (declarationColor : CostStaticColor) (elements : List Pattern)
    {index : Nat}
    (canonical :
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
        declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
      canonicalize declaration
        (.collection declaration.parallelCollection elements none) =
      .bvar index) :
    elements = [.bvar index] := by
  cases elements with
  | nil =>
    simp [canonicalize, canonicalizeList, normalizeParallelElements,
      collapseParallel, parallelSplice,
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns] at canonical
  | cons element elements =>
    cases elements with
    | nil =>
      rw [nil_cons_collection_canonicalize_singleton
        (declarationColor := declarationColor)] at canonical
      have elementEq : canonicalize _element_eq
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl) element =
            .bvar index := canonical
      have elementIsBvar : element = .bvar index :=
        canonicalize_eq_bvar element (costStaticReflectivePresentationDecl
          rhoCIGSLT declarationColor rhoReflectivePresentation.toReflectivePresentationDecl)
          elementEq
      exact elementIsBvar ▸ rfl
    | cons second remainder => simp_all

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
