import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureBridge

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

-- Step 1: does the collapsing-root disjunct on an .apply give the quote head?
example (declaration : ReflectivePresentationDecl) (w : String) (args : List Pattern)
    (h : CollapsingRoot declaration (.apply w args)) :
    w = declaration.quoteConstructor := by
  rcases h with ⟨as, hEq⟩ | ⟨es, hEq⟩
  · exact (Pattern.apply.inj hEq).1
  · exact absurd hEq (by simp)

