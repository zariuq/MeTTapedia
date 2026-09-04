import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.GSLT.LanguageDef.TptpNamedFofLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpOfficialAbstractSyntax
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Native types for named semantic FOF

The named FOF carrier is an inert but nontrivial GSLT.  Its native structural
type is generated from its actual constructor rows; its behavioral one-step
types are empty because the carrier deliberately performs no computation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpNamedFofNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open Mettapedia.GSLT.LanguageDef.TptpNamedFofLanguageDef

def formulaNativeType : langNativeType language "TptpNamedFof:Formula" where
  sort := "TptpNamedFof:Formula"
  pred := fun term =>
    checkHasType language WellSorted.FreeTypeContext.empty [] term
      (.base "TptpNamedFof:Formula") = true

theorem shadowing_formula_inhabits_native_type :
    formulaNativeType.pred Canary.encoded := by
  change checkHasType language WellSorted.FreeTypeContext.empty []
      Canary.encoded (.base "TptpNamedFof:Formula") = true
  decide +kernel

theorem official_ast_is_not_named_formula :
    ¬ formulaNativeType.pred
      TptpOfficialAbstractSyntax.fofAnnotatedExample := by
  change ¬ (checkHasType language WellSorted.FreeTypeContext.empty []
      TptpOfficialAbstractSyntax.fofAnnotatedExample
      (.base "TptpNamedFof:Formula") = true)
  decide +kernel

theorem exact_target_native_type_empty (source target : Pattern) :
    ¬ (gsltOSLF theory).satisfies source
      (exactTargetNativeType theory target).pred := by
  rw [satisfies_exactTargetNativeType_iff_step]
  exact theory_no_step source target

#print axioms shadowing_formula_inhabits_native_type
#print axioms official_ast_is_not_named_formula
#print axioms exact_target_native_type_empty

end Mettapedia.GSLT.LanguageDef.TptpNamedFofNTT
