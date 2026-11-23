import Mettapedia.GSLT.LanguageDef.TptpNamedFofToResolvedRules
import Mettapedia.GSLT.LanguageDef.RewriteValidationNameTraversal

/-! Validate the authored rules for named-to-resolved FOF. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpNamedFofToResolvedLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

private theorem constructorLabels_nodup :
    (language.terms.map (·.label)).Nodup := by
  decide +kernel

private theorem rewrites_checked :
    language.rewrites.all (RewriteValidationCertificate.check language) = true :=
  (RewriteValidationCertificate.check_all_eq_checkByNameTraversal language _).trans
    (by decide +kernel)

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide +kernel
  exact RewriteValidationCertificate.validateRewrite_eq_nil_of_all
    constructorLabels_nodup rewrites_checked

theorem source_types_are_prefix :
    TptpNamedFofLanguageDef.language.types.IsPrefix language.types := by
  simp [language]

theorem source_terms_are_prefix :
    TptpNamedFofLanguageDef.language.terms.IsPrefix language.terms := by
  simp [language]

theorem language_supported : CanonicalWire.languageSupported language := by
  decide +kernel

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

namespace Canary

def sameName : Pattern := a "X"
def otherName : Pattern := a "Y"

theorem equality_service_selects_equal :
    PatternEqualityDecision.relationTuples
      PatternEqualityDecision.relationName
      [sameName, sameName, v "decision"] =
        [[sameName, sameName, PatternEqualityDecision.equal]] := by
  exact PatternEqualityDecision.equal_exact sameName (v "decision")

theorem equality_service_selects_different :
    PatternEqualityDecision.relationTuples
      PatternEqualityDecision.relationName
      [sameName, otherName, v "decision"] =
        [[sameName, otherName, PatternEqualityDecision.different]] := by
  apply PatternEqualityDecision.different_exact
  decide

theorem free_lookup_has_no_root_rule :
    rewrites.filter (fun rule =>
      match rule.left with
      | .apply "tptp-fof-resolve:lookup"
          [_, .apply "tptp-fof-resolve:environment-nil" []] => true
      | _ => false) = [] := by
  decide +kernel

end Canary

#print axioms rewrite_count
#print axioms language_validate
#print axioms source_types_are_prefix
#print axioms source_terms_are_prefix
#print axioms language_supported
#print axioms Canary.equality_service_selects_equal
#print axioms Canary.equality_service_selects_different
#print axioms Canary.free_lookup_has_no_root_rule

end Mettapedia.GSLT.LanguageDef.TptpNamedFofToResolvedLanguageDef
