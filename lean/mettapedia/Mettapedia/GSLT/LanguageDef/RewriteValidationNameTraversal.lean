import Mettapedia.GSLT.LanguageDef.RewriteValidationBatch
import Mettapedia.OSLF.MeTTaIL.PatternNameTraversal

/-! Check closed rewrites through the ordered name traversal. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

open Mettapedia.OSLF.MeTTaIL.Syntax

private theorem all_eraseDups_eq (members : List String) (accept : String → Bool) :
    members.eraseDups.all accept = members.all accept := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_eraseDups]

/-- The same structural check, sharing each main pattern's name observations.
A universal name test is insensitive to repeated members of the list. -/
def checkByNameTraversal (language : LanguageDef) (rewrite : RewriteRule) : Bool :=
  let left := rewrite.left.names
  let right := rewrite.right.names
  let supplied := left.free ++ rewrite.premises.flatMap (Premise.producedNamesOutside [])
  let labels := constructorLabels language
  contextTypesCheck language rewrite &&
    premiseTypesCheck language rewrite &&
    patternDeclaredCheck language rewrite.left &&
    patternDeclaredCheck language rewrite.right &&
    premisesDeclaredCheck language rewrite &&
    allPatternsScopedCheck rewrite &&
    (left.free ++ right.free ++ rewrite.premises.flatMap (Premise.freeNamesOutside [])).all
      (fun name => decide (name ∉ labels)) &&
    (left.binders ++ right.binders ++
      (rewrite.premises.flatMap LanguageDef.premisePatterns).flatMap
        (fun pattern => pattern.names.binders) ++
      rewrite.premises.flatMap LanguageDef.premiseForAllParams).all
      (fun name => decide (name ∉ labels)) &&
    contextAvoidsConstructorsCheck language rewrite &&
    right.free.all (fun name => decide (name ∈ supplied))

theorem check_eq_checkByNameTraversal (language : LanguageDef) (rewrite : RewriteRule) :
    check language rewrite = checkByNameTraversal language rewrite := by
  simp only [check, checkByNameTraversal, fvarsAvoidConstructorsCheck, bindersAvoidConstructorsCheck,
    rightBoundCheck, all_eraseDups_eq, LanguageDef.patternFvarNames_eq_traversal,
    LanguageDef.patternBinderNames_eq_traversal, LanguageDef.premiseFvarNames_eq_traversal,
    LanguageDef.premiseProducedFvarNames_eq_traversal]
  simp [Pattern.freeNamesOutside, Bool.and_assoc]

/-- Verify the same complete rule list by reducing the structural
name traversal. -/
theorem check_all_eq_checkByNameTraversal (language : LanguageDef) (rewrites : List RewriteRule) :
    rewrites.all (check language) = rewrites.all (checkByNameTraversal language) :=
  congrArg (fun verifier => rewrites.all verifier)
    (funext (check_eq_checkByNameTraversal language))

end Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
