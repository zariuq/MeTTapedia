import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation

/-!
# The platform presentation passes its own validation gate

`LanguageDef.validate` is the presentation validator: it checks cross-references
between types, constructors, relations and syntax parameters, and it rejects the
silent-wildcard shapes an authored rule can fall into.  Running it on a
generated presentation is what makes "this is a presentation" a theorem rather
than a convention, and the platform's arity-indexed bundle former exists
precisely so that this check can pass.

**Why the check needs help.**  Two of the validator's helpers do not reduce in
the kernel: `Pattern.freeFvarNames` recurses over a nested `List Pattern` by
well-founded recursion, and `patternBinderNames` recurses through `List.attach`.
`RedexPosition` supplies structurally recursive counterparts for both, with the
agreement theorems, so a validation run is turned into a kernel computation
without introducing a second convention.  That is what the rewriting below
does; everything after it is `decide +kernel`.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformValidation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation

/-! ## The generated premises, exposed -/

theorem joinRule_premises (arity : Nat) :
    (joinRule arity).premises
      = [Premise.relationQuery guardRelation (channelPatterns arity)] := rfl

theorem persistentJoinRule_premises (arity : Nat) :
    (persistentJoinRule arity).premises
      = [Premise.relationQuery guardRelation (channelPatterns arity)] := rfl

/-! ## Each row of the presentation, checked -/

/-- **The reflection equation validates.** -/
theorem validateEquation_quoteDrop :
    LanguageDef.validateEquation (rhoPlatform [2]) quoteDropEquation = [] := by
  simp only [LanguageDef.validateEquation, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, ← fvarNames_eq, ← binderNames_eq]
  decide +kernel

/-- **The join of arity two validates.** -/
theorem validateRewrite_join :
    LanguageDef.validateRewrite (rhoPlatform [2]) (joinRule 2) = [] := by
  simp only [LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
    joinRule_premises, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
    patternFvarNames_nil, flatMap_patternFvarNames_nil,
    ← binderNames_eq, ← binderNamesList_eq]
  decide +kernel

/-- **And so does the persistent join**, whose right-hand side keeps the
receiver. -/
theorem validateRewrite_persistentJoin :
    LanguageDef.validateRewrite (rhoPlatform [2]) (persistentJoinRule 2) = [] := by
  simp only [LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
    persistentJoinRule_premises, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
    patternFvarNames_nil, flatMap_patternFvarNames_nil,
    ← binderNames_eq, ← binderNamesList_eq]
  decide +kernel

/-! ## The whole presentation -/

theorem rhoPlatform_equations :
    (rhoPlatform [2]).equations = [quoteDropEquation] := rfl

theorem rhoPlatform_rewrites_pair :
    (rhoPlatform [2]).rewrites = [joinRule 2, persistentJoinRule 2] := rfl

/-- **The platform presentation validates.**  Every cross-reference resolves,
no name is declared twice, and no rule carries a silent wildcard. -/
theorem rhoPlatform_validate : (rhoPlatform [2]).validate = [] := by
  rw [LanguageDef.validate]
  simp only [rhoPlatform_equations, rhoPlatform_rewrites_pair, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, validateEquation_quoteDrop,
    validateRewrite_join, validateRewrite_persistentJoin]
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformValidation
