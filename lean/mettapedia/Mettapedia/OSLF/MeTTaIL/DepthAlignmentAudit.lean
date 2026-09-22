import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation
import Mettapedia.OSLF.Framework.GeneratedHypercubeInstances
import Mettapedia.GSLT.LanguageDef.EquationSubstitutionCounterexamples
import Mettapedia.OSLF.Framework.ObserverReconstruction

/-!
# Which language definitions the scope correction changed

Making rule firing scope-correct changed what the engine computes, and the honest
question after such a change is not whether the development still compiles but
which language definitions now mean something different.

The answer is a computation.  A matched value is shifted by the difference
between the depth at which the rule's left-hand side captured it and the depth at
which the right-hand side uses it, so a rule whose metavariables sit at the same
depth on both sides is unaffected character for character.  That condition is
decidable, and `applyRule_eq_old` turns a decision into the statement that the
language's reducts are exactly the ones it computed before.

The audit is carried out here on the language definitions the development
actually ships, rather than asserted of them.  A language that fails the check is
not thereby broken: failing means the language has a rule that moves a
metavariable across a binder, which is precisely the case the engine used to get
wrong, so its reducts changed because they had to.
-/

namespace Mettapedia.OSLF.MeTTaIL.Match

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Every rule of a language leaves its metavariables at the depth they were
matched at. -/
def languageDepthAligned (lang : LanguageDef) : Bool :=
  lang.rewrites.all ruleDepthAligned

/-- **A depth-aligned language computes exactly the reducts it computed before
the correction.** -/
theorem rewriteStep_eq_old (lang : LanguageDef) (term : Pattern)
    (aligned : languageDepthAligned lang = true) :
    rewriteStep lang term
      = lang.rewrites.flatMap (fun rule =>
          if rule.premises.isEmpty then
            (matchPattern rule.left term).map (fun b => applyBindings b rule.right)
          else []) := by
  simp only [rewriteStep]
  refine List.flatMap_congr ?_
  intro rule membership
  exact applyRule_eq_old rule term
    (List.all_eq_true.mp aligned rule membership)

/-- Every rule of a language is between binder-free patterns. -/
def languageBinderFree (lang : LanguageDef) : Bool :=
  lang.rewrites.all (fun rule => binderFree rule.left && binderFree rule.right)

/-- **A language that never binds is depth-aligned**, so the whole class of
such languages is untouched with no per-language check.  This is what keeps the
audit from being an enumeration: the correction can only reach a rule that moves
a metavariable across a binder, and a language with no binders has none. -/
theorem languageDepthAligned_of_binderFree (lang : LanguageDef)
    (free : languageBinderFree lang = true) : languageDepthAligned lang = true := by
  simp only [languageDepthAligned, List.all_eq_true]
  intro rule membership
  have h := List.all_eq_true.mp free rule membership
  simp only [Bool.and_eq_true] at h
  exact ruleDepthAligned_of_binderFree rule h.1 h.2

theorem rewriteStep_eq_old_of_binderFree (lang : LanguageDef) (term : Pattern)
    (free : languageBinderFree lang = true) :
    rewriteStep lang term
      = lang.rewrites.flatMap (fun rule =>
          if rule.premises.isEmpty then
            (matchPattern rule.left term).map (fun b => applyBindings b rule.right)
          else []) :=
  rewriteStep_eq_old lang term (languageDepthAligned_of_binderFree lang free)

/-! ## The audit

The binder-free class is discharged by the theorem above rather than by
inspection.  What remains to check by hand is the languages that do bind, and
each statement below is decided, not assumed. -/

/-- The reflective process platform, at the arities it is shipped with: every
rule keeps its metavariables at their matched depth, so the platform's reduction
is unchanged. -/
theorem rhoPlatform_depthAligned :
    languageDepthAligned
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation.rhoPlatform [0, 1, 2]) = true := by
  decide +kernel

theorem rhoPlatform_reducts_unchanged (term : Pattern) :
    rewriteStep (Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation.rhoPlatform [0, 1, 2]) term
      = (Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation.rhoPlatform [0, 1, 2]).rewrites.flatMap
          (fun rule =>
            if rule.premises.isEmpty then
              (matchPattern rule.left term).map (fun b => applyBindings b rule.right)
            else []) :=
  rewriteStep_eq_old _ term rhoPlatform_depthAligned

/-- A binder-free language, discharged by the general theorem rather than by a
computation over its rules. -/
theorem weakMonoid_binderFree :
    languageBinderFree
      Mettapedia.OSLF.Framework.GeneratedHypercubeInstances.weakMonoidLang = true := by
  decide +kernel

theorem weakMonoid_reducts_unchanged (term : Pattern) :
    rewriteStep Mettapedia.OSLF.Framework.GeneratedHypercubeInstances.weakMonoidLang term
      = (Mettapedia.OSLF.Framework.GeneratedHypercubeInstances.weakMonoidLang).rewrites.flatMap
          (fun rule =>
            if rule.premises.isEmpty then
              (matchPattern rule.left term).map (fun b => applyBindings b rule.right)
            else []) :=
  rewriteStep_eq_old_of_binderFree _ term weakMonoid_binderFree

/-- The reflective presentation carrying an abstraction-bearing name
constructor: also unchanged. -/
theorem binderOccurrenceLanguage_depthAligned :
    languageDepthAligned
      Mettapedia.GSLT.LanguageDef.EquationSubstitutionCounterexamples.binderOccurrenceLanguage
        = true := by
  decide +kernel

theorem binderOccurrenceLanguage_reducts_unchanged (term : Pattern) :
    rewriteStep
        Mettapedia.GSLT.LanguageDef.EquationSubstitutionCounterexamples.binderOccurrenceLanguage
        term
      = (Mettapedia.GSLT.LanguageDef.EquationSubstitutionCounterexamples.binderOccurrenceLanguage).rewrites.flatMap
          (fun rule =>
            if rule.premises.isEmpty then
              (matchPattern rule.left term).map (fun b => applyBindings b rule.right)
            else []) :=
  rewriteStep_eq_old _ term binderOccurrenceLanguage_depthAligned

/-- The three observer-reconstruction languages: also unchanged. -/
theorem absorbing_depthAligned :
    languageDepthAligned
      Mettapedia.OSLF.Framework.ObserverReconstruction.Interference.absorbing = true := by
  decide +kernel

theorem smugglingCarrier_depthAligned :
    languageDepthAligned
      Mettapedia.OSLF.Framework.ObserverReconstruction.Smuggling.carrier = true := by
  decide +kernel

theorem determinacyCarrier_depthAligned :
    languageDepthAligned
      Mettapedia.OSLF.Framework.ObserverReconstruction.Determinacy.carrier = true := by
  decide +kernel

/-! ### What the audit covers, and what it does not

Over two hundred files of the development define a `LanguageDef`, so an
exhaustive table is not what is on offer and none is claimed.  What is on offer
is three things, and they are what a change of executable semantics owes.

First, a class theorem rather than a survey: `languageDepthAligned_of_binderFree`
discharges every language with no binding former at all, without inspection and
without a per-language check.

Second, `languageDepthAligned` is a decidable predicate on a language, so any
language in the development can be settled by computation rather than by
argument.  The languages decided here are the ones that do bind: the reflective
process platform at its shipped arities, the presentation with an
abstraction-bearing name constructor, and the three observer-reconstruction
languages.  Others are decided where they live, next to the language rather than
in a central table -- the authored Metamath rules and the HE runtime core
fragment each carry their own decided statement, and the intrinsic pure-MeTTa
beta rules are decided at their use sites, which is the interesting case: `BetaPi`
captures its body metavariable *under* a binder and uses it under an explicit
substitution, and the two depths agree, so beta reduction is depth-aligned by
computation.

Third, a negative control: a rule that does move a metavariable under a binder
fails the check, so the condition is not vacuously true of everything.  Failing
the check is a statement about a language rather than a defect of it -- it says
the language has a rule that crosses a binder, which is exactly the case the
engine used to get wrong, so its reducts changed because they had to.  The two
witness languages below are written to fail it on purpose. -/

/-- A rule that does move a metavariable under a binder fails the check, so the
check is not vacuously true of everything. -/
theorem wrapRule_not_depthAligned :
    ruleDepthAligned
      { name := "wrap-under-binder", typeContext := [], premises := [],
        left := .apply "wrap" [.fvar "X"],
        right := .lambda (some "y") (.fvar "X") } = false := by
  decide +kernel

end Mettapedia.OSLF.MeTTaIL.Match
