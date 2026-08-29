import Mettapedia.Languages.MeTTa.Prime.NucleusDerivedModalTyping
import Mathlib.Data.List.Nodup

/-!
# Gluing two extensions of one base presentation

The disjoint structural coproduct is the right construction for *independent*
guest languages: its symbol tags deliberately prevent identifications.  Two
dialect views of *one* language are the opposite situation: they share a base
and must be identified along it.  This module gives the smallest honest
version of that gluing — two extensions of a common base, joined along the
base with the base kept once — together with a positive instance, a precise
obstruction, and an explicit statement of what is *not* yet earned.

* Positive: the quotation extension of MeTTaZero (the exploratory Prime probe)
  and a choice extension of MeTTaZero glue along MeTTaZero to a presentation
  that is exactly the probe-with-choice extension, keeps constructor and
  rewrite names duplicate-free, and exposes both the quotation crossings and
  the choice rewrites to the OSLF derivation.
* Obstruction: two extensions that declare the same constructor label at
  different categories cannot both be included in any presentation with
  duplicate-free constructor labels.  Nothing glues them.
* Not earned: a universal property.  Inclusions here are list-level; a
  categorical pushout in the structural presentation category requires the
  glued presentation to be validated and the inclusions to be
  `StructuralMorphism`s, which this module does not construct.
-/

namespace Mettapedia.GSLT.LanguageDef.DialectGluing

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.MeTTa.Prime.NucleusDerivedModalTyping

/-- Join two extensions of `base`, keeping every base declaration once.  The
right extension's declarations are added only when their label or name is not
already declared by the base. -/
def glue (name : String) (base left right : LanguageDef) : LanguageDef :=
  { name
    types := left.types ++
      right.types.filter (fun declaration =>
        !(base.typeNames.contains declaration.name))
    terms := left.terms ++
      right.terms.filter (fun rule => !(base.terms.any (·.label == rule.label)))
    equations := left.equations ++
      right.equations.filter (fun equation =>
        !(base.equations.any (·.name == equation.name)))
    rewrites := left.rewrites ++
      right.rewrites.filter (fun rewrite =>
        !(base.rewrites.any (·.name == rewrite.name))) }

/-! ## Positive instance: quotation and choice glued along MeTTaZero -/

def zeroWithChoice : LanguageDef :=
  { Mettapedia.Languages.MeTTa.MeTTaZero.language with
    name := "metta-zero-with-choice"
    terms := Mettapedia.Languages.MeTTa.MeTTaZero.language.terms ++
      [chooseConstructor, collectConstructor]
    rewrites := Mettapedia.Languages.MeTTa.MeTTaZero.language.rewrites ++
      [chooseLeftRewrite, chooseRightRewrite] }

def quoteAndChoice : LanguageDef :=
  glue "metta-zero-quote-and-choice"
    Mettapedia.Languages.MeTTa.MeTTaZero.language
    Mettapedia.Languages.MeTTa.Prime.LanguageDef.language
    zeroWithChoice

/-- Gluing along the base reproduces the direct extension: the glued
constructors are exactly the probe-with-choice constructors. -/
theorem quoteAndChoice_terms_eq_direct_extension :
    quoteAndChoice.terms.map (·.label) = probeWithChoice.terms.map (·.label) := by
  decide

theorem quoteAndChoice_rewrites_eq_direct_extension :
    quoteAndChoice.rewrites.map (·.name) = probeWithChoice.rewrites.map (·.name) := by
  decide

theorem quoteAndChoice_constructor_names_nodup :
    (quoteAndChoice.terms.map (·.label)).Nodup := by
  decide

theorem quoteAndChoice_rewrite_names_nodup :
    (quoteAndChoice.rewrites.map (·.name)).Nodup := by
  decide

/-- Both extensions' contributions are visible to the derivation: the
quotation crossing and the choice rewrite are present in the glued
presentation. -/
theorem quoteAndChoice_has_quote_crossing :
    ("prime-quote", "Atom", "PrimeName") ∈ unaryCrossings quoteAndChoice := by
  decide

theorem quoteAndChoice_has_choice_rewrite :
    "prime-choose-left" ∈ quoteAndChoice.rewrites.map (·.name) := by
  decide

/-! ## Obstruction: a label clash cannot be glued -/

/-- A hypothetical rival extension declaring `prime-quote` at category `Atom`. -/
def clashingQuote : GrammarRule :=
  { label := "prime-quote"
    category := "Atom"
    params := [.simple "term" (.base "Atom")]
    syntaxPattern := [] }

theorem quoteConstructor_category :
    Mettapedia.Languages.MeTTa.Prime.LanguageDef.quoteConstructor.category = "PrimeName" := by
  decide

theorem clashingQuote_category : clashingQuote.category = "Atom" := by
  decide

theorem quoteConstructor_label :
    Mettapedia.Languages.MeTTa.Prime.LanguageDef.quoteConstructor.label = "prime-quote" := by
  decide

theorem clashingQuote_ne_quoteConstructor :
    clashingQuote ≠ Mettapedia.Languages.MeTTa.Prime.LanguageDef.quoteConstructor := by
  intro equal
  have categories := congrArg GrammarRule.category equal
  rw [clashingQuote_category, quoteConstructor_category] at categories
  exact absurd categories (by decide)

/-- No presentation with duplicate-free constructor labels contains both the
probe's quotation constructor and its rival: the same label at two categories
is an obstruction to any gluing that keeps both. -/
theorem no_presentation_glues_clash (presentation : LanguageDef)
    (quoteMember :
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.quoteConstructor ∈ presentation.terms)
    (clashMember : clashingQuote ∈ presentation.terms) :
    ¬ (presentation.terms.map (·.label)).Nodup := by
  intro nodup
  have injective := List.inj_on_of_nodup_map nodup
  have labels : clashingQuote.label =
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.quoteConstructor.label := by
    rw [quoteConstructor_label]; decide
  have equal := injective clashMember quoteMember labels
  exact clashingQuote_ne_quoteConstructor equal

/-- The positive instance really is duplicate-free while containing the
probe's quotation constructor, so the obstruction is not vacuous. -/
theorem quoteAndChoice_excludes_clash :
    clashingQuote ∉ quoteAndChoice.terms := by
  intro member
  exact no_presentation_glues_clash quoteAndChoice (by decide) member
    quoteAndChoice_constructor_names_nodup

#print axioms quoteAndChoice_terms_eq_direct_extension
#print axioms quoteAndChoice_has_quote_crossing
#print axioms no_presentation_glues_clash
#print axioms quoteAndChoice_excludes_clash

end Mettapedia.GSLT.LanguageDef.DialectGluing
