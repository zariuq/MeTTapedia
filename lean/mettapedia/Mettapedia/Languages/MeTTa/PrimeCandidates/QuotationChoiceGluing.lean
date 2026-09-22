import Mettapedia.GSLT.LanguageDef.DialectGluing
import Mettapedia.Languages.MeTTa.PrimeCandidates.NucleusDerivedModalTyping

/-!
# Gluing quotation and choice extensions of MeTTaZero

The nucleus candidate's quotation extension and a choice extension share the
MeTTaZero base.  Their list-level gluing reproduces the direct extension's
constructor labels and rewrite names, keeps those names duplicate-free, and
exposes both quotation crossings and choice rewrites to the OSLF derivation.

The negative control is a rival declaration of the quotation label at another
category.  No presentation with duplicate-free constructor labels can contain
both declarations, and the positive gluing excludes the rival.  These facts
instantiate the general operation and obstruction in `DialectGluing`; they do
not establish a categorical universal property.
-/

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.QuotationChoiceGluing

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.LanguageDef.DialectGluing
open Mettapedia.Languages.MeTTa.PrimeCandidates.NucleusDerivedModalTyping

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
    Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.language
    zeroWithChoice

/-- Gluing along the base reproduces the direct extension's constructor
labels. -/
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
    ("prime-quote", "Atom", "CandidateName") ∈ unaryCrossings quoteAndChoice := by
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
    Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.quoteConstructor.category = "CandidateName" := by
  decide

theorem clashingQuote_category : clashingQuote.category = "Atom" := by
  decide

theorem quoteConstructor_label :
    Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.quoteConstructor.label = "prime-quote" := by
  decide

theorem clashingQuote_ne_quoteConstructor :
    clashingQuote ≠ Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.quoteConstructor := by
  intro equal
  have categories := congrArg GrammarRule.category equal
  rw [clashingQuote_category, quoteConstructor_category] at categories
  exact absurd categories (by decide)

/-- No presentation with duplicate-free constructor labels contains both the
probe's quotation constructor and its rival: the same label at two categories
is an obstruction to any gluing that keeps both. -/
theorem no_presentation_glues_clash (presentation : LanguageDef)
    (quoteMember :
      Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.quoteConstructor ∈ presentation.terms)
    (clashMember : clashingQuote ∈ presentation.terms) :
    ¬ (presentation.terms.map (·.label)).Nodup := by
  have labels : clashingQuote.label =
      Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.quoteConstructor.label := by
    rw [quoteConstructor_label]; decide
  exact not_nodup_labels_of_constructor_clash presentation clashMember quoteMember
    labels clashingQuote_ne_quoteConstructor

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

end Mettapedia.Languages.MeTTa.PrimeCandidates.QuotationChoiceGluing
