import Mettapedia.GSLT.LanguageDef.InferenceExtension

/-!
# Language definitions with an authored proof calculus

`CalculusLanguageDef` is the canonical flat language object used by the generic
inference checker.  Its first five fields are an ordinary `LanguageDef`; its
remaining fields declare judgment forms, inference rules, and an optional
conversion interface.  Callers author and pass one value.  The coGSLT
factorization that licenses these fields is exposed by the higher
`CalculusLanguageDef` module, not represented as a pair in checker APIs.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- One flat language definition whose inference layer is authored by the
calculus coGSLT. -/
structure CalculusLanguageDef extends LanguageDef where
  /-- Declared judgment forms. -/
  judgments : List JudgmentDecl := []
  /-- Inference rules over those judgments. -/
  rules : List RuleSchema := []
  /-- An optional rooted conversion interface. -/
  conversion : Option ConversionDecl := none
deriving Repr

namespace CalculusLanguageDef

/-- Fieldwise extensionality for the canonical flat calculus language. -/
@[ext]
theorem ext {first second : CalculusLanguageDef}
    (name : first.name = second.name)
    (types : first.types = second.types)
    (terms : first.terms = second.terms)
    (equations : first.equations = second.equations)
    (rewrites : first.rewrites = second.rewrites)
    (judgments : first.judgments = second.judgments)
    (rules : first.rules = second.rules)
    (conversion : first.conversion = second.conversion) :
    first = second := by
  cases first with
  | mk firstLanguage firstJudgments firstRules firstConversion =>
      cases second with
      | mk secondLanguage secondJudgments secondRules secondConversion =>
          have languageEquality : firstLanguage = secondLanguage := by
            cases firstLanguage
            cases secondLanguage
            simp_all
          cases languageEquality
          simp_all

/-- Extend an ordinary language definition by an authored proof calculus and
return the canonical flat language object.  This is the specialization of
coGSLT-layer composition used by elaborators; it does not expose a nested
checker representation. -/
def extend (language : LanguageDef) (calculus : ProofCalculus) :
    CalculusLanguageDef where
  toLanguageDef := language
  judgments := calculus.judgments
  rules := calculus.rules
  conversion := calculus.conversion

/-- The calculus coordinate selected from the flat language object.  This is
an automatic projection for coGSLT elaboration and never a second public
language value. -/
abbrev toCalculus (definition : CalculusLanguageDef) : ProofCalculus where
  judgments := definition.judgments
  rules := definition.rules
  conversion := definition.conversion

@[simp] theorem extend_toLanguageDef (language : LanguageDef)
    (calculus : ProofCalculus) :
    (extend language calculus).toLanguageDef = language :=
  rfl

@[simp] theorem extend_toCalculus (language : LanguageDef)
    (calculus : ProofCalculus) :
    (extend language calculus).toCalculus = calculus :=
  rfl

/-! The fieldwise projection laws make the internal factorization transparent
to simplification.  Clients manipulate one flat definition; proofs may still
recover either authored coordinate without unfolding the record constructor. -/

@[simp] theorem extend_name (language : LanguageDef) (calculus : ProofCalculus) :
    (extend language calculus).name = language.name := rfl

@[simp] theorem extend_types (language : LanguageDef) (calculus : ProofCalculus) :
    (extend language calculus).types = language.types := rfl

@[simp] theorem extend_terms (language : LanguageDef) (calculus : ProofCalculus) :
    (extend language calculus).terms = language.terms := rfl

@[simp] theorem extend_equations (language : LanguageDef) (calculus : ProofCalculus) :
    (extend language calculus).equations = language.equations := rfl

@[simp] theorem extend_rewrites (language : LanguageDef) (calculus : ProofCalculus) :
    (extend language calculus).rewrites = language.rewrites := rfl

@[simp] theorem extend_judgments (language : LanguageDef) (calculus : ProofCalculus) :
    (extend language calculus).judgments = calculus.judgments := rfl

@[simp] theorem extend_rules (language : LanguageDef) (calculus : ProofCalculus) :
    (extend language calculus).rules = calculus.rules := rfl

@[simp] theorem extend_conversion (language : LanguageDef) (calculus : ProofCalculus) :
    (extend language calculus).conversion = calculus.conversion := rfl

/-- Projection followed by extension reconstructs the same flat definition.
This is the public eta law for the internal coGSLT factorization. -/
@[simp] theorem extend_eta (definition : CalculusLanguageDef) :
    extend definition.toLanguageDef definition.toCalculus = definition := by
  cases definition
  rfl

/-- The calculus coordinate is not silently erased by extension. -/
theorem extend_ne_of_calculus_ne (language : LanguageDef)
    {first second : ProofCalculus} (different : first ≠ second) :
    extend language first ≠ extend language second := by
  intro equal
  exact different (congrArg toCalculus equal)

/-- The object-language coordinate is not silently erased by extension. -/
theorem extend_ne_of_language_ne {first second : LanguageDef}
    (different : first ≠ second) (calculus : ProofCalculus) :
    extend first calculus ≠ extend second calculus := by
  intro equal
  exact different (congrArg CalculusLanguageDef.toLanguageDef equal)

end CalculusLanguageDef

end Mettapedia.GSLT.LanguageDef
