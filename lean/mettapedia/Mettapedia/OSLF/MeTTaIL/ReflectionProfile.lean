import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Reflection profiles beside the five-field language core

Reflective presentations and rule selections parameterize an interpretation
of a `LanguageDef`; they are not declarations of the underlying language.
This module supplies the small, dependency-neutral payload used by OSLF
interpreters.  Admission, coGSLT syntax, and staged realization live in the
higher `GSLT.LanguageDef.ReflectionExtension` layer.
-/

namespace Mettapedia.OSLF.MeTTaIL.Reflection

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The complete reflective payload over one five-field language. -/
structure ReflectionProfile where
  presentations : List ReflectivePresentationDecl := []
  rules : List ReflectiveRuleDecl := []
deriving Repr, DecidableEq

namespace ReflectionProfile

/-- The reflection-free profile used by the five-field operational core. -/
def empty : ReflectionProfile := {}

@[simp] theorem empty_presentations : empty.presentations = [] := rfl

@[simp] theorem empty_rules : empty.rules = [] := rfl

end ReflectionProfile

/-- Validate one reflective payload against the declarations of its core. -/
def validate (language : LanguageDef)
    (profile : ReflectionProfile) : List ValidationError :=
  let duplicatePresentations :=
    if (profile.presentations.map (·.name)).Nodup then []
    else [ValidationError.mk language.name
      "duplicate reflective presentation name"]
  let duplicateRules :=
    if (profile.rules.map (·.name)).Nodup then []
    else [ValidationError.mk language.name "duplicate reflective rule name"]
  duplicatePresentations ++ duplicateRules ++
    profile.presentations.flatMap
      (LanguageDef.validateReflectivePresentation language) ++
    profile.rules.flatMap
      (LanguageDef.validateReflectiveRule language profile.presentations)

/-- Whole-profile admission exposes the validation certificate for each
selected reflective presentation. -/
theorem presentation_validate_eq_nil_of_validate_eq_nil
    {language : LanguageDef} {profile : ReflectionProfile}
    (clean : validate language profile = [])
    {presentation : ReflectivePresentationDecl}
    (membership : presentation ∈ profile.presentations) :
    language.validateReflectivePresentation presentation = [] := by
  unfold validate at clean
  simp only [List.append_eq_nil_iff] at clean
  exact (List.flatMap_eq_nil_iff.mp clean.1.2)
    presentation membership

/-- Whole-profile admission includes duplicate freedom for presentation
names.  This belongs to the reflection fibre, not to the five-field core. -/
theorem presentationNames_nodup_of_validate_eq_nil
    {language : LanguageDef} {profile : ReflectionProfile}
    (clean : validate language profile = []) :
    (profile.presentations.map (·.name)).Nodup := by
  unfold validate at clean
  simp only [List.append_eq_nil_iff] at clean
  by_contra duplicate
  simp [duplicate] at clean

/-- Whole-profile admission includes duplicate freedom for rule names. -/
theorem ruleNames_nodup_of_validate_eq_nil
    {language : LanguageDef} {profile : ReflectionProfile}
    (clean : validate language profile = []) :
    (profile.rules.map (·.name)).Nodup := by
  unfold validate at clean
  simp only [List.append_eq_nil_iff] at clean
  by_contra duplicate
  simp [duplicate] at clean

/-- Whole-profile admission exposes the validation certificate for each
selected reflective rule against the profile's own presentations. -/
theorem rule_validate_eq_nil_of_validate_eq_nil
    {language : LanguageDef} {profile : ReflectionProfile}
    (clean : validate language profile = [])
    {rule : ReflectiveRuleDecl} (membership : rule ∈ profile.rules) :
    language.validateReflectiveRule profile.presentations rule = [] := by
  unfold validate at clean
  simp only [List.append_eq_nil_iff] at clean
  exact (List.flatMap_eq_nil_iff.mp clean.2) rule membership

/-- A raw language paired with an explicit reflective interpretation.
The inherited `LanguageDef` projections are ergonomic; `toLanguageDef` is
the exact conservative erasure. -/
structure ReflectiveLanguageDef extends LanguageDef where
  reflection : ReflectionProfile := .empty
deriving Repr

namespace ReflectiveLanguageDef

instance : Coe ReflectiveLanguageDef LanguageDef :=
  ⟨ReflectiveLanguageDef.toLanguageDef⟩

@[simp] theorem erase_name (language : ReflectiveLanguageDef) :
    language.toLanguageDef.name = language.name := rfl

@[simp] theorem erase_types (language : ReflectiveLanguageDef) :
    language.toLanguageDef.types = language.types := rfl

@[simp] theorem erase_terms (language : ReflectiveLanguageDef) :
    language.toLanguageDef.terms = language.terms := rfl

@[simp] theorem erase_equations (language : ReflectiveLanguageDef) :
    language.toLanguageDef.equations = language.equations := rfl

@[simp] theorem erase_rewrites (language : ReflectiveLanguageDef) :
    language.toLanguageDef.rewrites = language.rewrites := rfl

/-- Embed a five-field language with no reflective interpretation. -/
def ofCore (language : LanguageDef) : ReflectiveLanguageDef :=
  { language with reflection := .empty }

@[simp] theorem ofCore_toLanguageDef (language : LanguageDef) :
    (ofCore language).toLanguageDef = language := rfl

@[simp] theorem ofCore_reflection (language : LanguageDef) :
    (ofCore language).reflection = .empty := rfl

/-- Validate the five-field core and its explicitly attached reflection
profile without making the latter a field of `LanguageDef`. -/
def validate (language : ReflectiveLanguageDef) : List ValidationError :=
  language.toLanguageDef.validate ++
    Reflection.validate language.toLanguageDef language.reflection

end ReflectiveLanguageDef

end Mettapedia.OSLF.MeTTaIL.Reflection
