import Mettapedia.GSLT.LanguageDef.Extension
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.OSLF.MeTTaIL.ReflectionProfile

/-!
# Reflective interpretation as a coGSLT-authored extension

Reflection declarations select an interpretation of already-authored terms,
equations, and rewrites.  They do not belong to the five-field language
definition.  This module packages them as a separately validated fibre and
provides a compatibility-shaped total record for semantic developments that
need to carry a language and its reflection profile together.
-/

namespace Mettapedia.GSLT.LanguageDef.ReflectionExtension

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection

/-- A structural declaration in the authored reflection language. -/
inductive ReflectionDeclaration where
  | presentation (declaration : ReflectivePresentationDecl)
  | rule (declaration : ReflectiveRuleDecl)
deriving Repr, DecidableEq

abbrev ReflectionSyntax := ReflectionDeclaration

/-- Reflection declarations use their structural form directly as authored
syntax; the codec records that this identification is exact. -/
def reflectionCodec :
    ExactDeclarationCodec ReflectionSyntax ReflectionDeclaration where
  encode := id
  decode := id
  decode_encode := fun _ => rfl
  encode_decode := fun _ => rfl

def profileDeclarations
    (profile : ReflectionProfile) : List ReflectionDeclaration :=
  profile.presentations.map ReflectionDeclaration.presentation ++
    profile.rules.map ReflectionDeclaration.rule

def profileOfDeclarations
    (declarations : List ReflectionDeclaration) : ReflectionProfile :=
  { presentations := declarations.filterMap fun
      | .presentation declaration => some declaration
      | .rule _ => none
    rules := declarations.filterMap fun
      | .presentation _ => none
      | .rule declaration => some declaration }

@[simp] theorem profileOfDeclarations_declarations
    (profile : ReflectionProfile) :
    profileOfDeclarations (profileDeclarations profile) = profile := by
  cases profile with
  | mk presentations rules =>
      simp [profileDeclarations, profileOfDeclarations]

/-- A single, human-readable validation report for the reflection fibre. -/
def validate (language : LanguageDef)
    (profile : ReflectionProfile) : List ValidationError :=
  Mettapedia.OSLF.MeTTaIL.Reflection.validate language profile

abbrev AdmittedProfile (language : LanguageDef) :=
  { profile : ReflectionProfile // validate language profile = [] }

/-- Every five-field language admits the reflection-free profile. -/
def emptyAdmitted (language : LanguageDef) : AdmittedProfile language :=
  ⟨.empty, by
    simp [validate, Mettapedia.OSLF.MeTTaIL.Reflection.validate,
      ReflectionProfile.empty]⟩

/-- The law-bearing authored GSLT for reflection declaration sequences. -/
def reflectionAuthoringGSLT :
    DeclarationAuthoringGSLT ReflectionDeclaration :=
  reflectionCodec.compositionalElaboration

def reflectionDocumentGSLT : GSLT :=
  reflectionAuthoringGSLT.authoring.theory

private def elaborateProfile? (language : LanguageDef)
    (source : DeclarationDocument ReflectionSyntax) :
    Option (AdmittedProfile language) :=
  let profile := profileOfDeclarations source.values
  if admitted : validate language profile = [] then
    some ⟨profile, admitted⟩
  else
    none

private def quoteProfile (language : LanguageDef)
    (profile : AdmittedProfile language) :
    DeclarationDocument ReflectionSyntax :=
  .bundle ((profileDeclarations profile.1).map
    DeclarationDocument.declaration)

def layer : CoGSLTLayer LanguageDef where
  Fiber := AdmittedProfile
  sourceGSLT := fun _ => reflectionDocumentGSLT
  elaborate := elaborateProfile?
  quote := quoteProfile
  elaborate_quote := by
    intro language profile
    simp [quoteProfile, elaborateProfile?, profile.2]
  elaborate_equation := by
    intro language source target equal
    change source.values = target.values at equal
    unfold elaborateProfile?
    rw [equal]
  elaborate_rewrite := by
    intro language source target impossible
    exact False.elim impossible

@[simp] theorem erase_attach (language : LanguageDef)
    (profile : AdmittedProfile language) :
    layer.erase (layer.attach language profile) = language :=
  rfl

/-- A validated five-field language together with an admitted point of its
reflection fibre.  Validation is stored componentwise, so this object is
literally a dependent extension rather than a second validation authority. -/
structure ValidatedReflectiveLanguageDef where
  core : ValidatedLanguageDef
  reflection : AdmittedProfile core.language

namespace ValidatedReflectiveLanguageDef

/-- The ergonomic raw pair reconstructed from the dependent fibre. -/
def language (presentation : ValidatedReflectiveLanguageDef) :
    ReflectiveLanguageDef :=
  { presentation.core.language with
    reflection := presentation.reflection.1 }

instance : Coe ValidatedReflectiveLanguageDef ReflectiveLanguageDef :=
  ⟨language⟩

@[simp] theorem language_toLanguageDef
    (presentation : ValidatedReflectiveLanguageDef) :
    presentation.language.toLanguageDef = presentation.core.language :=
  rfl

@[simp] theorem language_reflection
    (presentation : ValidatedReflectiveLanguageDef) :
    presentation.language.reflection = presentation.reflection.1 :=
  rfl

/-- The combined validator is derived from the two component certificates. -/
theorem valid (presentation : ValidatedReflectiveLanguageDef) :
    presentation.language.validate = [] := by
  apply List.append_eq_nil_iff.mpr
  exact ⟨presentation.core.valid, presentation.reflection.2⟩

/-- Split a validated raw pair into the exact core and its admitted fibre. -/
def ofLanguage (language : ReflectiveLanguageDef)
    (valid : language.validate = []) : ValidatedReflectiveLanguageDef := by
  change language.toLanguageDef.validate ++
      Mettapedia.OSLF.MeTTaIL.Reflection.validate
        language.toLanguageDef language.reflection = [] at valid
  have parts := List.append_eq_nil_iff.mp valid
  exact
    { core := ⟨language.toLanguageDef, parts.1⟩
      reflection := ⟨language.reflection, parts.2⟩ }

@[simp] theorem ofLanguage_language (language : ReflectiveLanguageDef)
    (valid : language.validate = []) :
    (ofLanguage language valid).language = language := by
  cases language
  rfl

/-- Reconstructing and re-splitting a validated fibre changes no data. -/
@[simp] theorem ofLanguage_roundtrip
    (presentation : ValidatedReflectiveLanguageDef) :
    ofLanguage presentation.language presentation.valid = presentation := by
  cases presentation with
  | mk core reflection =>
      cases core
      cases reflection
      rfl

def admittedReflection (presentation : ValidatedReflectiveLanguageDef) :
    AdmittedProfile presentation.language.toLanguageDef :=
  presentation.reflection

end ValidatedReflectiveLanguageDef

/-- Rho's reflective declarations are attached beside its five-field core. -/
def rhoReflectionProfile : ReflectionProfile :=
  { presentations :=
      [rhoReflectivePresentation.toReflectivePresentationDecl]
    rules := [rhoReflectiveRule] }

def rhoCalcReflective : ReflectiveLanguageDef :=
  { rhoCalc with
    reflection := rhoReflectionProfile }

private def rhoUnitTerm : GrammarRule :=
  rhoCalc.terms.get ⟨0, by decide⟩

private def rhoDropTerm : GrammarRule :=
  rhoCalc.terms.get ⟨1, by decide⟩

private def rhoQuoteTerm : GrammarRule :=
  rhoCalc.terms.get ⟨2, by decide⟩

private def rhoQuoteDropEquation : Equation :=
  rhoCalc.equations.get ⟨0, by decide⟩

private theorem rhoReflectivePresentation_valid :
    LanguageDef.validateReflectivePresentation rhoCalc
      rhoReflectivePresentation.toReflectivePresentationDecl = [] := by
  apply LanguageDef.validateReflectivePresentation_eq_nil_of_unique
    rhoCalc rhoReflectivePresentation.toReflectivePresentationDecl
    rhoQuoteTerm rhoDropTerm rhoUnitTerm rhoQuoteDropEquation
    "p" "n" "N"
  all_goals
    simp [rhoCalc, rhoQuoteTerm, rhoDropTerm, rhoUnitTerm,
      rhoQuoteDropEquation, rhoReflectivePresentation,
      LanguageDef.typeNames, TypeDecl.plain, TypeExpr.proc, TypeExpr.name,
      TypeExpr.baseType]

private theorem rhoReflectiveRule_valid :
    LanguageDef.validateReflectiveRule rhoCalc
      [rhoReflectivePresentation.toReflectivePresentationDecl]
      rhoReflectiveRule = [] := by
  exact (show LanguageDef.ReflectiveRuleWitness rhoCalc
      [rhoReflectivePresentation.toReflectivePresentationDecl]
      rhoReflectiveRule from
    { rewrite := rhoCommRewrite
      matchingPresentation :=
        rhoReflectivePresentation.toReflectivePresentationDecl
      substitutionPresentation :=
        rhoReflectivePresentation.toReflectivePresentationDecl
      rewriteUnique := by
        simp [rhoCalc, rhoCommRewrite, rhoParCongRewrite,
          rhoReflectiveRule]
      matchingUnique := by simp [rhoReflectivePresentation, rhoReflectiveRule]
      substitutionUnique := by
        simp [rhoReflectivePresentation, rhoReflectiveRule] }).validate

theorem rhoCalcReflective_validate_eq_nil :
    rhoCalcReflective.validate = [] := by
  simp [ReflectiveLanguageDef.validate,
    Mettapedia.OSLF.MeTTaIL.Reflection.validate,
    rhoCalcReflective, rhoReflectionProfile, rhoCalc_validate_eq_nil,
    rhoReflectivePresentation_valid, rhoReflectiveRule_valid]

def rhoCalcValidatedReflective : ValidatedReflectiveLanguageDef :=
  .ofLanguage rhoCalcReflective rhoCalcReflective_validate_eq_nil

/-- Negative: a rule-local selector cannot name an absent authored rewrite. -/
theorem rho_missing_rewrite_rejected :
    validate rhoCalc
      { rhoReflectionProfile with
        rules := [{ rhoReflectiveRule with rewriteRule := "MissingComm" }] } ≠ [] := by
  intro clean
  have ruleClean :
      LanguageDef.validateReflectiveRule rhoCalc
        [rhoReflectivePresentation.toReflectivePresentationDecl]
        { rhoReflectiveRule with rewriteRule := "MissingComm" } = [] := by
    have pieces := List.append_eq_nil_iff.mp clean
    have ruleErrors := pieces.2
    have pieces' := List.flatMap_eq_nil_iff.mp ruleErrors
    exact pieces'
      { rhoReflectiveRule with rewriteRule := "MissingComm" } (by simp)
  exact (LanguageDef.validateReflectiveRule_ne_nil_of_missing_rewrite
    rhoCalc [rhoReflectivePresentation.toReflectivePresentationDecl]
    { rhoReflectiveRule with rewriteRule := "MissingComm" }
    (by simp [rhoCalc, rhoCommRewrite, rhoParCongRewrite])) ruleClean

private def markedLanguage : LanguageDef :=
  { LanguageDef.empty "marked" with
    types := [TypeDecl.plain "P", TypeDecl.plain "N"]
    terms :=
      [{ label := "Q", category := "N",
         params := [.simple "p" (.base "P")], syntaxPattern := [] },
       { label := "D", category := "P",
         params := [.simple "n" (.base "N")], syntaxPattern := [] },
       { label := "Z", category := "P", params := [], syntaxPattern := [] }]
    equations :=
      [{ name := "QD", typeContext := [("n", .base "N")], premises := [],
         left := .apply "Q" [.apply "D" [.fvar "n"]], right := .fvar "n" }] }

private def markedPresentation : ReflectivePresentationDecl :=
  { name := "marked-reflection"
    processSort := "P"
    nameSort := "N"
    quoteConstructor := "Q"
    dropConstructor := "D"
    parallelCollection := .hashBag
    parallelUnitConstructor := "Z"
    quoteDropEquation := "QD" }

private def markedQuoteTerm : GrammarRule :=
  markedLanguage.terms.get ⟨0, by decide⟩

private def markedDropTerm : GrammarRule :=
  markedLanguage.terms.get ⟨1, by decide⟩

private def markedUnitTerm : GrammarRule :=
  markedLanguage.terms.get ⟨2, by decide⟩

private def markedEquation : Equation :=
  markedLanguage.equations.get ⟨0, by decide⟩

private theorem markedPresentation_valid :
    LanguageDef.validateReflectivePresentation markedLanguage
      markedPresentation = [] := by
  apply LanguageDef.validateReflectivePresentation_eq_nil_of_unique
    markedLanguage markedPresentation markedQuoteTerm markedDropTerm
    markedUnitTerm markedEquation "p" "n" "n"
  all_goals
    simp [markedLanguage, markedPresentation, markedQuoteTerm,
      markedDropTerm, markedUnitTerm, markedEquation,
      LanguageDef.typeNames, TypeDecl.plain]

private def markedProfile : AdmittedProfile markedLanguage :=
  ⟨{ presentations := [markedPresentation] }, by
    simp [ReflectionExtension.validate,
      Mettapedia.OSLF.MeTTaIL.Reflection.validate,
      markedPresentation_valid]⟩

def reflectionNonTrivialFiber :
    NonTrivialFiber layer.erase (fun attached => attached.2.1) where
  left := layer.attach markedLanguage
    ⟨{}, by simp [ReflectionExtension.validate,
      Mettapedia.OSLF.MeTTaIL.Reflection.validate]⟩
  right := layer.attach markedLanguage markedProfile
  sameShadow := rfl
  differentValue := by
    change ({} : ReflectionProfile) ≠ { presentations := [markedPresentation] }
    intro equal
    have := congrArg ReflectionProfile.presentations equal
    simp at this

theorem reflection_not_determined_by_language :
    ¬ Factors layer.erase (fun attached => attached.2.1) :=
  reflectionNonTrivialFiber.not_factors

end Mettapedia.GSLT.LanguageDef.ReflectionExtension
