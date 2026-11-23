import Mettapedia.OSLF.MeTTaIL.PlainRuleValidation
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

/-! Structural validation of an ordered list of authored rewrites. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- One check of the authored row list supplies the ordinary validation
result at every member, with the signature fixed throughout. -/
theorem validateRewrite_eq_nil_of_all
    {language : LanguageDef} {rewrites : List RewriteRule}
    (labelsNodup : (language.terms.map (·.label)).Nodup)
    (checked : rewrites.all (check language) = true) :
    ∀ rewrite ∈ rewrites, language.validateRewrite rewrite = [] :=
  fun rewrite member =>
    validateRewrite_eq_nil_of_check labelsNodup (List.all_eq_true.mp checked rewrite member)

theorem validate_eq_nil_iff_signature_and_rewrites (lang : LanguageDef) :
    lang.validate = [] ↔
      ({ lang with rewrites := [] } : LanguageDef).validate = [] ∧
      (lang.rewrites.map (·.name)).Nodup ∧
      ∀ rewrite ∈ lang.rewrites, lang.validateRewrite rewrite = [] := by
  let signature : LanguageDef := { lang with rewrites := [] }
  constructor
  · intro valid
    refine ⟨?_, LanguageDef.rewriteNames_nodup_of_validate_eq_nil lang valid,
      LanguageDef.validateRewrite_eq_nil_of_validate_eq_nil lang valid⟩
    exact LanguageDef.validate_eq_nil_of_rows signature
      (LanguageDef.typeNames_nodup_of_validate_eq_nil lang valid)
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil lang valid)
      (LanguageDef.equationNames_nodup_of_validate_eq_nil lang valid)
      List.nodup_nil
      (LanguageDef.validateTerm_eq_nil_of_validate_eq_nil lang valid)
      (LanguageDef.validateEquation_eq_nil_of_validate_eq_nil lang valid)
      (by simp [signature])
  · rintro ⟨signatureValid, names, rewrites⟩
    exact LanguageDef.validate_eq_nil_of_rows lang
      (LanguageDef.typeNames_nodup_of_validate_eq_nil signature signatureValid)
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil signature signatureValid)
      (LanguageDef.equationNames_nodup_of_validate_eq_nil signature signatureValid) names
      (LanguageDef.validateTerm_eq_nil_of_validate_eq_nil signature signatureValid)
      (LanguageDef.validateEquation_eq_nil_of_validate_eq_nil signature signatureValid)
      rewrites

/-- Check a constructor signature and its plain equation rows once. -/
theorem validate_signature_of_plain_equations {lang : LanguageDef}
    (types : lang.typeNames.Nodup)
    (constructors : (lang.terms.map (·.label)).Nodup)
    (equations : (lang.equations.map (·.name)).Nodup)
    (categories : ∀ term ∈ lang.terms, term.category ∈ lang.typeNames)
    (parameters : ∀ term ∈ lang.terms, ∀ param ∈ term.params,
      ∀ typeName ∈ (TermParam.typeExpr param).baseNames, typeName ∈ lang.typeNames)
    (syntaxRows : ∀ term ∈ lang.terms, term.syntaxPattern = [] ∨
      term.syntaxPattern = term.params.map (fun param => SyntaxItem.nonTerminal (TermParam.bodyName param)))
    (equationRows : lang.equations.all (LanguageDef.plainEquationOk lang) = true) :
    ({ lang with rewrites := [] } : LanguageDef).validate = [] := by
  let signature : LanguageDef := { lang with rewrites := [] }
  apply LanguageDef.validate_eq_nil_of_constructorEquationsAndRewrites
    signature types constructors equations List.nodup_nil categories parameters syntaxRows
  · intro equation member
    exact LanguageDef.validateEquation_eq_nil_of_plainEquationOk
      (List.all_eq_true.mp equationRows equation member)
  · simp [signature]

theorem validate_eq_nil_of_signature_and_checks {lang : LanguageDef}
    (signatureValid : ({ lang with rewrites := [] } : LanguageDef).validate = [])
    (names : (lang.rewrites.map (·.name)).Nodup)
    (rows : ∀ rewrite ∈ lang.rewrites, check lang rewrite = true) :
    lang.validate = [] := by
  refine (validate_eq_nil_iff_signature_and_rewrites lang).mpr ⟨signatureValid, names, ?_⟩
  exact fun rewrite member =>
    validateRewrite_eq_nil_of_check
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil { lang with rewrites := [] } signatureValid)
      (rows rewrite member)

/-- Successful signature validation transports across changes to the
presentation label and rewrite list. The structural data are fixed. -/
theorem validate_signature_of_same_data {left right : LanguageDef}
    (types : left.typeNames = right.typeNames)
    (terms : left.terms = right.terms)
    (equations : left.equations = right.equations)
    (accepted : ({ left with rewrites := [] } : LanguageDef).validate = []) :
    ({ right with rewrites := [] } : LanguageDef).validate = [] := by
  let origin : LanguageDef := { left with rewrites := [] }
  let target : LanguageDef := { right with rewrites := [] }
  apply LanguageDef.validate_eq_nil_of_rows target
  · exact types ▸ LanguageDef.typeNames_nodup_of_validate_eq_nil origin accepted
  · exact terms ▸ LanguageDef.constructorLabels_nodup_of_validate_eq_nil origin accepted
  · exact equations ▸ LanguageDef.equationNames_nodup_of_validate_eq_nil origin accepted
  · exact List.nodup_nil
  · intro term member
    have same : origin.validateTerm term = target.validateTerm term := by
      have h : origin.typeNames = target.typeNames := types
      simp only [LanguageDef.validateTerm, h]
    rw [← same]
    exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil origin accepted term
      (terms.symm ▸ member)
  · intro equation member
    have same : origin.validateEquation equation = target.validateEquation equation := by
      have h : origin.typeNames = target.typeNames := types
      have hterms : origin.terms = target.terms := terms
      simp only [LanguageDef.validateEquation, h, hterms]
    rw [← same]
    exact LanguageDef.validateEquation_eq_nil_of_validate_eq_nil origin accepted equation
      (equations.symm ▸ member)
  · simp [target]

private def identityRow : RewriteRule :=
  ⟨"identity", [], [], .fvar "x", .fvar "x", none⟩

private def unboundResult : RewriteRule :=
  { identityRow with right := .fvar "y" }

example : [identityRow, identityRow].all (check (LanguageDef.empty "variables")) = true := by
  cbv

example : [identityRow, unboundResult].all (check (LanguageDef.empty "variables")) = false := by
  cbv

example :
    [identityRow, { identityRow with right := .lambda none (.bvar 0) }].all
      (check (LanguageDef.empty "binder")) = true := by
  cbv

example :
    [identityRow, { identityRow with right := .bvar 0 }].all
      (check (LanguageDef.empty "binder")) = false := by
  cbv

private def identityLanguage : LanguageDef :=
  { LanguageDef.empty "variables" with rewrites := [identityRow] }

example : identityLanguage.validate = [] := by
  apply validate_eq_nil_of_signature_and_checks
  · cbv
  · decide
  · intro rewrite member
    have same : rewrite = identityRow := List.mem_singleton.mp member
    subst rewrite
    cbv

private def repeatedIdentityLanguage : LanguageDef :=
  { identityLanguage with rewrites := [identityRow, identityRow] }

example : repeatedIdentityLanguage.validate ≠ [] := by
  intro accepted
  have unique := ((validate_eq_nil_iff_signature_and_rewrites _).mp accepted).2.1
  simp [repeatedIdentityLanguage] at unique

end Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
