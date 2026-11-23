import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension
import Mettapedia.GSLT.LanguageDef.RewriteValidationBatch

/-! Transport structural rewrite validation across signature extensions. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension

private theorem references_declared_of_validate
    (language : LanguageDef) (role : String) (pattern : Pattern)
    (clean : LanguageDef.validatePatternConstructors role language.terms pattern = []) :
    ∀ reference ∈ pattern.constructorRefs, reference ∈ constructorSignatures language := by
  intro reference member
  rcases reference with ⟨label, arity⟩
  unfold LanguageDef.validatePatternConstructors at clean
  have noErrors := List.flatMap_eq_nil_iff.mp clean _ member
  dsimp only at noErrors
  split at noErrors
  · contradiction
  · rename_i declaration filtered
    have matchLabel : declaration ∈ language.terms.filter (·.label == label) := by
      rw [filtered]
      simp
    obtain ⟨declared, labelEqual⟩ := List.mem_filter.mp matchLabel
    have arityEqual : declaration.params.length = arity := by
      by_contra wrongArity
      simp [wrongArity] at noErrors
    exact List.mem_map.mpr ⟨declaration, declared,
      Prod.ext (beq_iff_eq.mp labelEqual) arityEqual⟩
  · contradiction

/-- Successful validation supplies each structural premise of a rewrite certificate. -/
theorem certificate_of_validate {language : LanguageDef} {rewrite : RewriteRule}
    (clean : language.validateRewrite rewrite = []) : Certificate language rewrite := by
  simp only [LanguageDef.validateRewrite, List.append_eq_nil_iff] at clean
  obtain ⟨⟨⟨⟨⟨contextTypes, premiseTypes⟩, leftConstructors⟩, rightConstructors⟩,
    premiseConstructors⟩, patterns⟩ := clean
  simp only [LanguageDef.validateRulePatterns, List.append_eq_nil_iff] at patterns
  obtain ⟨⟨⟨⟨scoping, freeNames⟩, binderNames⟩, contextNames⟩, rhs⟩ := patterns
  refine {
    contextTypes := fun entry member => (LanguageDef.validateTypeExpr_eq_nil_iff _ _ _).mp
      (List.flatMap_eq_nil_iff.mp contextTypes entry member)
    premiseTypes := fun type member => (LanguageDef.validateTypeExpr_eq_nil_iff _ _ _).mp
      (List.flatMap_eq_nil_iff.mp premiseTypes type member)
    leftDeclared := references_declared_of_validate _ _ _ leftConstructors
    rightDeclared := references_declared_of_validate _ _ _ rightConstructors
    premisesDeclared := fun pattern member => references_declared_of_validate _ _ _
      (List.flatMap_eq_nil_iff.mp premiseConstructors pattern member)
    allPatternsScoped := ?_
    fvarsAvoidConstructors := ?_
    bindersAvoidConstructors := ?_
    contextAvoidsConstructors := ?_
    rightBound := ?_
  }
  · split at scoping
    · assumption
    · contradiction
  · intro name member collision
    have issue := List.flatMap_eq_nil_iff.mp freeNames name member
    change name ∈ language.terms.map (·.label) at collision
    simp only [List.contains_iff_mem, collision, if_true, List.cons_ne_nil] at issue
  · intro name member collision
    have issue := List.flatMap_eq_nil_iff.mp binderNames name member
    change name ∈ language.terms.map (·.label) at collision
    simp only [List.contains_iff_mem, collision, if_true, List.cons_ne_nil] at issue
  · intro entry member collision
    have issue := List.filterMap_eq_nil_iff.mp contextNames entry member
    change entry.1 ∈ language.terms.map (·.label) at collision
    simp only [List.contains_iff_mem, collision, if_true, Option.some_ne_none] at issue
  · intro name member
    have fresh : name ∉ constructorLabels language := by
      intro collision
      have memberOfFree : name ∈
          ((LanguageDef.patternFvarNames [] rewrite.left ++
            LanguageDef.patternFvarNames [] rewrite.right ++
            rewrite.premises.flatMap (LanguageDef.premiseFvarNames [])).eraseDups) :=
        List.mem_eraseDups.mpr (List.mem_append_left _
          (List.mem_append_right _ (List.mem_eraseDups.mp member)))
      have issue := List.flatMap_eq_nil_iff.mp freeNames name memberOfFree
      change name ∈ language.terms.map (·.label) at collision
      simp only [List.contains_iff_mem, collision, if_true, List.cons_ne_nil] at issue
    change name ∉ language.terms.map (·.label) at fresh
    by_contra absent
    have noDangling := List.flatMap_eq_nil_iff.mp rhs name member
    simp only [Bool.or_eq_true, List.contains_iff_mem, fresh, absent, or_self, if_false,
      List.cons_ne_nil] at noDangling

/-- Inherited rules retain their validation when the appended constructor
declarations are fresh for the rule. -/
theorem validateRewrite_of_append_signature
    {source target : LanguageDef} {rewrite : RewriteRule}
    {addedTypes : List TypeDecl} {addedTerms : List GrammarRule}
    (clean : source.validateRewrite rewrite = [])
    (typesAppend : target.types = source.types ++ addedTypes)
    (termsAppend : target.terms = source.terms ++ addedTerms)
    (fresh : ∀ name ∈ schemaNames rewrite, name ∉ addedTerms.map (·.label))
    (labelsNodup : (target.terms.map (·.label)).Nodup) :
    target.validateRewrite rewrite = [] := by
  let extension : ExtendsFor source target rewrite := {
    addedTypes := addedTypes.map (·.name)
    addedSignatures := addedTerms.map fun term => (term.label, term.params.length)
    addedLabels := addedTerms.map (·.label)
    typeNames := by simp only [LanguageDef.typeNames, typesAppend, List.map_append]
    signatures := by simp only [constructorSignatures, termsAppend, List.map_append]
    labels := by simp only [constructorLabels, termsAppend, List.map_append]
    avoidsSchema := fresh }
  exact validateRewrite_eq_nil labelsNodup
    (RewriteValidationCertificateExtension.Certificate.extend
      (certificate_of_validate clean) extension)

private def source : LanguageDef :=
  { LanguageDef.empty "variables" with types := ["Atom"] }

private def introduced (name : String) : GrammarRule :=
  { label := name, category := "Atom", params := [], syntaxPattern := [] }

private def identity : RewriteRule :=
  ⟨"identity", [], [], .fvar "x", .fvar "x", none⟩

private def extended (name : String) : LanguageDef :=
  { source with terms := source.terms ++ [introduced name] }

private theorem identity_valid : source.validateRewrite identity = [] :=
  validateRewrite_eq_nil_of_check (by simp [source, LanguageDef.empty]) (by cbv)

example : (extended "fresh").validateRewrite identity = [] := by
  apply validateRewrite_of_append_signature (source := source)
    (addedTypes := []) (addedTerms := [introduced "fresh"]) identity_valid rfl rfl
  · intro name member
    have equal : name = "x" := by
      simpa [schemaNames, identity, LanguageDef.patternFvarNames,
        LanguageDef.patternBinderNames, Pattern.freeFvarNames] using member
    subst name
    decide
  · decide

example : (extended "x").validateRewrite identity ≠ [] := by
  intro clean
  have certificate := certificate_of_validate clean
  exact certificate.fvarsAvoidConstructors "x" (by cbv; exact List.Mem.head _)
    (by exact List.Mem.head _)

end Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
