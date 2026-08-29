import Mettapedia.GSLT.LanguageDef.CostInteractionClosure

/-!
# Structural certificates for authored rewrite validation

`LanguageDef.validateRewrite` is the semantic authority.  This module exposes
a proof-oriented certificate for the same checks: type references,
constructor signatures, scoping, collision freedom, and output binding.  The
certificate's soundness theorem concludes the actual validator result; it is
not a parallel acceptance criterion.

The executable Boolean front end is useful for large authored presentations
because each rewrite can be certified independently.  Unchanged rows can then
reuse their theorem without normalizing the whole language validator again.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

open Mettapedia.OSLF.MeTTaIL.Syntax

def constructorSignatures (language : LanguageDef) : List (String × Nat) :=
  language.terms.map fun declaration =>
    (declaration.label, declaration.params.length)

def constructorLabels (language : LanguageDef) : List String :=
  language.terms.map (·.label)

theorem validatePatternConstructors_eq_nil_of_signatures
    (language : LanguageDef)
    (labelsNodup : (language.terms.map (·.label)).Nodup)
    (context : String) (pattern : Pattern)
    (declared : ∀ reference ∈ pattern.constructorRefs,
      reference ∈ constructorSignatures language) :
    LanguageDef.validatePatternConstructors context language.terms pattern =
      [] := by
  unfold LanguageDef.validatePatternConstructors
  apply List.flatMap_eq_nil_iff.mpr
  intro reference referenceMembership
  have signatureMembership :
      reference ∈ language.terms.map (fun declaration =>
        (declaration.label, declaration.params.length)) := by
    simpa only [constructorSignatures] using
      declared reference referenceMembership
  obtain ⟨declaration, declarationMembership, declarationSignature⟩ :=
    List.mem_map.mp signatureMembership
  rcases reference with ⟨label, arity⟩
  have labelEquality : declaration.label = label :=
    congrArg Prod.fst declarationSignature
  have arityEquality : declaration.params.length = arity :=
    congrArg Prod.snd declarationSignature
  subst label
  dsimp only
  rw [LanguageDef.filter_terms_by_label_eq_singleton language.terms
    declaration labelsNodup declarationMembership]
  simp [arityEquality]

structure Certificate (language : LanguageDef)
    (rewrite : RewriteRule) : Prop where
  contextTypes : ∀ entry ∈ rewrite.typeContext,
    ∀ name ∈ entry.2.baseNames, name ∈ language.typeNames
  leftDeclared : ∀ reference ∈ rewrite.left.constructorRefs,
    reference ∈ constructorSignatures language
  rightDeclared : ∀ reference ∈ rewrite.right.constructorRefs,
    reference ∈ constructorSignatures language
  premisesDeclared : ∀ pattern ∈
      rewrite.premises.flatMap LanguageDef.premisePatterns,
    ∀ reference ∈ pattern.constructorRefs,
      reference ∈ constructorSignatures language
  allPatternsScoped :
    ([rewrite.left, rewrite.right] ++
      rewrite.premises.flatMap LanguageDef.premisePatterns).all
        Pattern.isWellScoped = true
  fvarsAvoidConstructors : ∀ name ∈
      ((LanguageDef.patternFvarNames [] rewrite.left ++
        LanguageDef.patternFvarNames [] rewrite.right ++
        rewrite.premises.flatMap
          (LanguageDef.premiseFvarNames [])).eraseDups),
    name ∉ constructorLabels language
  bindersAvoidConstructors : ∀ name ∈
      ((LanguageDef.patternBinderNames rewrite.left ++
        LanguageDef.patternBinderNames rewrite.right ++
        (rewrite.premises.flatMap LanguageDef.premisePatterns).flatMap
          LanguageDef.patternBinderNames ++
        rewrite.premises.flatMap
          LanguageDef.premiseForAllParams).eraseDups),
    name ∉ constructorLabels language
  contextAvoidsConstructors : ∀ entry ∈ rewrite.typeContext,
    entry.1 ∉ constructorLabels language
  rightBound : ∀ name ∈
      (LanguageDef.patternFvarNames [] rewrite.right).eraseDups,
    name ∈ LanguageDef.patternFvarNames [] rewrite.left ++
      rewrite.premises.flatMap
        (LanguageDef.premiseProducedFvarNames [])

theorem Certificate.patternsClean
    {language : LanguageDef} {rewrite : RewriteRule}
    (certificate : Certificate language rewrite) :
    LanguageDef.validateRulePatterns s!"rewrite {rewrite.name}"
      (constructorLabels language) rewrite.typeContext rewrite.premises
      rewrite.left rewrite.right = [] := by
  unfold LanguageDef.validateRulePatterns
  simp only [certificate.allPatternsScoped, if_true,
    List.append_eq_nil_iff, true_and]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · apply List.flatMap_eq_nil_iff.mpr
    intro name membership
    simp [certificate.fvarsAvoidConstructors name membership]
  · apply List.flatMap_eq_nil_iff.mpr
    intro name membership
    simp [certificate.bindersAvoidConstructors name membership]
  · apply List.filterMap_eq_nil_iff.mpr
    intro entry membership
    simp [certificate.contextAvoidsConstructors entry membership]
  · apply List.flatMap_eq_nil_iff.mpr
    intro name membership
    have bound := certificate.rightBound name membership
    simp only [List.mem_append] at bound
    rcases bound with leftBound | premiseBound
    · unfold LanguageDef.patternFvarNames at leftBound
      simp only [List.mem_filter] at leftBound
      simp [leftBound.1]
    · simp only [List.mem_flatMap] at premiseBound
      obtain ⟨premise, premiseMembership, nameMembership⟩ := premiseBound
      simp
      intro _ premiseAbsent
      exact (premiseAbsent premise premiseMembership nameMembership).elim

theorem validateRewrite_eq_nil
    {language : LanguageDef} {rewrite : RewriteRule}
    (labelsNodup : (language.terms.map (·.label)).Nodup)
    (certificate : Certificate language rewrite) :
    language.validateRewrite rewrite = [] := by
  unfold LanguageDef.validateRewrite
  simp only [List.append_eq_nil_iff]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · apply List.flatMap_eq_nil_iff.mpr
    intro entry entryMembership
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    exact certificate.contextTypes entry entryMembership
  · exact validatePatternConstructors_eq_nil_of_signatures language
      labelsNodup _ rewrite.left certificate.leftDeclared
  · exact validatePatternConstructors_eq_nil_of_signatures language
      labelsNodup _ rewrite.right certificate.rightDeclared
  · apply List.flatMap_eq_nil_iff.mpr
    intro pattern patternMembership
    exact validatePatternConstructors_eq_nil_of_signatures language
      labelsNodup _ pattern
      (certificate.premisesDeclared pattern patternMembership)
  · change LanguageDef.validateRulePatterns _
      (language.terms.map fun declaration => declaration.label) _ _ _ _ = []
    simpa only [constructorLabels] using certificate.patternsClean

def contextTypesCheck (language : LanguageDef)
    (rewrite : RewriteRule) : Bool :=
  rewrite.typeContext.all fun entry =>
    entry.2.baseNames.all fun name => decide (name ∈ language.typeNames)

def patternDeclaredCheck (language : LanguageDef)
    (pattern : Pattern) : Bool :=
  pattern.constructorRefs.all fun reference =>
    decide (reference ∈ constructorSignatures language)

def premisesDeclaredCheck (language : LanguageDef)
    (rewrite : RewriteRule) : Bool :=
  (rewrite.premises.flatMap LanguageDef.premisePatterns).all
    (patternDeclaredCheck language)

def allPatternsScopedCheck (rewrite : RewriteRule) : Bool :=
  ([rewrite.left, rewrite.right] ++
    rewrite.premises.flatMap LanguageDef.premisePatterns).all
      Pattern.isWellScoped

def fvarsAvoidConstructorsCheck (language : LanguageDef)
    (rewrite : RewriteRule) : Bool :=
  ((LanguageDef.patternFvarNames [] rewrite.left ++
    LanguageDef.patternFvarNames [] rewrite.right ++
    rewrite.premises.flatMap
      (LanguageDef.premiseFvarNames [])).eraseDups).all fun name =>
    decide (name ∉ constructorLabels language)

def bindersAvoidConstructorsCheck (language : LanguageDef)
    (rewrite : RewriteRule) : Bool :=
  ((LanguageDef.patternBinderNames rewrite.left ++
    LanguageDef.patternBinderNames rewrite.right ++
    (rewrite.premises.flatMap LanguageDef.premisePatterns).flatMap
      LanguageDef.patternBinderNames ++
    rewrite.premises.flatMap
      LanguageDef.premiseForAllParams).eraseDups).all fun name =>
    decide (name ∉ constructorLabels language)

def contextAvoidsConstructorsCheck (language : LanguageDef)
    (rewrite : RewriteRule) : Bool :=
  rewrite.typeContext.all fun entry =>
    decide (entry.1 ∉ constructorLabels language)

def rightBoundCheck (rewrite : RewriteRule) : Bool :=
  let supplied := LanguageDef.patternFvarNames [] rewrite.left ++
    rewrite.premises.flatMap (LanguageDef.premiseProducedFvarNames [])
  (LanguageDef.patternFvarNames [] rewrite.right).eraseDups.all fun name =>
    decide (name ∈ supplied)

def check (language : LanguageDef) (rewrite : RewriteRule) : Bool :=
  contextTypesCheck language rewrite &&
    (patternDeclaredCheck language rewrite.left &&
      (patternDeclaredCheck language rewrite.right &&
        (premisesDeclaredCheck language rewrite &&
          (allPatternsScopedCheck rewrite &&
            (fvarsAvoidConstructorsCheck language rewrite &&
              (bindersAvoidConstructorsCheck language rewrite &&
                (contextAvoidsConstructorsCheck language rewrite &&
                  rightBoundCheck rewrite)))))))

theorem certificate_of_check
    {language : LanguageDef} {rewrite : RewriteRule}
    (checked : check language rewrite = true) :
    Certificate language rewrite := by
  simp only [check, Bool.and_eq_true] at checked
  rcases checked with
    ⟨contextChecked, leftChecked, rightChecked, premisesChecked,
      scopedChecked, fvarsChecked, bindersChecked, contextNamesChecked,
      rightBoundedChecked⟩
  refine {
    contextTypes := ?_
    leftDeclared := ?_
    rightDeclared := ?_
    premisesDeclared := ?_
    allPatternsScoped := scopedChecked
    fvarsAvoidConstructors := ?_
    bindersAvoidConstructors := ?_
    contextAvoidsConstructors := ?_
    rightBound := ?_ }
  · intro entry entryMembership name nameMembership
    exact decide_eq_true_eq.mp (List.all_eq_true.mp
      (List.all_eq_true.mp contextChecked entry entryMembership)
      name nameMembership)
  · intro reference referenceMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp leftChecked reference referenceMembership)
  · intro reference referenceMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp rightChecked reference referenceMembership)
  · intro pattern patternMembership reference referenceMembership
    exact decide_eq_true_eq.mp (List.all_eq_true.mp
      (List.all_eq_true.mp premisesChecked pattern patternMembership)
      reference referenceMembership)
  · intro name nameMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp fvarsChecked name nameMembership)
  · intro name nameMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp bindersChecked name nameMembership)
  · intro entry entryMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp contextNamesChecked entry entryMembership)
  · intro name nameMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp rightBoundedChecked name nameMembership)

theorem validateRewrite_eq_nil_of_check
    {language : LanguageDef} {rewrite : RewriteRule}
    (labelsNodup : (language.terms.map (·.label)).Nodup)
    (checked : check language rewrite = true) :
    language.validateRewrite rewrite = [] :=
  validateRewrite_eq_nil labelsNodup (certificate_of_check checked)

end Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
