import Mettapedia.OSLF.MeTTaIL.UnaryNumerals

/-!
# Validating rules generated from data

A rewrite or equation written out literally is validated by evaluating
`LanguageDef.validate`.  A rule generated from a table entry mentions
numerals of unknown size, so its validation has to be argued instead.  The
constructor check is the only component that inspects every node of a
pattern; this module restates it as a condition on the pattern's list of
constructor references, which is where the numeral lemmas apply.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Syntax

namespace LanguageDef

/-- A constructor reference is declared exactly once with the referenced
arity. -/
def referenceDeclared (constructors : List GrammarRule)
    (reference : String × Nat) : Bool :=
  match constructors.filter fun declaration => declaration.label == reference.1 with
  | [declaration] => declaration.params.length == reference.2
  | _ => false

/-- The constructor check of a pattern passes exactly when every constructor
reference in it is declared once with the right arity. -/
theorem validatePatternConstructors_eq_nil_iff
    (context : String) (constructors : List GrammarRule) (pattern : Pattern) :
    validatePatternConstructors context constructors pattern = [] ↔
      ∀ reference ∈ pattern.constructorRefs,
        referenceDeclared constructors reference = true := by
  unfold validatePatternConstructors
  rw [List.flatMap_eq_nil_iff]
  constructor
  · intro checked reference membership
    have row := checked reference membership
    unfold referenceDeclared
    obtain ⟨label, arity⟩ := reference
    simp only at row ⊢
    split at row
    · cases row
    · split at row
      · simp_all
      · cases row
    · cases row
  · intro declared reference membership
    have row := declared reference membership
    unfold referenceDeclared at row
    obtain ⟨label, arity⟩ := reference
    simp only at row ⊢
    split
    · simp_all
    · simp_all
    · simp_all

/-- A premise-free rewrite validates when its variable types are declared,
its two sides mention only declared constructors at their declared arities,
and the scope and naming checks on its two sides pass. -/
theorem validateRewrite_eq_nil_of_premiseFree
    (lang : LanguageDef) (rewrite : RewriteRule)
    (premiseFree : rewrite.premises = [])
    (types : ∀ entry ∈ rewrite.typeContext, ∀ typeName ∈ entry.2.baseNames,
      typeName ∈ lang.typeNames)
    (leftDeclared : ∀ reference ∈ rewrite.left.constructorRefs,
      referenceDeclared lang.terms reference = true)
    (rightDeclared : ∀ reference ∈ rewrite.right.constructorRefs,
      referenceDeclared lang.terms reference = true)
    (patterns : ∀ context, validateRulePatterns context
      (lang.terms.map (·.label)) rewrite.typeContext [] rewrite.left rewrite.right = []) :
    validateRewrite lang rewrite = [] := by
  unfold validateRewrite
  simp only [premiseFree, List.flatMap_nil, List.append_nil, List.append_eq_nil_iff,
    List.flatMap_eq_nil_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro entry membership
    apply validateTypeExpr_eq_nil_of_baseNames
    exact types entry membership
  · exact (validatePatternConstructors_eq_nil_iff _ _ _).mpr leftDeclared
  · exact (validatePatternConstructors_eq_nil_iff _ _ _).mpr rightDeclared
  · exact patterns _

/-- A rewrite whose only hypothesis is a reduction between two metavariables
validates under the same conditions on its two sides. -/
theorem validateRewrite_eq_nil_of_variableCongruence
    (lang : LanguageDef) (rewrite : RewriteRule) (source target : String)
    (premises : rewrite.premises = [.congruence (.fvar source) (.fvar target)])
    (types : ∀ entry ∈ rewrite.typeContext, ∀ typeName ∈ entry.2.baseNames,
      typeName ∈ lang.typeNames)
    (leftDeclared : ∀ reference ∈ rewrite.left.constructorRefs,
      referenceDeclared lang.terms reference = true)
    (rightDeclared : ∀ reference ∈ rewrite.right.constructorRefs,
      referenceDeclared lang.terms reference = true)
    (patterns : ∀ context, validateRulePatterns context
      (lang.terms.map (·.label)) rewrite.typeContext
      [.congruence (.fvar source) (.fvar target)] rewrite.left rewrite.right = []) :
    validateRewrite lang rewrite = [] := by
  unfold validateRewrite
  simp only [premises, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    premiseStepTypeExprs, premisePatterns, List.append_eq_nil_iff, List.flatMap_eq_nil_iff]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩
  · intro entry membership
    apply validateTypeExpr_eq_nil_of_baseNames
    exact types entry membership
  · exact (validatePatternConstructors_eq_nil_iff _ _ _).mpr leftDeclared
  · exact (validatePatternConstructors_eq_nil_iff _ _ _).mpr rightDeclared
  · exact (validatePatternConstructors_eq_nil_iff _ _ _).mpr (by
      intro reference membership
      simp [Pattern.constructorRefs] at membership)
  · exact (validatePatternConstructors_eq_nil_iff _ _ _).mpr (by
      intro reference membership
      simp [Pattern.constructorRefs] at membership)
  · exact patterns _

/-- The same criterion for a premise-free equation. -/
theorem validateEquation_eq_nil_of_premiseFree
    (lang : LanguageDef) (equation : Equation)
    (premiseFree : equation.premises = [])
    (types : ∀ entry ∈ equation.typeContext, ∀ typeName ∈ entry.2.baseNames,
      typeName ∈ lang.typeNames)
    (leftDeclared : ∀ reference ∈ equation.left.constructorRefs,
      referenceDeclared lang.terms reference = true)
    (rightDeclared : ∀ reference ∈ equation.right.constructorRefs,
      referenceDeclared lang.terms reference = true)
    (patterns : ∀ context, validateRulePatterns context
      (lang.terms.map (·.label)) equation.typeContext [] equation.left equation.right = []) :
    validateEquation lang equation = [] := by
  unfold validateEquation
  simp only [premiseFree, List.flatMap_nil, List.append_nil, List.append_eq_nil_iff,
    List.flatMap_eq_nil_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro entry membership
    apply validateTypeExpr_eq_nil_of_baseNames
    exact types entry membership
  · exact (validatePatternConstructors_eq_nil_iff _ _ _).mpr leftDeclared
  · exact (validatePatternConstructors_eq_nil_iff _ _ _).mpr rightDeclared
  · exact patterns _

/-- Validation of a rewrite reads only the sorts and constructors of the
language.  Two languages with the same signature validate the same rules. -/
theorem validateRewrite_congr_signature {first second : LanguageDef}
    (types : first.types = second.types) (terms : first.terms = second.terms)
    (rewrite : RewriteRule) :
    validateRewrite first rewrite = validateRewrite second rewrite := by
  unfold validateRewrite typeNames
  rw [types, terms]

/-- Validation of an equation reads only the sorts and constructors of the
language. -/
theorem validateEquation_congr_signature {first second : LanguageDef}
    (types : first.types = second.types) (terms : first.terms = second.terms)
    (equation : Equation) :
    validateEquation first equation = validateEquation second equation := by
  unfold validateEquation typeNames
  rw [types, terms]

end LanguageDef

/-- Evaluate the scope and naming checks of a rule written out literally,
after unfolding the listed definitions.  The lemma set is fixed for every
rule shape, so the unused-argument check is switched off for this one call. -/
macro "rule_patterns" "[" definitions:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    (intro context
     set_option linter.unusedSimpArgs false in
     simp [$definitions,*, LanguageDef.validateRulePatterns, Pattern.isWellScoped,
       Pattern.isWellScopedAt, Pattern.isWellScopedListAt, LanguageDef.patternFvarNames,
       Pattern.freeFvarNames, LanguageDef.patternBinderNames,
       LanguageDef.premiseLocallyScoped, LanguageDef.premiseFvarNames,
       LanguageDef.premisePatterns, LanguageDef.premiseForAllParams,
       LanguageDef.premiseProducedFvarNames]))

end Mettapedia.OSLF.MeTTaIL.Syntax
