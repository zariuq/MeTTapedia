import Mettapedia.OSLF.MeTTaIL.PlainRuleValidation

/-! Successful source validation forbids a premise-free rewrite from
inventing output captures. Constructor-label collisions and dangling
variables are read from the original validator's distinct error lists.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef

theorem validated_premise_free_bound (language : LanguageDef) (rule : RewriteRule)
    (valid : language.validate = []) (member : rule ∈ language.rewrites) (premiseFree : rule.premises = []) :
    ∀ name ∈ rule.right.freeFvarNames, name ∈ rule.left.freeFvarNames := by
  have rowChecked := validateRewrite_eq_nil_of_validate_eq_nil language valid rule member
  have patterns : validateRulePatterns s!"rewrite {rule.name}" (language.terms.map GrammarRule.label)
      rule.typeContext rule.premises rule.left rule.right = [] := by
    unfold validateRewrite at rowChecked
    simp only [List.append_eq_nil_iff] at rowChecked
    exact rowChecked.2
  rw [premiseFree] at patterns
  unfold validateRulePatterns at patterns
  simp only [List.flatMap_nil, List.append_nil, List.append_eq_nil_iff,
    patternFvarNames_nil, Pattern.schemaVariables_eq_freeFvarNames] at patterns
  intro name present
  have listed : name ∈ (rule.left.freeFvarNames ++ rule.right.freeFvarNames).eraseDups :=
    List.mem_eraseDups.mpr (List.mem_append_right _ present)
  have collision := (List.flatMap_eq_nil_iff.mp patterns.1.1.1.2) name listed
  have noConstructor : (language.terms.map GrammarRule.label).contains name = false := by
    cases found : (language.terms.map GrammarRule.label).contains name with
    | false => rfl
    | true => simp only [found, if_true, List.cons_ne_nil] at collision
  have outputListed := List.mem_eraseDups.mpr present
  have supplied := (List.flatMap_eq_nil_iff.mp patterns.2) name outputListed
  cases found : rule.left.freeFvarNames.contains name with
  | false => simp only [found, noConstructor, Bool.or_self, Bool.false_eq_true, if_false, List.cons_ne_nil] at supplied
  | true => exact List.contains_iff_mem.mp found

#print axioms validated_premise_free_bound

end Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef
