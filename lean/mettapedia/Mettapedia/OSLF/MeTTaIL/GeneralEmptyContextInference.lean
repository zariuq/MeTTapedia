import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference

/-! A nonempty capture schema with no authored capture context uses the
existing grammar-inference branch. This theorem exposes that branch without
evaluating unrelated root-admission tests.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference

open Syntax

theorem compile_empty_context (language : LanguageDef) (rule : RewriteRule)
    (omitted : rule.bindings = none) (empty : rule.typeContext = [])
    (captures : rule.left.freeFvarNames ≠ []) (result : GeneralRuleBindingGrammar.Inference)
    (inferred : GeneralRuleBindingGrammar.infer? language rule = some result) :
    compile? language rule = some ⟨result.spec, .inferredGrammar result.extraTypes⟩ := by
  have undeclared : rootDeclared rule = false := by
    unfold rootDeclared
    cases names : rule.left.freeFvarNames with
    | nil => exact False.elim (captures names)
    | cons name rest => simp [empty]
  simp only [compile?, omitted, undeclared, Bool.and_false, Bool.false_and, Bool.false_eq_true,
    if_false, grammarPlan?, inferred, Option.map_some]

#print axioms compile_empty_context

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference
