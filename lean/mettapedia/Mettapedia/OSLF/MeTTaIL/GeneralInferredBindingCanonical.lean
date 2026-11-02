import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference
import Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonicalSyntax

/-! Inference-generated occurrence spines use canonical bound variables.
Authored binding declarations retain their separate metadata check.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

open Syntax

theorem specification_canonical (context : List (String × TypeExpr)) (rows : List Occurrence) :
    GeneralEquationCanonicalTemplates.checkBinding (specification context rows) = true := by
  simp [GeneralEquationCanonicalTemplates.checkBinding, specification, Pattern.hasCanonicalBinderMetadata]

theorem infer_binding_canonical (language : LanguageDef) (rule : RewriteRule) (result : Inference)
    (inferred : infer? language rule = some result) :
    GeneralEquationCanonicalTemplates.checkBinding result.spec = true := by
  simp only [infer?, Option.bind_eq_bind, Option.bind_eq_some_iff] at inferred
  obtain ⟨expected, _, left, _, right, _, premises, _, inferred⟩ := inferred
  split at inferred
  · cases Option.some.inj inferred
    exact specification_canonical _ _
  · contradiction

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference

open Syntax

theorem omitted_binding_canonical (language : LanguageDef) (rule : RewriteRule) (binding : BindingPlan)
    (omitted : rule.bindings = none) (compiled : compile? language rule = some binding) :
    GeneralEquationCanonicalTemplates.checkBinding binding.spec = true := by
  rcases compile_origin compiled with authored | root | grammar
  · rw [omitted] at authored
    cases authored.2
  · rw [root.2.2.1]
    rfl
  · obtain ⟨_, result, inferred, _, spec⟩ := grammar
    rw [spec]
    exact GeneralRuleBindingGrammar.infer_binding_canonical language rule result inferred

#print axioms omitted_binding_canonical

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference
