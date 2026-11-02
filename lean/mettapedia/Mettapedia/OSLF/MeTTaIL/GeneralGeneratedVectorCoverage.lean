import Mettapedia.OSLF.MeTTaIL.GeneralInferredVectorRoot
import Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment

/-! A generated rule with omitted binding declarations and an empty
authored context obtains its capture context through the existing grammar
inference. Selected plans retain that actual origin and root coverage.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference

open Syntax RuleBinding

theorem generated_grammar_origin {language : LanguageDef} {rule : RewriteRule} {binding : BindingPlan}
    (omitted : rule.bindings = none) (empty : rule.typeContext = [])
    (hasInput : rule.left.freeFvarNames ≠ []) (compiled : compile? language rule = some binding) :
    ∃ inference, GeneralRuleBindingGrammar.infer? language rule = some inference ∧
      binding.origin = .inferredGrammar inference.extraTypes ∧ binding.spec = inference.spec := by
  rcases compile_origin compiled with authored | root | grammar
  · rw [omitted] at authored
    cases authored.2
  · have declared := root.2.2.2.2
    unfold rootDeclared at declared
    rw [empty] at declared
    have none : rule.left.freeFvarNames = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro name member
      have impossible := List.all_eq_true.mp declared name (List.mem_append_left _ member)
      cases impossible
    exact False.elim (hasInput none)
  · obtain ⟨_, inference, inferred, origin, spec⟩ := grammar
    exact ⟨inference, inferred, origin, spec⟩

theorem generated_elaborate {rule : RewriteRule} {binding : BindingPlan} {inference : GeneralRuleBindingGrammar.Inference}
    (origin : binding.origin = .inferredGrammar inference.extraTypes) (spec : binding.spec = inference.spec) :
    binding.elaborate rule = GeneralRuleBindingGrammar.elaborate rule inference := by
  simp only [BindingPlan.elaborate, BindingPlan.implicitTypes, origin, spec, GeneralRuleBindingGrammar.elaborate]

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem generated_plan_root_construct {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {type : TypeExpr} {assignment : Bindings} {source target : Pattern}
    (position : plan.rules[ordinal]? = some row)
    (compiled : GeneralRuleBindingInference.compile? (GeneralPlanEnvironment.environment plan).language row.authored = some row.binding)
    (omitted : row.authored.bindings = none) (empty : row.authored.typeContext = [])
    (hasInput : row.authored.left.freeFvarNames ≠ [])
    (labels : LabelDeterministic (GeneralPlanEnvironment.environment plan).language)
    (choices : CollectionChoiceDeterministic (GeneralPlanEnvironment.environment plan).language)
    (leftShape : VectorFirstOrder row.authored.left) (rightShape : VectorFirstOrder row.authored.right)
    (head : GeneralRuleBindingGrammar.headType? (GeneralPlanEnvironment.environment plan).language [] [] row.authored.left = some type)
    (premiseFree : row.authored.premises = [])
    (rightBound : ∀ name ∈ row.authored.right.freeFvarNames, name ∈ row.authored.left.freeFvarNames)
    (sourceClosed : source.freeFvarNames = [])
    (sourceTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free [] type source)
    (targetTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free [] type target)
    (input : applyBindings assignment row.authored.left = source)
    (output : applyBindings assignment row.authored.right = target) :
    ∃ trace captured, GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] type source ordinal
      trace captured captured [] target := by
  obtain ⟨inference, inferred, origin, spec⟩ := GeneralRuleBindingInference.generated_grammar_origin omitted empty hasInput compiled
  have elaborated := GeneralRuleBindingInference.generated_elaborate (rule := row.authored) origin spec
  have declared := GeneralPlanEnvironment.selected_rule plan position
  change (GeneralPlanEnvironment.environment plan).language.rewrites[ordinal]? = some (row.binding.elaborate row.authored) at declared
  rw [elaborated] at declared
  have specified := GeneralPlanEnvironment.selected_specification plan position
  rw [spec] at specified
  exact inferred_vector_root_construct declared specified inferred labels choices leftShape rightShape
    (empty ▸ head) premiseFree rightBound sourceClosed sourceTyped targetTyped input output

#print axioms generated_plan_root_construct

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
