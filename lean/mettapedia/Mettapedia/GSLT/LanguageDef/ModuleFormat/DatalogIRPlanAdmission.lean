import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRProjectionAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSourcePlan
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseRuleCongruence
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseStaticRuleCongruence

/-! Every compiled source clause receives an actual selected rule plan.
Binding elaboration retains its operational fields, and the actual rule
obligation list is empty. Global snapshot checks remain separate. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.PlanAdmission

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax GeneralRuleBindingInference GeneralExecutionAdmission

theorem clause_ready (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern)
    (ordinal : Nat) (clause : Clause) (source : ProgramGrounding.ClauseAt program ordinal clause)
    (rule : RewriteRule) (compiled : Query.compileClause? prepared.vocabulary ordinal clause = some rule)
    (index : Nat) :
    rulePlan? (Executable.snapshot prepared known) index rule =
        some ⟨index,rule,⟨inferredSpec rule,.inferredRootInputs⟩⟩ ∧
      ruleObligations (Executable.snapshot prepared known) index rule = [] := by
  let binding : BindingPlan := ⟨inferredSpec rule,.inferredRootInputs⟩
  have terms : prepared.compiled.terms = Query.baseLanguage.terms := SourcePlan.plan_grammar program seeds prepared accepted known
  have actualSource : ProgramGrounding.ClauseAt prepared.source ordinal clause := by
    rw [(Executable.prepare_typed program seeds prepared accepted).1]
    exact source
  have bodyCheck : GeneralPremise.rulePremisesAdmitted prepared.compiled (Executable.snapshot prepared known).provider
      (binding.elaborate rule) (inferredSpec rule) = true := by
    rw [GeneralPremise.rulePremisesAdmitted_fields_eq prepared.compiled (Executable.snapshot prepared known).provider
      (first := binding.elaborate rule) (second := rule)
      (by simp [binding,BindingPlan.elaborate,BindingPlan.implicitTypes]) rfl rfl rfl]
    exact FlowAdmission.clause_premises_admitted prepared.compiled terms prepared known ordinal clause actualSource rule compiled
  have bindingCheck := BindingAdmission.compile_binding prepared.compiled prepared.vocabulary ordinal clause rule compiled
  have canonical := CanonicalAdmission.rule_canonical prepared.vocabulary ordinal clause rule compiled
  have spine := CanonicalAdmission.binding_canonical rule
  constructor
  · simp only [rulePlan?,show (Executable.snapshot prepared known).language = prepared.compiled from rfl,
      bindingCheck,Option.bind_eq_bind,Option.bind_some,canonical,spine,Bool.and_true]
    exact if_pos bodyCheck
  · simp only [ruleObligations,show (Executable.snapshot prepared known).language = prepared.compiled from rfl,
      bindingCheck,canonical,spine,Bool.and_self,if_true]
    exact if_pos bodyCheck

theorem rule_obligations_empty (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern) :
    (selectedRules (Executable.snapshot prepared known) Executable.permissions).flatMap
      (fun (rule,index) => ruleObligations (Executable.snapshot prepared known) index rule) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro entry member
  rcases entry with ⟨rule,index⟩
  have atRule := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp member).1
  have inside : index < prepared.compiled.rewrites.length := (List.getElem?_eq_some_iff.mp atRule).1
  obtain ⟨ordinal,clause,source,compiled,_⟩ := Executable.compiled_origin_at program seeds prepared accepted index inside
  have same : prepared.compiled.rewrites[index] = rule := (List.getElem?_eq_some_iff.mp atRule).2
  rw [same] at compiled
  exact (clause_ready program seeds prepared accepted known ordinal clause source rule compiled index).2

theorem scope_checked (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern) :
    GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared known)) = true := by
  apply List.all_eq_true.mpr
  intro entry member
  rcases entry with ⟨rule,index⟩
  have atRule := List.mk_mem_zipIdx_iff_getElem?.mp member
  change (((Executable.plan prepared known).rules.map RulePlan.rule)[index]?) = some rule at atRule
  rw [List.getElem?_map] at atRule
  obtain ⟨selected,position,sameRule⟩ := Option.map_eq_some_iff.mp atRule
  subst rule
  have specified := GeneralPlanEnvironment.selected_specification (Executable.plan prepared known) position
  dsimp only
  rw [specified]
  obtain ⟨raw,rawIndex,authored,_,planned⟩ := compiled_rule_origin (List.mem_of_getElem? position)
  have fields := rulePlan_readout planned
  have atRaw := List.mk_mem_zipIdx_iff_getElem?.mp authored
  have inside : rawIndex < prepared.compiled.rewrites.length := (List.getElem?_eq_some_iff.mp atRaw).1
  obtain ⟨ordinal,clause,source,compiled,_⟩ := Executable.compiled_origin_at program seeds prepared accepted rawIndex inside
  have same : prepared.compiled.rewrites[rawIndex] = raw := (List.getElem?_eq_some_iff.mp atRaw).2
  rw [same] at compiled
  have inferred := BindingAdmission.compile_binding prepared.compiled prepared.vocabulary ordinal clause raw compiled
  have bindingSame : selected.binding = ⟨inferredSpec raw,.inferredRootInputs⟩ :=
    Option.some.inj (fields.2.2.1.symm.trans inferred)
  apply Bool.and_eq_true_iff.mpr
  refine ⟨fields.2.2.2.1,?_⟩
  have actualSource : ProgramGrounding.ClauseAt prepared.source ordinal clause := by
    rw [(Executable.prepare_typed program seeds prepared accepted).1]
    exact source
  have rawChecked := ProjectionAdmission.rule_static
    (GeneralPlanEnvironment.environment (Executable.plan prepared known)).language
    (SourcePlan.plan_grammar program seeds prepared accepted known)
    prepared known ordinal clause actualSource raw compiled
  have sameContext : selected.rule.typeContext = raw.typeContext := by
    simp [RulePlan.rule,BindingPlan.elaborate,bindingSame,fields.2.1,BindingPlan.implicitTypes]
  have sameLeft : selected.rule.left = raw.left := by simp [RulePlan.rule,BindingPlan.elaborate,fields.2.1]
  have sameRight : selected.rule.right = raw.right := by simp [RulePlan.rule,BindingPlan.elaborate,fields.2.1]
  have samePremises : selected.rule.premises = raw.premises := by simp [RulePlan.rule,BindingPlan.elaborate,fields.2.1]
  rw [bindingSame]
  rw [GeneralPremise.Static.checkRule_fields_eq _ _ sameContext sameLeft sameRight samePremises]
  exact rawChecked

#print axioms clause_ready
#print axioms rule_obligations_empty
#print axioms scope_checked

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.PlanAdmission
