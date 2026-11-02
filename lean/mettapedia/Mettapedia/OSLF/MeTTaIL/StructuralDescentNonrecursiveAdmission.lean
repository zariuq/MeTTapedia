import Mettapedia.OSLF.MeTTaIL.StructuralDescentAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment

/-! Declarations whose premises do not invoke child execution satisfy the
structural descent check. Relation queries, freshness and quantified
nonrecursive premises retain their existing admission requirements.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent

open Syntax GeneralPremise GeneralExecutionAdmission

theorem checkPremises_of_no_steps (rule : RewriteRule) (spec : RuleBindingSpec)
    (index : Nat) (premises : List Premise)
    (nonrecursive : ∀ premise ∈ premises, stepSources premise = []) :
    checkPremises rule spec index premises = true := by
  induction premises generalizing index with
  | nil => rfl
  | cons premise rest ih =>
    have head := nonrecursive premise List.mem_cons_self
    have checked : checkPremise rule spec index 0 premise = true := by
      cases premise <;> simp_all [stepSources, checkPremise]
    simp only [checkPremises, checked, Bool.true_and]
    exact ih _ (fun item member => nonrecursive item (List.mem_cons_of_mem _ member))

theorem nonrecursive_admitted (snapshot : Snapshot) (permissions : Permissions)
    (nonrecursive : ∀ rule ∈ snapshot.language.rewrites,
      ∀ premise ∈ rule.premises, stepSources premise = []) :
    checkEnvironment (GeneralPlanEnvironment.environment (compile snapshot permissions)) = true := by
  apply List.all_eq_true.mpr
  rintro ⟨rule, ordinal⟩ member
  have ruleAt := List.mk_mem_zipIdx_iff_getElem?.mp member
  change ((compile snapshot permissions).rules.map RulePlan.rule)[ordinal]? = some rule at ruleAt
  rw [List.getElem?_map] at ruleAt
  obtain ⟨declaration, position, same⟩ := Option.map_eq_some_iff.mp ruleAt
  have declared := compiled_rule_origin (List.mem_of_getElem? position)
  obtain ⟨authored, _, source, _, compiled⟩ := declared
  have info := rulePlan_readout compiled
  have noCalls : ∀ premise ∈ declaration.rule.premises, stepSources premise = [] := by
    have preserved := GeneralRuleBindingInference.elaborate_source declaration.binding declaration.authored
    change ∀ premise ∈ (declaration.binding.elaborate declaration.authored).premises, stepSources premise = []
    rw [preserved.2.2.2, info.2.1]
    exact nonrecursive authored (List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp source))
  rw [← same]
  change (match specification? (GeneralPlanEnvironment.environment (compile snapshot permissions)) ordinal with
    | none => false | some spec => checkRule declaration.rule spec) = true
  rw [GeneralPlanEnvironment.selected_specification _ position]
  simp only [checkRule, checkPremises_of_no_steps _ _ _ _ noCalls, Bool.and_true]
  exact info.2.2.2.1

#print axioms checkPremises_of_no_steps
#print axioms nonrecursive_admitted

end Mettapedia.OSLF.MeTTaIL.StructuralDescent
