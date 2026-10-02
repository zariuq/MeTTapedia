import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Binding-flow admission for rules with one reduction hypothesis

The ordered binding-flow gate accepts a rule when every variable it reads has
been bound before it is read.  This module states that gate, for the two
shapes of rule a calculus with contextual reduction uses, as a condition on
the variables of the rule.

* A rule with no premise passes when every variable of its right side occurs
  on its left side.
* A rule whose single premise is a reduction between two metavariables passes
  when the source of the premise occurs on the left side and every variable of
  the right side is the target of the premise or occurs on the left side.

A language whose rules have these shapes and which authors no equation passes
the gate for any table of relation modes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Syntax

namespace LanguageDef

open private directedRuleFlowErrors checkPremiseFlow availabilityErrors missingNames
  FlowState.addBindings from Mettapedia.OSLF.MeTTaIL.Syntax

/-- A rule passes the binding-flow gate by its shape. -/
inductive RuleFlows (rule : RewriteRule) : Prop where
  /-- No premise: the right side reads only what the left side binds. -/
  | plain
      (premiseFree : rule.premises = [])
      (rightBound : ∀ name ∈ rule.right.freeFvarNames, name ∈ rule.left.freeFvarNames) :
      RuleFlows rule
  /-- One reduction between two metavariables: its source is bound by the left
  side, and the right side reads the left side's variables and its target. -/
  | contextual (source target : String)
      (premises : rule.premises = [.congruence (.fvar source) (.fvar target)])
      (sourceBound : source ∈ rule.left.freeFvarNames)
      (rightBound : ∀ name ∈ rule.right.freeFvarNames,
        name = target ∨ name ∈ rule.left.freeFvarNames) :
      RuleFlows rule

/-- A rule of either shape produces no binding-flow error. -/
theorem directedRuleFlowErrors_eq_nil_of_ruleFlows (modes : RelationModeTable)
    (context : String) {rule : RewriteRule} (flows : RuleFlows rule) :
    directedRuleFlowErrors modes context rule.premises rule.left rule.right = [] := by
  cases flows with
  | plain premiseFree rightBound =>
      rw [premiseFree]
      unfold directedRuleFlowErrors
      simp only [checkPremiseFlow, List.nil_append]
      unfold availabilityErrors missingNames
      apply List.map_eq_nil_iff.mpr
      apply List.filter_eq_nil_iff.mpr
      intro name erasedMembership
      have rightMembership : name ∈ rule.right.freeFvarNames :=
        List.mem_eraseDups.mp erasedMembership
      simp [rightBound name rightMembership]
  | contextual source target premises sourceBound rightBound =>
      rw [premises]
      unfold directedRuleFlowErrors
      simp only [checkPremiseFlow, List.append_nil, List.append_eq_nil_iff]
      constructor
      · unfold availabilityErrors missingNames
        apply List.map_eq_nil_iff.mpr
        apply List.filter_eq_nil_iff.mpr
        intro name erasedMembership
        have isSource : name = source := by
          simpa [Pattern.freeFvarNames] using List.mem_eraseDups.mp erasedMembership
        subst isSource
        simp [sourceBound]
      · unfold availabilityErrors missingNames
        apply List.map_eq_nil_iff.mpr
        apply List.filter_eq_nil_iff.mpr
        intro name erasedMembership
        have rightMembership : name ∈ rule.right.freeFvarNames :=
          List.mem_eraseDups.mp erasedMembership
        rcases rightBound name rightMembership with isTarget | inLeft
        · subst isTarget
          simp [FlowState.addBindings, Pattern.freeFvarNames]
        · simp [FlowState.addBindings, inLeft]

/-- **Flow admission by shape.**  A language with no authored equation whose
every rule has one of the two shapes passes the binding-flow gate. -/
theorem executionFlowErrors_eq_nil_of_ruleFlows (lang : LanguageDef)
    (modes : RelationModeTable) (equationsEmpty : lang.equations = [])
    (rules : ∀ rule ∈ lang.rewrites, RuleFlows rule) :
    lang.executionFlowErrors modes = [] := by
  unfold executionFlowErrors
  rw [equationsEmpty]
  simp only [List.flatMap_nil, List.append_nil]
  apply List.flatMap_eq_nil_iff.mpr
  intro rule membership
  exact directedRuleFlowErrors_eq_nil_of_ruleFlows modes _ (rules rule membership)

end LanguageDef

end Mettapedia.OSLF.MeTTaIL.Syntax
