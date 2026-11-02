import Mettapedia.Languages.MeTTa.OSLFCore.MetaMeTTa
import Mettapedia.Languages.MeTTa.OSLFCore.RewriteRules

/-!
# Source register steps and the older workspace prototype are different

The comparison fixes the same input representation and observes the output
multiset of one reachable state. It allows any finite number of prototype
steps. It does not exclude a different encoding or a different observation
such as collecting results across separate nondeterministic branches.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.MeTTa.OSLFCore.MetaMeTTa.Controls

open Mettapedia.Languages.MeTTa.SubstitutionAlgebra
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Insertion (single)

def a : Atom := .symbol "a"
def b : Atom := .symbol "b"
def request := transform a b
def knowledge : Atomspace := ⟨{a}⟩
def start : MeTTaState := ⟨{request}, knowledge, 0, 0⟩
def queued : MeTTaState := ⟨0, knowledge, {request}, 0⟩
def literalOutput : MeTTaState := ⟨0, knowledge, 0, {request}⟩
def transformed : MeTTaState := ⟨0, knowledge, {b}, 0⟩
def transformedOutput : MeTTaState := ⟨0, knowledge, 0, {b}⟩

def useA : ContextUse a := ⟨.hole, a, empty, principal_refl a⟩

theorem one_admitted (policy : EmptyFamily) : policy.Admits 1 := by
  cases policy <;> simp [EmptyFamily.Admits]

theorem any_query_is_insensitive_to_this_non_equation (query : Atom) : Insensitive query knowledge.atoms := by
  intro left right member
  have same := Multiset.mem_singleton.mp member
  cases same

theorem source_transform_uses_its_explicit_template (policy : EmptyFamily) : Step policy start transformed := by
  have rule := Step.transform (policy := policy) 0 0 0 0 a b [useA]
    (one_admitted policy) (insensitive_empty a)
  simpa [start, transformed, request, knowledge, useA, ContextUse.entry, ContextUse.result,
    Context.fill, subst_empty] using rule

theorem source_emits_the_transformed_value (policy : EmptyFamily) : Reaches policy start transformedOutput := by
  have returned : Step policy transformed transformedOutput := by
    simpa [transformed, transformedOutput] using
      (Step.output (policy := policy) 0 knowledge.atoms 0 0 b
        (any_query_is_insensitive_to_this_non_equation b))
  exact (Relation.ReflTransGen.single (source_transform_uses_its_explicit_template policy)).tail returned

theorem prototype_transform_has_no_input_register_step : ruleTransform start = 0 := by
  simp [ruleTransform, ruleQuery, start]

theorem prototype_first_step : applyRewriteRules start = {queued} := by
  simp [applyRewriteRules, ruleInput, ruleQuery, ruleAddAtom, ruleRemAtom, ruleOutput,
    start, queued, MeTTaState.inputToWorkspace, Multiset.filter_zero]

theorem prototype_queued_steps : applyRewriteRules queued = {queued} + {literalOutput} := by
  simp [applyRewriteRules, ruleInput, ruleQuery, ruleAddAtom, ruleRemAtom, ruleOutput,
    queued, literalOutput, request, transform, knowledge, a,
    Atomspace.queryEquations, Atomspace.equations, Atomspace.isEquation, Atomspace.insensitive,
    MeTTaState.workspaceToOutput, Multiset.filter_singleton]
  rfl

theorem prototype_output_stops : applyRewriteRules literalOutput = 0 := by
  simp [applyRewriteRules, ruleInput, ruleQuery, ruleAddAtom, ruleRemAtom, ruleOutput, literalOutput, Multiset.filter_zero]

def PrototypeStep (before after : MeTTaState) : Prop := after ∈ applyRewriteRules before
def PrototypeReaches := Relation.ReflTransGen PrototypeStep

theorem prototype_reachable_states {after : MeTTaState} (path : PrototypeReaches start after) :
    after = start ∨ after = queued ∨ after = literalOutput := by
  induction path with
  | refl => exact Or.inl rfl
  | @tail middle last _ edge ih =>
      change last ∈ applyRewriteRules middle at edge
      rcases ih with rfl | rfl | rfl
      · rw [prototype_first_step] at edge
        exact Or.inr (Or.inl (Multiset.mem_singleton.mp edge))
      · rw [prototype_queued_steps, Multiset.mem_add] at edge
        rcases edge with first | second
        · exact Or.inr (Or.inl (Multiset.mem_singleton.mp first))
        · exact Or.inr (Or.inr (Multiset.mem_singleton.mp second))
      · rw [prototype_output_stops] at edge
        exact False.elim (Multiset.notMem_zero _ edge)

theorem prototype_never_emits_the_transformed_value {after : MeTTaState}
    (path : PrototypeReaches start after) : b ∉ after.output := by
  rcases prototype_reachable_states path with rfl | rfl | rfl
  · simp [start]
  · simp [queued]
  · simp [literalOutput, request, transform, b]

/-- Even allowing arbitrarily many finite prototype steps cannot recover
this source output with the identity input representation and exact output
observation. This is not an impossibility result for all encodings. -/
theorem no_identity_output_simulation (policy : EmptyFamily) :
    ¬ (∀ reached, Reaches policy start reached → ∃ target,
      PrototypeReaches start target ∧ reached.output = target.output) := by
  intro simulation
  obtain ⟨target, path, outputs⟩ := simulation transformedOutput (source_emits_the_transformed_value policy)
  apply prototype_never_emits_the_transformed_value path
  rw [← outputs]
  exact Multiset.mem_singleton_self b

def wrapped : Context := .expression [.symbol "wrapper"] .hole []
def nestedUse : ContextUse a := ⟨wrapped, a, empty, principal_refl a⟩

theorem source_preserves_the_selected_knowledge_context (policy : EmptyFamily) :
    Step policy ⟨{request}, ⟨{wrapped.fill a}⟩, 0, 0⟩
      ⟨0, ⟨{wrapped.fill a}⟩, {wrapped.fill b}, 0⟩ := by
  simpa [request, nestedUse, ContextUse.entry, ContextUse.result, subst_empty] using
    (Step.transform (policy := policy) 0 0 0 0 a b [nestedUse]
      (one_admitted policy) (insensitive_empty a))

def variableUse : ContextUse (.var "x") :=
  ⟨.hole, a, single "x" a, principal_variable "x" a (by simp [a, vars])⟩
def template : Atom := .expression [.symbol "f", .var "x"]
def instantiated : Atom := .expression [.symbol "f", a]

theorem this_template_has_the_same_result_for_every_principal_answer
    {answer : Subst} (principal : Principal (.var "x") a answer) :
    subst answer template = instantiated := by
  have same := grounded_template_result_is_determined .hole (.var "x") template a
    (by simp [a, vars]) (by simp [template, vars, vars.varsList]) principal variableUse.principal
  simpa [variableUse, Context.fill, template, instantiated, subst, subst.substList, single] using same

theorem source_transform_performs_a_nontrivial_substitution (policy : EmptyFamily) :
    Step policy ⟨{transform (.var "x") template}, knowledge, 0, 0⟩
      ⟨0, knowledge, {instantiated}, 0⟩ := by
  simpa [variableUse, ContextUse.entry, ContextUse.result, Context.fill, template, instantiated,
    knowledge, subst, subst.substList, single] using
    (Step.transform (policy := policy) 0 0 0 0 (.var "x") template [variableUse]
      (one_admitted policy) (insensitive_empty (.var "x")))

def variableUseB : ContextUse (.var "x") :=
  ⟨.hole, b, single "x" b, principal_variable "x" b (by simp [b, vars])⟩
def secondInstance : Atom := .expression [.symbol "f", b]

theorem two_admitted (policy : EmptyFamily) : policy.Admits 2 := by
  cases policy <;> simp [EmptyFamily.Admits]

theorem one_source_step_collects_distinct_substitution_instances (policy : EmptyFamily) :
    Step policy ⟨{transform (.var "x") template}, ⟨{a, b}⟩, 0, 0⟩
      ⟨0, ⟨{a, b}⟩, {instantiated, secondInstance}, 0⟩ := by
  simpa [variableUse, variableUseB, ContextUse.entry, ContextUse.result, Context.fill,
    template, instantiated, secondInstance, subst, subst.substList, single, ← Multiset.cons_coe] using
    (Step.transform (policy := policy) 0 0 0 0 (.var "x") template [variableUse, variableUseB]
      (two_admitted policy) (insensitive_empty (.var "x")))

/-- A family of source answers is not the conjunction of their bindings.
An encoding needs separate answer instances instead of one shared x=a=b. -/
theorem the_two_answer_substitutions_have_no_shared_solution :
    ¬ ∃ candidate : Subst, subst candidate (.var "x") = a ∧ subst candidate (.var "x") = b := by
  rintro ⟨candidate, first, second⟩
  have same := first.symm.trans second
  simp [a, b] at same

theorem duplicate_knowledge_occurrences_produce_duplicate_results (policy : EmptyFamily) :
    Step policy ⟨{request}, ⟨{a, a}⟩, 0, 0⟩ ⟨0, ⟨{a, a}⟩, {b, b}, 0⟩ := by
  simpa [request, useA, ContextUse.entry, ContextUse.result, Context.fill, subst_empty, ← Multiset.cons_coe] using
    (Step.transform (policy := policy) 0 0 0 0 a b [useA, useA]
      (two_admitted policy) (insensitive_empty a))

theorem equation_insensitivity_is_not_contextual_coverage :
    Insensitive a knowledge.atoms ∧ ¬ ContextInsensitive a knowledge.atoms := by
  refine ⟨any_query_is_insensitive_to_this_non_equation a, ?_⟩
  intro covered
  exact covered .hole a (Multiset.mem_singleton_self _) ⟨empty, rfl⟩

/-- Under the displayed equation-only remainder condition, Transform can
leave an otherwise matching non-equation occurrence unselected. -/
theorem the_literal_remainder_condition_allows_a_partial_family (policy : EmptyFamily) :
    Step policy ⟨{request}, ⟨{a, a}⟩, 0, 0⟩ ⟨0, ⟨{a, a}⟩, {b}, 0⟩ := by
  simpa [request, useA, ContextUse.entry, ContextUse.result, Context.fill, subst_empty,
    knowledge, Multiset.cons_add] using
    (Step.transform (policy := policy) 0 knowledge.atoms 0 0 a b [useA]
      (one_admitted policy) (any_query_is_insensitive_to_this_non_equation a))

theorem literal_transform_has_two_different_result_counts (policy : EmptyFamily) :
    (∃ reached, Step policy ⟨{request}, ⟨{a, a}⟩, 0, 0⟩ reached ∧ reached.workspace.card = 1) ∧
    (∃ reached, Step policy ⟨{request}, ⟨{a, a}⟩, 0, 0⟩ reached ∧ reached.workspace.card = 2) :=
  ⟨⟨_, the_literal_remainder_condition_allows_a_partial_family policy, by simp⟩,
    ⟨_, duplicate_knowledge_occurrences_produce_duplicate_results policy, by simp⟩⟩

theorem admitting_an_empty_query_family_discards_an_unmatched_input :
    Step .allowed ⟨{a}, ⟨0⟩, 0, 0⟩ ⟨0, ⟨0⟩, 0, 0⟩ := by
  simpa [EquationUse.entry, EquationUse.result, Context.fill] using
    (Step.query (policy := .allowed) 0 0 0 0 .hole a [] True.intro (insensitive_empty a))

theorem nonempty_policy_rejects_that_family : ¬ EmptyFamily.forbidden.Admits 0 := by
  simp [EmptyFamily.Admits]

def surrounding : Context := .expression [.symbol "pair", .var "x"] .hole []
def equationUse : EquationUse (.var "x") :=
  ⟨a, b, single "x" a, principal_variable "x" a (by simp [a, vars])⟩

/-- Query substitutes the selected equation RHS, leaving its displayed
surrounding context unchanged. A global binding of that context's x would
therefore be a different interpretation. -/
theorem query_keeps_the_original_surrounding_context (policy : EmptyFamily) :
    Step policy ⟨{surrounding.fill (.var "x")}, ⟨{Atom.equality a b}⟩, 0, 0⟩
      ⟨0, ⟨{Atom.equality a b}⟩, {surrounding.fill b}, 0⟩ := by
  simpa [equationUse, EquationUse.entry, EquationUse.result, subst, b] using
    (Step.query (policy := policy) 0 0 0 0 surrounding (.var "x") [equationUse]
      (one_admitted policy) (insensitive_empty (.var "x")))

theorem substituting_the_whole_context_changes_that_observation :
    surrounding.fill (subst (single "x" a) b) ≠ subst (single "x" a) (surrounding.fill b) := by
  simp [surrounding, Context.fill, subst, subst.substList, single, a, b]

end Mettapedia.Languages.MeTTa.OSLFCore.MetaMeTTa.Controls
