import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.Languages.MeTTa.OSLFCore.MetaMeTTa

/-!
# Source answer families need separate instances in a joint constraint step

The independent finite-register source is upstream of this comparison.
The same total atom substitution algebra supplies a concrete CMR profile.
The examples rule out conjoining distinct source answers under one shared
query variable, and construct an actual two-answer occurrence firing with
private variables. They are not a uniform compiler or a whole-language
adequacy theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison

open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Insertion (single wrap)

def atomAction : SubstitutionAction Atom Subst where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply := subst
  identity := empty
  compose outer inner := comp inner outer
  apply_identity := subst_empty
  apply_compose outer inner value := (subst_subst inner outer value).symm
  preserves := fun candidate {_ _} same => congrArg (subst candidate) same

theorem principal_to_constraint {left right : Atom} {answer : Subst}
    (principal : MetaMeTTa.Principal left right answer) : atomAction.Principal [(left, right)] answer := by
  constructor
  · intro equation member
    obtain rfl := List.mem_singleton.mp member
    exact principal.solves
  · intro candidate solved
    obtain ⟨residual, factors⟩ := principal.factors candidate (solved _ (List.mem_singleton_self _))
    refine ⟨residual, fun value => ?_⟩
    exact (factors value).trans (subst_subst answer residual value)

namespace Family

def a : Atom := .symbol "a"
def b : Atom := .symbol "b"
def query : Atom := .var "x"
def template : Atom := wrap "f" query
def request := MetaMeTTa.transform query template
def selected : Selection Nat := ⟨[0], [1, 2], [3, 4]⟩
def before : Configuration Atom Nat := ⟨[], {0, 1, 2}⟩

def sharedLabels (occurrence : Nat) : Atom :=
  if occurrence = 0 then request else if occurrence = 1 then a else if occurrence = 2 then b else template
def sharedRule : RuleInstance Atom := ⟨[request], [query, query], [], [], [template, template]⟩

/-- Physical availability is insufficient: conjoining the two source
answers forces the one query variable to equal two different constants. -/
theorem one_shared_variable_cannot_realize_the_family : ¬ selected.Valid atomAction sharedLabels sharedRule before := by
  intro valid
  obtain ⟨candidate, solved⟩ := valid.consistent
  have first := solved (query, a) (by simp [Selection.problem, Selection.equations, selected, sharedLabels, sharedRule, before])
  have second := solved (query, b) (by simp [Selection.problem, Selection.equations, selected, sharedLabels, sharedRule, before])
  have same := first.symm.trans second
  change a = b at same
  simp [a, b] at same

def left : Atom := .var "answer-left"
def right : Atom := .var "answer-right"
def labels (occurrence : Nat) : Atom :=
  if occurrence = 0 then request else if occurrence = 1 then a else if occurrence = 2 then b
  else if occurrence = 3 then wrap "f" left else wrap "f" right
def rule : RuleInstance Atom := ⟨[request], [left, right], [], [], [wrap "f" left, wrap "f" right]⟩
def result := selected.result labels rule before

def extendCaller (caller : Subst) : Subst := fun name =>
  if name = "answer-left" then some a else if name = "answer-right" then some b else caller name

theorem every_caller_has_a_joint_extension (caller : Subst) :
    atomAction.Models (extendCaller caller) (selected.problem labels rule before) := by
  intro equation member
  change equation ∈ [(request, request), (left, a), (right, b)] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rfl
  · rfl
  · rfl

/-- All caller observations avoiding the two fresh private names retain
their original joint values, not merely their individual marginals. -/
theorem caller_terms_are_protected (caller : Subst) (value : Atom)
    (leftFresh : "answer-left" ∉ vars value) (rightFresh : "answer-right" ∉ vars value) :
    subst (extendCaller caller) value = subst caller value := by
  apply subst_congr_on_vars
  intro name present
  have notLeft : name ≠ "answer-left" := fun same => leftFresh (same ▸ present)
  have notRight : name ≠ "answer-right" := fun same => rightFresh (same ▸ present)
  simp [extendCaller, notLeft, notRight]

theorem private_answer_variables_give_an_actual_step : Step atomAction labels rule before result := by
  refine ⟨selected, ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl, by decide +kernel,
    ⟨extendCaller empty, every_caller_has_a_joint_extension empty⟩, ?_⟩, rfl⟩
  intro check member
  cases member

theorem every_joint_solution_has_the_source_answer_multiset (candidate : Subst)
    (solved : atomAction.Models candidate result.equations) :
    ((selected.made.map fun occurrence => subst candidate (labels occurrence)) : Multiset Atom) =
      {wrap "f" a, wrap "f" b} := by
  have first := solved (left, a) (by simp [result, Selection.result, Selection.problem, Selection.equations, selected, labels, rule, before])
  have second := solved (right, b) (by simp [result, Selection.result, Selection.problem, Selection.equations, selected, labels, rule, before])
  change subst candidate left = a at first
  change subst candidate right = b at second
  change (([subst candidate (wrap "f" left), subst candidate (wrap "f" right)] : List Atom) : Multiset Atom) = _
  rw [Insertion.subst_wrap, Insertion.subst_wrap, first, second]
  rfl

def sourceUse (value : Atom) (ground : vars value = []) : MetaMeTTa.ContextUse query :=
  ⟨.hole, value, single "x" value, MetaMeTTa.principal_variable "x" value (by simp [ground])⟩
def sourceBefore : MeTTaState := ⟨{request}, ⟨{a, b}⟩, 0, 0⟩
def sourceAfter : MeTTaState := ⟨0, ⟨{a, b}⟩, {wrap "f" a, wrap "f" b}, 0⟩

theorem source_collects_the_family (policy : MetaMeTTa.EmptyFamily) : MetaMeTTa.Step policy sourceBefore sourceAfter := by
  have admitted : policy.Admits 2 := by cases policy <;> simp [MetaMeTTa.EmptyFamily.Admits]
  simpa [sourceBefore, sourceAfter, request, sourceUse, MetaMeTTa.ContextUse.entry, MetaMeTTa.ContextUse.result,
    MetaMeTTa.Context.fill, query, template, wrap, subst, subst.substList, single, ← Multiset.cons_coe] using
    (MetaMeTTa.Step.transform (policy := policy) 0 0 0 0 query template
      [sourceUse a rfl, sourceUse b rfl] admitted (MetaMeTTa.insensitive_empty query))

/-- Both sides execute, and every solution of the selected core firing has
exactly the source's two-result workspace observation. -/
theorem concrete_source_and_core_agree (policy : MetaMeTTa.EmptyFamily) :
    MetaMeTTa.Step policy sourceBefore sourceAfter ∧ Step atomAction labels rule before result ∧
      ∀ candidate, atomAction.Models candidate result.equations →
        ((selected.made.map fun occurrence => subst candidate (labels occurrence)) : Multiset Atom) = sourceAfter.workspace :=
  ⟨source_collects_the_family policy, private_answer_variables_give_an_actual_step,
    every_joint_solution_has_the_source_answer_multiset⟩

def duplicated : Selection Nat := ⟨[0], [1, 1], [3, 4]⟩
def duplicateAnswer : Subst := fun name =>
  if name = "answer-left" ∨ name = "answer-right" then some a else none

/-- Fresh answer variables alone do not enforce a source catalogue
enumeration: the general core also permits two reads of the same row. -/
theorem unrestricted_read_aliasing_admits_another_firing :
    duplicated.Valid atomAction labels rule before := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl, by decide +kernel, ?_, ?_⟩
  · refine ⟨duplicateAnswer, ?_⟩
    intro equation member
    change equation ∈ [(request, request), (left, a), (right, a)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · intro check member
    cases member

theorem that_aliasing_repeats_the_first_result :
    ((duplicated.made.map fun occurrence => subst duplicateAnswer (labels occurrence)) : Multiset Atom) =
      {wrap "f" a, wrap "f" a} := rfl

/-- The independent source rule's multiset decomposition prevents using its
single a occurrence twice. A complete encoding must preserve this condition
as well as keeping the answer substitutions separate. -/
theorem source_catalogue_cannot_supply_that_duplicate_family :
    ¬ ∃ rest : Multiset Atom, ({a, b} : Multiset Atom) = ({a, a} : Multiset Atom) + rest := by
  rintro ⟨rest, same⟩
  have counts := congrArg (Multiset.count a) same
  simp [a, b] at counts

end Family

namespace OperationalEquality

open Family (a b)

def useEquation : MetaMeTTa.EquationUse a := ⟨a, b, empty, MetaMeTTa.principal_refl a⟩

theorem a_stored_equation_can_rewrite_distinct_constants (policy : MetaMeTTa.EmptyFamily) :
    MetaMeTTa.Step policy ⟨{a}, ⟨{Atom.equality a b}⟩, 0, 0⟩
      ⟨0, ⟨{Atom.equality a b}⟩, {b}, 0⟩ := by
  have admitted : policy.Admits 1 := by cases policy <;> simp [MetaMeTTa.EmptyFamily.Admits]
  simpa [useEquation, MetaMeTTa.EquationUse.entry, MetaMeTTa.EquationUse.result, MetaMeTTa.Context.fill,
    subst_empty] using
    (MetaMeTTa.Step.query (policy := policy) 0 0 0 0 .hole a [useEquation] admitted (MetaMeTTa.insensitive_empty a))

/-- An operational equation in the knowledge register is not automatically
a constraint or a license for conversion under structural equality. -/
theorem telling_that_structural_equality_would_be_inconsistent : ¬ atomAction.Consistent [(a, b)] := by
  rintro ⟨candidate, solved⟩
  have impossible := solved _ (List.mem_singleton_self _)
  change a = b at impossible
  simp [a, b] at impossible

def labels (occurrence : Nat) : Atom := if occurrence = 0 then a else b
def rule : RuleInstance Atom := ⟨[a], [], [], [], [b]⟩
def selected : Selection Nat := ⟨[0], [], [1]⟩
def before : Configuration Atom Nat := ⟨[], {0}⟩

/-- The core can perform the operational change using its resource and
production parts, without adding the false equality a=b to information. -/
theorem the_rewrite_is_an_actual_occurrence_step :
    Step atomAction labels rule before (selected.result labels rule before) := by
  refine ⟨selected, ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl, by decide +kernel, ?_, ?_⟩, rfl⟩
  · refine ⟨empty, ?_⟩
    intro equation member
    change equation ∈ [(a, a)] at member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · intro check member
    cases member

end OperationalEquality

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison
