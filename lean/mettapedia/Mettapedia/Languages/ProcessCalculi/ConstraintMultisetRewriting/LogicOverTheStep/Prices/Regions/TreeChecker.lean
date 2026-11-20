import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Acceptance

/-!
# The definition checker's acceptance table: a finite table with the constant bound 16

The tree's checker of definitions over the vector package (`Vectors.Checker.procedure`) answers the
seven definitions of its acceptance table at budget 16 and at every larger budget
(`table_answered`), by the tree's kernel-evaluated verdicts (`append_admitted`, `keep_refused`, …) and
its law that a decided verdict is kept (`procedure_of_admitted`, `procedure_of_refused`). So the table is
a region with the constant bound 16, the first mechanism of a faster checker (`Regions.table_boundedOn`
in the abstract). Beyond the table no bound is proved: `konst A a = λ _. a` is not decided at budget 16
(`konst_undecided`), and whether some budget decides it is not proved in the tree.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.TreeChecker

open NativeTypesOnTheStep.Computing
open NativeTypesOnTheStep.Computing.Vectors.Checker

/-- The seven definitions of the acceptance table. -/
def table : List Definition :=
  [appendDef, keepDef, nilNilDef, consFirstDef, nilPairDef, headDef, evalDef]

/-- **The table is answered from budget 16 on.** -/
theorem table_answered : ∀ d ∈ table, ∀ k, 16 ≤ k → procedure.verdict k d ≠ .undecided := by
  intro d member k le
  simp only [table, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same | same <;> subst same
  · rw [append_procedure k le]
    exact fun h => Budgeted.Verdict.noConfusion h
  · rw [keep_procedure k le]
    exact fun h => Budgeted.Verdict.noConfusion h
  · rw [nilNil_procedure k le]
    exact fun h => Budgeted.Verdict.noConfusion h
  · rw [procedure_of_refused consFirst_refused k le]
    exact fun h => Budgeted.Verdict.noConfusion h
  · rw [procedure_of_refused nilPair_refused k le]
    exact fun h => Budgeted.Verdict.noConfusion h
  · rw [head_procedure k le]
    exact fun h => Budgeted.Verdict.noConfusion h
  · rw [eval_procedure k le]
    exact fun h => Budgeted.Verdict.noConfusion h

/-- The table's definitions are named `append`, `head` and `eval`. -/
theorem table_names : ∀ d ∈ table, d.name ≠ "konst" := by
  simp [table, appendDef, keepDef, nilNilDef, consFirstDef, nilPairDef, headDef, evalDef]

/-- **Control: outside the table, `konst` is not decided at budget 16.** -/
theorem konst_outside : konstDef ∉ table ∧ checkDefinition 16 konstDef = .undecided :=
  ⟨fun member => table_names konstDef member rfl, konst_undecided⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.TreeChecker

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.TreeChecker in
#print axioms table_answered
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.TreeChecker in
#print axioms konst_outside
