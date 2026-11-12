import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanCompiler

/-!
# Source branch construction rules

These rules distinguish SWI's compile-time output alias from a runtime
equation. They mention the actual term unifier and emitted forms, not a whole
evaluator oracle or the branch compiler's successful result as a premise.
They characterize compilation, not execution of the resulting goals.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.OutputPlan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

inductive BranchRel : BranchPolicy → Supply → Plan → Atom → Supply × Atom → Prop where
  | runtime (supply : Supply) (plan : Plan) (output : Atom) :
      BranchRel .runtimeConstraints supply plan output
        (supply,equate plan.output output plan.goals)
  | pureValue (supply : Supply) (plan : Plan) (output : Atom)
      (pureGoals : plan.goals = unit) :
      BranchRel .swiAliases supply plan output (supply,equate plan.output output unit)
  | outputAlias (supply : Supply) (plan : Plan) (output : Atom) (name : String) (aliases : Subst)
      (nontrivial : plan.goals ≠ unit) (variableOutput : supply.normalize plan.output = .var name)
      (unified : Unifying.unify supply.aliases (.var name) output = .ok aliases) :
      BranchRel .swiAliases supply plan output (⟨supply.used,aliases⟩,plan.goals)
  | structured (supply : Supply) (plan : Plan) (output : Atom)
      (nontrivial : plan.goals ≠ unit)
      (notVariable : ∀ name, supply.normalize plan.output ≠ .var name) :
      BranchRel .swiAliases supply plan output (supply,equate plan.output output plan.goals)

theorem branch_of_rule {policy : BranchPolicy} {supply : Supply} {plan : Plan}
    {output : Atom} {result : Supply × Atom} (rule : BranchRel policy supply plan output result) :
    branch supply plan output policy = some result := by
  cases rule with
  | runtime => rfl
  | pureValue supply plan output pureGoals =>
      simp [branch,show (BranchPolicy.swiAliases == .runtimeConstraints) = false from rfl,pureGoals]
  | outputAlias supply plan output name aliases nontrivial variableOutput unified =>
      simp [branch,show (BranchPolicy.swiAliases == .runtimeConstraints) = false from rfl,
        nontrivial,variableOutput,unified]
  | structured supply plan output nontrivial notVariable =>
      cases normalized : supply.normalize plan.output with
      | var name => exact False.elim (notVariable name normalized)
      | symbol name => simp [branch,show (BranchPolicy.swiAliases == .runtimeConstraints) = false from rfl,
          nontrivial,normalized]
      | grounded value => simp [branch,show (BranchPolicy.swiAliases == .runtimeConstraints) = false from rfl,
          nontrivial,normalized]
      | expression terms => simp [branch,show (BranchPolicy.swiAliases == .runtimeConstraints) = false from rfl,
          nontrivial,normalized]

theorem branch_has_rule {policy : BranchPolicy} {supply : Supply} {plan : Plan}
    {output : Atom} {result : Supply × Atom} (computed : branch supply plan output policy = some result) :
    BranchRel policy supply plan output result := by
  cases policy with
  | runtimeConstraints =>
      change some (supply,equate plan.output output plan.goals) = some result at computed
      cases computed
      exact .runtime supply plan output
  | swiAliases =>
      have different : (BranchPolicy.swiAliases == .runtimeConstraints) = false := rfl
      by_cases pureGoals : plan.goals = unit
      · simp [branch,different,pureGoals] at computed
        subst result
        exact .pureValue supply plan output pureGoals
      · cases normalized : supply.normalize plan.output with
        | var name =>
            cases unified : Unifying.unify supply.aliases (.var name) output with
            | ok aliases =>
                simp [branch,different,pureGoals,normalized,unified] at computed
                subst result
                exact .outputAlias supply plan output name aliases pureGoals normalized unified
            | clash => simp [branch,different,pureGoals,normalized,unified] at computed
            | exhausted => simp [branch,different,pureGoals,normalized,unified] at computed
        | symbol name =>
            simp [branch,different,pureGoals,normalized] at computed
            subst result
            exact .structured supply plan output pureGoals (by simp [normalized])
        | grounded value =>
            simp [branch,different,pureGoals,normalized] at computed
            subst result
            exact .structured supply plan output pureGoals (by simp [normalized])
        | expression terms =>
            simp [branch,different,pureGoals,normalized] at computed
            subst result
            exact .structured supply plan output pureGoals (by simp [normalized])

theorem branch_iff (policy : BranchPolicy) (supply : Supply) (plan : Plan)
    (output : Atom) (result : Supply × Atom) :
    branch supply plan output policy = some result ↔ BranchRel policy supply plan output result :=
  ⟨branch_has_rule,branch_of_rule⟩

inductive BranchesRel (policy : BranchPolicy) : Supply → List Plan → Atom → Supply × List Atom → Prop where
  | nil (supply : Supply) (output : Atom) : BranchesRel policy supply [] output (supply,[])
  | cons (supply : Supply) (first : Plan) (rest : List Plan) (output : Atom)
      (selected : Supply × Atom) (later : Supply × List Atom)
      (head : BranchRel policy supply first output selected)
      (tail : BranchesRel policy selected.1 rest output later) :
      BranchesRel policy supply (first :: rest) output (later.1,selected.2 :: later.2)

theorem branches_iff (policy : BranchPolicy) (plans : List Plan) :
    ∀ supply output result,
      branches policy supply plans output = some result ↔ BranchesRel policy supply plans output result := by
  induction plans with
  | nil =>
      intro supply output result
      constructor
      · intro computed
        simp only [branches,Option.some.injEq] at computed
        subst result
        exact .nil supply output
      · intro rule
        cases rule
        rfl
  | cons first rest ih =>
      intro supply output result
      constructor
      · intro computed
        simp only [branches,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
        obtain ⟨selected,head,later,tail,rfl⟩ := computed
        exact .cons supply first rest output selected later (branch_has_rule head)
          ((ih selected.1 output later).mp tail)
      · intro rule
        cases rule with
        | cons _ _ _ _ selected later head tail =>
            simp only [branches,branch_of_rule head,(ih selected.1 output later).mpr tail,
              bind,pure,Option.bind_some]

theorem branch_rule_functional {policy : BranchPolicy} {supply : Supply} {plan : Plan}
    {output : Atom} {first second : Supply × Atom}
    (left : BranchRel policy supply plan output first)
    (right : BranchRel policy supply plan output second) : first = second := by
  exact Option.some.inj ((branch_of_rule left).symm.trans (branch_of_rule right))

end Mettapedia.Languages.MeTTa.PeTTa.OutputPlan
