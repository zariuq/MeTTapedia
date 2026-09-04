import Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation

/-!
# Binding-preserving compilation of first-order pattern plans

This module lowers a first-order `PatternPlan` to an independently executable
decision tree.  The target separates constructor tests, child projections,
bound-occurrence tests, variable captures, and binding joins.  In particular,
repeated metavariables are checked by the ordinary `mergeBindings` operation;
they are not weakened to unrelated wildcard captures.

The main theorem is equality of the complete binding list.  It therefore
preserves rejection, every binding value, repeated-variable consistency, and
the observable ordering of the binding carrier.  Sharing equivalent target
subtrees is a later semantics-preserving optimization; this file establishes
the unshared semantic reference first.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PatternPlanBindingDecisionCompilation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation

namespace FirstOrder

export Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
  (PatternPlan patternPlansWork)

end FirstOrder

/-! ## Target decision language -/

/-- A stable route from the root subject to one ordered application child. -/
inductive AccessPath where
  | root
  | child (parent : AccessPath) (index : Nat)
deriving DecidableEq, Repr

/-- Follow one target access path.  Projection failure is ordinary matcher
rejection, never an exceptional or invented result. -/
def AccessPath.project? : AccessPath → Pattern → Option Pattern
  | .root, subject => some subject
  | .child parent index, subject => do
      let focused ← parent.project? subject
      match focused with
      | .apply _ children => children[index]?
      | _ => none

/-- Binding-producing decision trees over explicit subject projections. -/
inductive Decision where
  | succeed
  | capture (path : AccessPath) (name : String)
  | checkBound (path : AccessPath) (expected : Nat)
  | checkConstructor (path : AccessPath) (expected : String) (arity : Nat)
      (children : Decision)
  | join (head tail : Decision)
deriving Repr

/-- Execute the target decision tree independently of `PatternPlan.run`.
`join` deliberately uses the canonical binding merge, retaining its exact
list order and its equality check for repeated names. -/
def Decision.eval : Decision → Pattern → List Bindings
  | .succeed, _ => [[]]
  | .capture path name, subject =>
      match path.project? subject with
      | some focused => [[(name, focused)]]
      | none => []
  | .checkBound path expected, subject =>
      match path.project? subject with
      | some (.bvar actual) => if expected == actual then [[]] else []
      | _ => []
  | .checkConstructor path expected arity children, subject =>
      match path.project? subject with
      | some (.apply actual arguments) =>
          if expected == actual && arity == arguments.length then
            children.eval subject
          else
            []
      | _ => []
  | .join head tail, subject =>
      (head.eval subject).flatMap fun headBindings =>
        (tail.eval subject).filterMap fun tailBindings =>
          mergeBindings headBindings tailBindings

/-! ## Structural compiler -/

mutual
  /-- Compile one pattern relative to its explicit root access path. -/
  def compileAt (path : AccessPath) : FirstOrder.PatternPlan → Decision
    | .metavariable name => .capture path name
    | .bound index => .checkBound path index
    | .application constructor arguments =>
        .checkConstructor path constructor arguments.length
          (compileArgumentsAt path 0 arguments)

  /-- Compile ordered children.  The `join` spine has the same grouping as
  first-order argument matching, so even the binding-list order is retained. -/
  def compileArgumentsAt (parent : AccessPath) (nextIndex : Nat) :
      List FirstOrder.PatternPlan → Decision
    | [] => .succeed
    | argument :: arguments =>
        .join (compileAt (.child parent nextIndex) argument)
          (compileArgumentsAt parent (nextIndex + 1) arguments)
end

/-- Compile a complete first-order pattern at the root subject. -/
def compile (plan : FirstOrder.PatternPlan) : Decision :=
  compileAt .root plan

/-! ## Exact binding semantics -/

private theorem applicationChildren_decreases
    (constructor : String) (plans : List FirstOrder.PatternPlan) :
    2 * patternPlansWork plans + 1 <
      2 * ((.application constructor plans : FirstOrder.PatternPlan).work) := by
  simp only [PatternPlan.work]
  omega

private theorem head_decreases
    (plan : FirstOrder.PatternPlan) (plans : List FirstOrder.PatternPlan) :
    2 * plan.work < 2 * patternPlansWork (plan :: plans) + 1 := by
  rw [patternPlansWork]
  omega

private theorem tail_decreases
    (plan : FirstOrder.PatternPlan) (plans : List FirstOrder.PatternPlan) :
    2 * patternPlansWork plans + 1 <
      2 * patternPlansWork (plan :: plans) + 1 := by
  rw [patternPlansWork]
  have positive := PatternPlan.work_pos plan
  omega

mutual
  /-- A compiled decision at a successfully projected path has exactly the
  source plan's complete binding-list result. -/
  theorem eval_compileAt_of_project?
      (plan : FirstOrder.PatternPlan) (path : AccessPath)
      (root focused : Pattern)
      (projected : path.project? root = some focused) :
      (compileAt path plan).eval root = PatternPlan.run plan focused := by
    cases plan with
    | metavariable name =>
        simp [compileAt, Decision.eval, projected, PatternPlan.run]
    | bound expected =>
        cases focused <;>
          simp [compileAt, Decision.eval, projected,
            PatternPlan.run]
    | application expected plans =>
        cases focused with
        | apply actual subjects =>
            by_cases sameHead : expected == actual
            · by_cases sameLength : plans.length == subjects.length
              · have lengths : plans.length = subjects.length :=
                  beq_iff_eq.mp sameLength
                rw [compileAt, Decision.eval, projected]
                simp only [sameHead, sameLength, Bool.true_and, if_true]
                rw [eval_compileArgumentsAt_of_parent? plans path 0 root
                  actual subjects projected (by omega)]
                simp [PatternPlan.run, sameHead, sameLength]
              · simp [compileAt, Decision.eval, projected,
                  PatternPlan.run, sameHead, sameLength]
            · simp [compileAt, Decision.eval, projected,
                PatternPlan.run, sameHead]
        | _ =>
            simp [compileAt, Decision.eval, projected,
              PatternPlan.run]
  termination_by 2 * plan.work
  decreasing_by
    exact applicationChildren_decreases expected plans

  /-- Ordered-child companion to `eval_compileAt_of_project?`. -/
  theorem eval_compileArgumentsAt_of_parent?
      (plans : List FirstOrder.PatternPlan) (parent : AccessPath)
      (nextIndex : Nat) (root : Pattern) (constructor : String)
      (subjects : List Pattern)
      (projected : parent.project? root =
        some (.apply constructor subjects))
      (complete : nextIndex + plans.length = subjects.length) :
      (compileArgumentsAt parent nextIndex plans).eval root =
        runPlans plans (subjects.drop nextIndex) := by
    cases plans with
    | nil =>
        have exhausted : nextIndex = subjects.length := by
          simpa using complete
        simp [compileArgumentsAt, Decision.eval, exhausted, runPlans]
    | cons plan plans =>
        have inBounds : nextIndex < subjects.length := by
          simp at complete
          omega
        have childProjected :
            (AccessPath.child parent nextIndex).project? root =
              some subjects[nextIndex] := by
          simp [AccessPath.project?, projected,
            List.getElem?_eq_getElem inBounds]
        have tailComplete :
            nextIndex + 1 + plans.length = subjects.length := by
          simp at complete
          omega
        have headExact := eval_compileAt_of_project? plan
          (.child parent nextIndex) root subjects[nextIndex] childProjected
        have tailExact := eval_compileArgumentsAt_of_parent? plans parent
          (nextIndex + 1) root constructor subjects projected tailComplete
        have dropped := List.drop_eq_getElem_cons inBounds
        rw [compileArgumentsAt, Decision.eval, headExact, tailExact, dropped]
        rfl
  termination_by 2 * patternPlansWork plans + 1
  decreasing_by
    · subst_vars
      exact head_decreases plan plans
    · subst_vars
      exact tail_decreases plan plans
end

/-- The independently executable binding decision tree has exactly the
first-order plan interpreter's complete result. -/
theorem eval_compile (plan : FirstOrder.PatternPlan) (subject : Pattern) :
    (compile plan).eval subject = PatternPlan.run plan subject := by
  exact eval_compileAt_of_project? plan .root subject subject rfl

/-- Consequently, compilation also agrees with the canonical MeTTaIL matcher
on the erased source pattern. -/
theorem eval_compile_eq_matchPattern
    (plan : FirstOrder.PatternPlan) (subject : Pattern) :
    (compile plan).eval subject = matchPattern plan.erase subject := by
  rw [eval_compile,
    Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation.run_eq_matchPattern]

/-! ## Discriminating controls -/

private def repeatedPlan : FirstOrder.PatternPlan :=
  .application "pair" [.metavariable "x", .metavariable "x"]

/-- Repeated variables accept equal children and emit one canonical binding. -/
example :
    (compile repeatedPlan).eval
      (.apply "pair" [.apply "a" [], .apply "a" []]) =
        [[("x", .apply "a" [])]] := by
  decide +kernel

/-- Repeated variables reject unequal children; they are not compiled as
independent wildcards. -/
example :
    (compile repeatedPlan).eval
      (.apply "pair" [.apply "a" [], .apply "b" []]) = [] := by
  decide +kernel

private def openNestedPlan : FirstOrder.PatternPlan :=
  .application "box" [
    .application "pair" [.metavariable "x", .metavariable "x"]]

/-- A metavariable nested inside a rigid source pattern remains a real binding
and repeated-variable constraint. -/
example :
    (compile openNestedPlan).eval
      (.apply "box" [
        .apply "pair" [.apply "a" [], .apply "a" []]]) =
      [[("x", .apply "a" [])]] := by
  decide +kernel

/-- Constructor disagreement fails before any binding can escape. -/
example :
    (compile openNestedPlan).eval
      (.apply "foreign-box" [
        .apply "pair" [.apply "a" [], .apply "a" []]]) = [] := by
  decide +kernel

#print axioms eval_compileAt_of_project?
#print axioms eval_compileArgumentsAt_of_parent?
#print axioms eval_compile
#print axioms eval_compile_eq_matchPattern

end Mettapedia.GSLT.LanguageDef.PatternPlanBindingDecisionCompilation
