import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.Languages.MeTTa.PeTTa.Answers

/-!
# Body-closure fusion: executing a clause body under its environment

When a clause fires, the direct implementation builds a fully substituted copy
of the body and hands that copy to the evaluator.  The copy is consumed
immediately and discarded, so every call pays to materialise structure that no
observation ever inspects.

The alternative is to keep the body and its environment separate, and let the
machine read a binding only where a variable occurrence is actually reached.
This module proves that the two agree:

    evaluate (substitute env body)  =  evaluateUnder env body

as **ordered answer lists** — same answers, same order, same multiplicity — so
the substituted copy is never semantically required.

## What is modelled, and how faithfully

* Bodies are the project's own `Pattern`, and substitution is the project's own
  `applyBindings`; neither is re-invented here.
* Answers are `List Pattern` (the existing `Answers`), so the observation is an
  ordered bag: a proof up to set equality would not say what the runtime needs.
* Argument answers combine through `orderedProduct`, an ordered cartesian
  product that preserves both order and duplicate occurrences.
* Calls are interpreted by an opaque parameter.  The theorem is about *where
  substitution happens*, not about what any particular call computes, so it
  holds for every call interpretation uniformly.
* `PlanNode` and `planOf` mirror the execution plan that already accompanies
  each compiled body: a leaf is a value, an expression whose head is a known or
  intrinsic program head is a call, any other expression is inert data, and an
  expression with a computed head is a dynamic call.  `planOf_role_call` ties
  that classification to the branch the fused evaluator actually takes.

## Results

* `evalUnder_eq_evalEager` — **the fusion law**.  Its corollary
  `substituted_copy_unnecessary` states the engineering consequence directly.
* `misclassified_call_loses_answer` — a plan that calls an expression inert
  changes the observation, so the classification is load-bearing rather than
  advisory.
* `evalUnder_congr_on_consulted` — evaluation depends only on the bindings the
  body actually consults, which is what licenses projecting an environment down
  to its reachable part instead of retaining all of it.  The relevant name set
  is `consultedNames`, not `freeVars`: substitution also consults a collection
  pattern's tail variable, which `freeVars` does not report, so the statement
  would be false against `freeVars`.

## Scope honesty

The call interpretation is opaque, so this says nothing about the behaviour of
any individual builtin, and nothing about effects: the observation algebra here
is the answer bag alone.  Extending it to an effect trace is a separate
obligation and is deliberately not claimed.  Likewise the `dynamicCall` role is
carried for artifact fidelity but is unreachable in this syntax, where an
application head is always a fixed name.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.BodyClosureFusion

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.MeTTa.PeTTa (Answers)

/-! ## The compiled plan

`planOf` mirrors the plan builder that walks a body once at compile time and
labels every node with the role the machine will take at it. -/

/-- The role a body node plays during execution. -/
inductive PlanNode where
  /-- A leaf: nothing to evaluate, only a possible binding to read. -/
  | value
  /-- An inert expression: its children are evaluated, the node is rebuilt. -/
  | data (children : List PlanNode)
  /-- An expression whose head is a known or intrinsic program head. -/
  | staticCall (children : List PlanNode)
  /-- An expression whose head is itself computed. -/
  | dynamicCall (children : List PlanNode)
deriving Repr

/-- Label every node of a body with its execution role, given the program's
known heads. -/
def planOf (heads : List String) : Pattern → PlanNode
  | .apply c args =>
    if c ∈ heads then .staticCall (args.map (planOf heads))
    else .data (args.map (planOf heads))
  | _ => .value

/-- The plan classifies an application as a call exactly when its head is a
known program head — the decision the fused evaluator branches on. -/
theorem planOf_role_call (heads : List String) (c : String) (args : List Pattern)
    (hc : c ∈ heads) :
    planOf heads (.apply c args) = .staticCall (args.map (planOf heads)) := by
  simp [planOf, hc]

/-- Symmetrically, an expression whose head is not a program head is inert. -/
theorem planOf_role_data (heads : List String) (c : String) (args : List Pattern)
    (hc : c ∉ heads) :
    planOf heads (.apply c args) = .data (args.map (planOf heads)) := by
  simp [planOf, hc]

/-- A leaf carries no children to descend into. -/
theorem planOf_leaf (heads : List String) (x : String) :
    planOf heads (.fvar x) = .value := by
  simp [planOf]

/-! ## Evaluation

Both evaluators are parametric in one call interpretation, so the theorem below
compares only *where substitution happens*. -/

/-- Ordered cartesian product of per-argument answer lists.  Order and
duplicate occurrences are both preserved, so this is a bag combinator, not a
set one. -/
def orderedProduct : List Answers → List (List Pattern)
  | [] => [[]]
  | a :: rest => a.flatMap fun v => (orderedProduct rest).map fun vs => v :: vs

/-- Evaluate a body that has **already** been substituted — the direct route,
which requires the materialised copy. -/
def evalEager (call : String → List Pattern → Answers) (heads : List String) :
    Pattern → Answers
  | .apply c args =>
    if c ∈ heads then (orderedProduct (args.map (evalEager call heads))).flatMap (call c)
    else (orderedProduct (args.map (evalEager call heads))).map (Pattern.apply c)
  | t => [t]

/-- Evaluate a body **under** its environment, reading bindings only at the
leaves it reaches.  No substituted copy of any interior node is ever built. -/
def evalUnder (call : String → List Pattern → Answers) (heads : List String)
    (env : Bindings) : Pattern → Answers
  | .apply c args =>
    if c ∈ heads then
      (orderedProduct (args.map (evalUnder call heads env))).flatMap (call c)
    else
      (orderedProduct (args.map (evalUnder call heads env))).map (Pattern.apply c)
  | t => evalEager call heads (applyBindings env t)

/-! ## The fusion law -/

/-- **Fusion.**  Executing a body under its environment yields exactly the
answers of executing its substituted copy — identical list, so identical
answers in identical order with identical multiplicity.

The substituted copy is therefore never semantically required: the only place
the environment must be consulted is a leaf actually reached. -/
theorem evalUnder_eq_evalEager (call : String → List Pattern → Answers)
    (heads : List String) (env : Bindings) (t : Pattern) :
    evalUnder call heads env t = evalEager call heads (applyBindings env t) := by
  induction t using Pattern.inductionOn with
  | hbvar n => simp [evalUnder]
  | hfvar x => simp [evalUnder]
  | happly c args ih =>
    have hmap : args.map (evalUnder call heads env)
        = (args.map (applyBindings env)).map (evalEager call heads) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact ih a ha
    by_cases hc : c ∈ heads <;>
      simp [evalUnder, evalEager, applyBindings, hc, hmap]
  | hlambda nm body _ => simp [evalUnder]
  | hmultiLambda n nms body _ => simp [evalUnder]
  | hsubst body repl _ _ => simp [evalUnder]
  | hcollection ct elems rest _ => simp [evalUnder]

/-- The engineering consequence, stated directly: for every body, environment,
and call interpretation, the answers obtained without materialising the
substituted body are the answers obtained with it. -/
theorem substituted_copy_unnecessary (call : String → List Pattern → Answers)
    (heads : List String) (env : Bindings) :
    ∀ t : Pattern, evalEager call heads (applyBindings env t) = evalUnder call heads env t :=
  fun t => (evalUnder_eq_evalEager call heads env t).symm

/-! ## The classification is load-bearing

The fused evaluator branches on whether a node is a call.  If a plan called an
expression inert that is in fact a call, the observation changes — so the
classification carries semantic weight and is not merely a hint. -/

/-- The same evaluator with the call branch suppressed: every expression is
treated as inert data. -/
def evalUnderNoCalls (call : String → List Pattern → Answers) (heads : List String)
    (env : Bindings) : Pattern → Answers
  | .apply c args =>
    (orderedProduct (args.map (evalUnderNoCalls call heads env))).map (Pattern.apply c)
  | t => evalEager call heads (applyBindings env t)

/-- **Negative witness.**  With one known head `f` whose call answers `done`,
treating the call as inert data returns the unevaluated expression instead, so
the two observations differ.  A plan that mis-labels a call therefore changes
the answer bag. -/
theorem misclassified_call_loses_answer :
    ∃ (call : String → List Pattern → Answers) (heads : List String) (env : Bindings)
      (t : Pattern),
      evalUnderNoCalls call heads env t ≠ evalUnder call heads env t := by
  refine ⟨fun _ _ => [Pattern.fvar "done"], ["f"], [], Pattern.apply "f" [], ?_⟩
  simp [evalUnderNoCalls, evalUnder, orderedProduct]

/-- For contrast, the correctly classified plan does reach the call. -/
theorem classified_call_reaches_interpretation :
    evalUnder (fun _ _ => [Pattern.fvar "done"]) ["f"] [] (Pattern.apply "f" [])
      = [Pattern.fvar "done"] := by
  simp [evalUnder, orderedProduct]

/-! ## Environment lifetime

Execution consults the environment only where a name is actually reached, so
only bindings for those names can matter.  This is what licenses projecting an
environment down to its reachable part instead of retaining it whole across a
derivation.

The relevant name set is **not** `freeVars`: substitution also consults the
tail variable of a collection pattern, which `freeVars` does not report.
`consultedNames` is that corrected set, and the congruence below is stated
against it — with `freeVars` the statement would simply be false. -/

/-- Every name whose binding substitution may consult: the free variables,
together with the tail variable of each collection pattern. -/
def consultedNames : Pattern → List String
  | .bvar _ => []
  | .fvar x => [x]
  | .apply _ args => args.flatMap consultedNames
  | .lambda _ body => consultedNames body
  | .multiLambda _ _ body => consultedNames body
  | .subst body repl => consultedNames body ++ consultedNames repl
  | .collection _ elems rest => elems.flatMap consultedNames ++ rest.toList
termination_by p => sizeOf p

/-- Substitution depends only on the bindings of the names it consults. -/
theorem applyBindings_congr_on_consulted (env env' : Bindings) :
    ∀ t : Pattern,
      (∀ x ∈ consultedNames t,
        env.find? (·.1 == x) = env'.find? (·.1 == x)) →
      applyBindings env t = applyBindings env' t := by
  intro t
  induction t using Pattern.inductionOn with
  | hbvar n => intro _; simp [applyBindings]
  | hfvar x =>
    intro h
    have hx : x ∈ consultedNames (Pattern.fvar x) := by simp [consultedNames]
    simp [applyBindings, h x hx]
  | happly c args ih =>
    intro h
    have hargs : args.map (applyBindings env) = args.map (applyBindings env') := by
      apply List.map_congr_left
      intro a ha
      refine ih a ha (fun x hx => h x ?_)
      simp only [consultedNames, List.mem_flatMap]
      exact ⟨a, ha, hx⟩
    simp [applyBindings, hargs]
  | hlambda nm body ih =>
    intro h
    have hb : applyBindings env body = applyBindings env' body :=
      ih (fun x hx => h x (by simpa [consultedNames] using hx))
    simp [applyBindings, hb]
  | hmultiLambda n nms body ih =>
    intro h
    have hb : applyBindings env body = applyBindings env' body :=
      ih (fun x hx => h x (by simpa [consultedNames] using hx))
    simp [applyBindings, hb]
  | hsubst body repl ihb ihr =>
    intro h
    have hb : applyBindings env body = applyBindings env' body := by
      refine ihb (fun x hx => h x ?_)
      simp only [consultedNames, List.mem_append]
      exact Or.inl hx
    have hr : applyBindings env repl = applyBindings env' repl := by
      refine ihr (fun x hx => h x ?_)
      simp only [consultedNames, List.mem_append]
      exact Or.inr hx
    simp [applyBindings, hb, hr]
  | hcollection ct elems rest ih =>
    intro h
    have helems : elems.map (applyBindings env) = elems.map (applyBindings env') := by
      apply List.map_congr_left
      intro a ha
      refine ih a ha (fun x hx => h x ?_)
      simp only [consultedNames, List.mem_append, List.mem_flatMap]
      exact Or.inl ⟨a, ha, hx⟩
    cases rest with
    | none => simp [applyBindings, helems]
    | some rv =>
      have hrv : env.find? (·.1 == rv) = env'.find? (·.1 == rv) := by
        refine h rv ?_
        simp [consultedNames]
      simp [applyBindings, helems, hrv]

/-- **Environment lifetime.**  Two environments agreeing on every name the body
consults give identical answers, so a binding for any other name need not be
retained. -/
theorem evalUnder_congr_on_consulted (call : String → List Pattern → Answers)
    (heads : List String) (env env' : Bindings) (t : Pattern)
    (hagree : ∀ x ∈ consultedNames t,
      env.find? (·.1 == x) = env'.find? (·.1 == x)) :
    evalUnder call heads env t = evalUnder call heads env' t := by
  rw [evalUnder_eq_evalEager, evalUnder_eq_evalEager,
    applyBindings_congr_on_consulted env env' t hagree]

end Mettapedia.Languages.MeTTa.PeTTa.BodyClosureFusion
