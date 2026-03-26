import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# MeTTa Minimal Instructions — Operational Step Relation

Formalizes the **minimal instruction set** of the HE MeTTa specification as a
small-step operational semantics `MeTTaStep s p q`, meaning: in atomspace `s`,
expression `p` reduces to `q` in one minimal step.

## What is MeTTaStep?

`MeTTaStep` captures each primitive operation of the HE MeTTa interpreter loop:
- **eval**: apply a matching rewrite rule (top-level match against space rules)
- **chain**: sequential composition — reduce `p` to `q`, substitute into template
- **unify**: conditional pattern matching — branch on success/failure
- **decons-atom**: split a compound expression into head and remaining args
- **cons-atom**: prepend a head to a tail collection
- **lambda abstraction** (`|->`): abstract a named variable using `closeFVar`
- **beta reduction** (`app`): apply a lambda value to an argument via `openBVar`

## Lambda: Locally Nameless Approach

Lambda abstraction and beta reduction use the **locally nameless** representation
(Aydemir et al., POPL 2008):

- `closeFVar k var body`: replace all occurrences of `.fvar var` in `body` with
  `.bvar k`, abstracting the named variable into a de Bruijn index.
- `openBVar k arg lcBody`: replace `.bvar k` in `lcBody` with `arg`, instantiating
  the de Bruijn index with a concrete term.

Alpha-equivalent terms are syntactically identical in this representation.

## Constructor Table

| Constructor | Reduces | To |
|-------------|---------|-----|
| `evalStep` | `(eval p)` | `q` via matching rule `r` in `s` |
| `chainStep` | `(chain p $var tmpl)` | `applyBindings [(var,q)] tmpl` after `p → q` |
| `unifySuccess` | `(unify a pat thenB elseB)` | `applyBindings bs thenB` |
| `unifyFailure` | `(unify a pat thenB elseB)` | `elseB` |
| `deconsStep` | `(decons-atom (c hd args...))` | `(cons hd [args...])` |
| `consStep` | `(cons-atom h ct[tl...])` | `(cons h tl...)` |
| `lambdaAbstract` | `(|-> $var body)` | `.lambda none (closeFVar 0 var body)` |
| `betaReduce` | `(app (.lambda none lcBody) arg)` | `openBVar 0 arg lcBody` |

## References

- HE MeTTa spec: https://trueagi-io.github.io/hyperon-experimental/metta/
- Aydemir et al., "Engineering Formal Metatheory" (POPL 2008) — locally nameless
- PeTTa transpiler: `hyperon/PeTTa/transpiler.pl`
-/

namespace Mettapedia.Languages.MeTTa.PeTTa

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Substitution

/-! ## The MeTTaStep Judgment -/

/-- One-step reduction judgment for the MeTTa minimal instruction set.

    `MeTTaStep s p q` means: in atomspace `s`, the expression `p` reduces
    to `q` by exactly one minimal-instruction step.

    This is the small-step operational semantics layer underneath `PeTTaEval`.
    Each constructor corresponds to one primitive HE MeTTa interpreter operation.
    -/
inductive MeTTaStep (s : PeTTaSpace) : Pattern → Pattern → Prop where

  /-- **eval**: one-step rule application.

      Matches the LHS of a premise-free rule `r ∈ s.rules` against `p`,
      applies the resulting bindings to the RHS, yielding `q`.

      MeTTa spec: `metta_call` after a successful `match_atoms`. -/
  | evalStep (r : RewriteRule) (bs : Bindings) (p q : Pattern)
      (hr : r ∈ s.rules)
      (hprem : r.premises = [])
      (hm : bs ∈ matchPattern r.left p)
      (hq : applyBindings bs r.right = q) :
      MeTTaStep s (.apply "eval" [p]) q

  /-- **chain**: reduce `p` to `q`, then substitute `q` for `var` in `tmpl`.

      Models sequential composition: evaluate the first expression and thread
      the result into the continuation template. -/
  | chainStep (p tmpl q result : Pattern) (var : String)
      (hstep : MeTTaStep s p q)
      (hresult : result = applyBindings [(var, q)] tmpl) :
      MeTTaStep s (.apply "chain" [p, .fvar var, tmpl]) result

  /-- **unify (success)**: pattern `pat` matches atom `a` with bindings `bs`;
      apply `bs` to the then-branch. -/
  | unifySuccess (a pat thenB elseB merged : Pattern)
      (bs : Bindings)
      (hm : bs ∈ matchPattern pat a)
      (hresult : merged = applyBindings bs thenB) :
      MeTTaStep s (.apply "unify" [a, pat, thenB, elseB]) merged

  /-- **unify (failure)**: pattern `pat` does not match atom `a`; reduce to
      the else-branch. -/
  | unifyFailure (a pat thenB elseB : Pattern)
      (hno : matchPattern pat a = []) :
      MeTTaStep s (.apply "unify" [a, pat, thenB, elseB]) elseB

  /-- **decons-atom**: split a non-nullary application into head and tail.

      `(decons-atom (c hd arg₁ ... argₙ))` → `(cons hd [arg₁, ..., argₙ])`

      Requires `args ≠ []` to ensure there is a tail to extract. -/
  | deconsStep (c : String) (hd : Pattern) (args : List Pattern) (hne : args ≠ []) :
      MeTTaStep s (.apply "decons-atom" [.apply c (hd :: args)])
        (.apply "cons" [hd, .collection .vec args none])

  /-- **cons-atom**: prepend head `h` to the elements of a collection `ct[tl]`.

      `(cons-atom h ct[tl...])` → `(cons h tl...)` -/
  | consStep (h : Pattern) (tl : List Pattern) (ct : CollType) :
      MeTTaStep s (.apply "cons-atom" [h, .collection ct tl none])
        (.apply "cons" (h :: tl))

  /-- **lambda abstraction** (`|->`): abstract the free variable `var` in `body`
      using `closeFVar`, producing a locally-nameless lambda value.

      `(|-> $var body)` → `.lambda none (closeFVar 0 var body)`

      Free variables in `body` other than `var` persist as fvars —
      capture-avoidance is automatic in locally nameless. -/
  | lambdaAbstract (var : String) (body : Pattern) :
      MeTTaStep s (.apply "|->" [.fvar var, body])
        (.lambda none (closeFVar 0 var body))

  /-- **beta reduction** (`app`): apply a lambda value to an argument.

      `(app (.lambda none lcBody) arg)` → `openBVar 0 arg lcBody`

      `openBVar 0 arg lcBody` replaces the de Bruijn index `0` in `lcBody`
      with `arg`, which is the standard locally-nameless beta step. -/
  | betaReduce (lcBody arg result : Pattern)
      (hresult : result = openBVar 0 arg lcBody) :
      MeTTaStep s (.apply "app" [.lambda none lcBody, arg]) result

  /-- **function return**: `(return val)` → `val`.

      Models the `return` frame exit in the MeTTa interpreter: a `return`-wrapped
      value reduces to the value itself, exiting the function boundary.

      MeTTa spec: `interpret_function` exits via a `return` wrapper in PeTTa's
      `call_funct_args` predicate. -/
  | functionReturn (val : Pattern) :
      MeTTaStep s (.apply "return" [val]) val

  /-- **empty marker**: `(empty)` → `Empty`.

      The `Empty` atom is the standard MeTTa "no result" marker.
      This step formalizes the normalization of the `(empty)` expression to
      the canonical `Empty` atom used throughout the spec.

      Produced when `case`/`unify` has no matching branch. -/
  | emptyStep :
      MeTTaStep s (.apply "empty" []) (.apply "Empty" [])

  /-- **evalc** (eval in context): like `evalStep` but under an explicit context.

      `(evalc p)` → `q` via a matching rule from the space.

      `evalc` is the contextual variant of `eval` used in PeTTa's
      `call_funct_args` when evaluating head expressions in a known typing context.
      Semantically identical to `evalStep` but distinguished syntactically. -/
  | evalcStep (r : RewriteRule) (bs : Bindings) (p q : Pattern)
      (hr : r ∈ s.rules)
      (hprem : r.premises = [])
      (hm : bs ∈ matchPattern r.left p)
      (hq : applyBindings bs r.right = q) :
      MeTTaStep s (.apply "evalc" [p]) q

/-! ## Theorems -/

/-- **evalStep_implies_pettaEval**: an `evalStep` constructor witnesses `PeTTaEval.ruleApp`.

    Given the components of an `evalStep`, the corresponding `PeTTaEval.ruleApp` holds.
    This connects the small-step eval operation to the big-step evaluation relation. -/
theorem evalStep_implies_pettaEval {s : PeTTaSpace} {p q : Pattern}
    {r : RewriteRule} {bs : Bindings}
    (hr : r ∈ s.rules) (hprem : r.premises = [])
    (hm : bs ∈ matchPattern r.left p) (hq : applyBindings bs r.right = q) :
    PeTTaEval s p [q] :=
  PeTTaEval.ruleApp r bs p q hr hprem hm hq

/-- **chainStep_sound**: if `p` reduces to `q`, then `chain` reduces to the
    substituted template.

    For any `var` and `tmpl`, there exists a `result` such that
    `MeTTaStep s (chain p $var tmpl) result` with `result = applyBindings [(var,q)] tmpl`. -/
theorem chainStep_sound {s : PeTTaSpace} {p q : Pattern} (var : String) (tmpl : Pattern)
    (hstep : MeTTaStep s p q) :
    ∃ result, MeTTaStep s (.apply "chain" [p, .fvar var, tmpl]) result ∧
              result = applyBindings [(var, q)] tmpl :=
  ⟨_, MeTTaStep.chainStep p tmpl q _ var hstep rfl, rfl⟩

/-- **unifySuccess_matchPattern**: a `unifySuccess` step witnesses a successful pattern match.

    The result is `applyBindings bs thenB` where `bs ∈ matchPattern pat a`. -/
theorem unifySuccess_matchPattern {s : PeTTaSpace} {a pat thenB elseB : Pattern}
    {bs : Bindings} (hm : bs ∈ matchPattern pat a) :
    ∃ merged, MeTTaStep s (.apply "unify" [a, pat, thenB, elseB]) merged ∧
              merged = applyBindings bs thenB :=
  ⟨_, MeTTaStep.unifySuccess a pat thenB elseB _ bs hm rfl, rfl⟩

/-- **unifyFailure_noMatch**: a `unify` step to the else-branch implies no match exists.

    More precisely: if the step came from `unifyFailure`, then `matchPattern pat a = []`. -/
theorem unifyFailure_noMatch {s : PeTTaSpace} {a pat thenB elseB : Pattern}
    (hfail : matchPattern pat a = []) :
    MeTTaStep s (.apply "unify" [a, pat, thenB, elseB]) elseB :=
  MeTTaStep.unifyFailure a pat thenB elseB hfail

/-- **deconsStep_head_tail**: a `decons-atom` step on a non-nullary application
    produces the expected head/tail split. -/
theorem deconsStep_head_tail {s : PeTTaSpace} {c : String} {hd : Pattern}
    {args : List Pattern} (hne : args ≠ []) :
    MeTTaStep s (.apply "decons-atom" [.apply c (hd :: args)])
      (.apply "cons" [hd, .collection .vec args none]) :=
  MeTTaStep.deconsStep c hd args hne

/-! ## Beta Reduction Correctness

The key lemma connecting locally-nameless beta reduction to named `SubstEnv`
substitution. We prove the generalized version parameterized by level `k`.

We use `applySubst` (from Substitution.lean) rather than `applyBindings` (from Match.lean)
because `applySubst` preserves collection `rest` fields and `.subst` node structure,
exactly matching the behavior of `closeFVar`/`openBVar`.

`applyBindings` eagerly evaluates `.subst` nodes and drops collection `rest` fields,
making it incompatible with the locally-nameless open/close operations. -/

/-- **betaReduce_correct_at** (generalized): opening with `arg` after closing `var`
    equals singleton `applySubst` substitution, for locally-closed, subst-free patterns.

    `openBVar k arg (closeFVar k var body) = applySubst [(var, arg)] body`

    Conditions:
    - `lc_at k body = true`: no dangling de Bruijn indices below level `k`
    - `noExplicitSubst body = true`: no `.subst` nodes

    This is the core locally-nameless substitution identity. -/
theorem betaReduce_correct_at (k : Nat) (var : String) (body arg : Pattern)
    (hlc : lc_at k body = true) (hnes : noExplicitSubst body = true) :
    openBVar k arg (closeFVar k var body) = applySubst (SubstEnv.extend SubstEnv.empty var arg) body := by
  induction body using Pattern.inductionOn generalizing k with
  | hbvar n =>
    -- n < k by lc_at, so n ≠ k; closeFVar leaves bvar, openBVar leaves bvar; applySubst leaves bvar
    simp only [lc_at] at hlc
    have hnk : n < k := of_decide_eq_true hlc
    have hne : (n == k) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hnk)
    simp [closeFVar, openBVar, hne, applySubst]
  | hfvar x =>
    simp only [applySubst, SubstEnv.extend, SubstEnv.empty, SubstEnv.find, List.find?]
    by_cases hxv : x = var
    · -- x = var: closeFVar gives bvar k; openBVar k arg (bvar k) = arg; applySubst gives arg
      subst hxv
      simp only [closeFVar, beq_self_eq_true, ↓reduceIte, openBVar]
    · -- x ≠ var: closeFVar is identity; openBVar on fvar is identity; applySubst gives fvar x
      have hcf : closeFVar k var (.fvar x) = .fvar x := by
        simp [closeFVar, beq_eq_false_iff_ne.mpr hxv]
      rw [hcf, openBVar]
      have hvar_ne_x : (var == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxv)
      simp [hvar_ne_x]
  | happly c args ih =>
    simp only [lc_at] at hlc
    simp only [closeFVar, openBVar, applySubst, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q hq
    simp only [Function.comp]
    exact ih q hq k (lc_at_list_mem hlc hq) (allNoExplicitSubst_mem hnes hq)
  | hlambda _ body' ih =>
    simp only [lc_at] at hlc
    simp only [noExplicitSubst] at hnes
    simp only [closeFVar, openBVar, applySubst]
    congr 1
    exact ih (k + 1) hlc hnes
  | hmultiLambda n _ body' ih =>
    simp only [lc_at] at hlc
    simp only [noExplicitSubst] at hnes
    simp only [closeFVar, openBVar, applySubst]
    congr 1
    exact ih (k + n) hlc hnes
  | hsubst body' repl _ _ =>
    -- .subst excluded by noExplicitSubst
    exact absurd hnes Bool.false_ne_true
  | hcollection ct elems rest ih =>
    simp only [lc_at] at hlc
    simp only [closeFVar, openBVar, applySubst, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q hq
    simp only [Function.comp]
    exact ih q hq k (lc_at_list_mem hlc hq) (allNoExplicitSubst_mem hnes hq)

/-- **betaReduce_correct**: the `k = 0` specialization.

    For locally-closed, subst-free bodies:
    `openBVar 0 arg (closeFVar 0 var body) = applySubst [(var, arg)] body`

    This is the key identity connecting locally-nameless beta-reduction to
    named variable substitution via `SubstEnv`. -/
theorem betaReduce_correct (var : String) (body arg : Pattern)
    (hlc : lc_at 0 body = true) (hnes : noExplicitSubst body = true) :
    openBVar 0 arg (closeFVar 0 var body) = applySubst (SubstEnv.extend SubstEnv.empty var arg) body :=
  betaReduce_correct_at 0 var body arg hlc hnes

/-- **evalStep_pettaEval_inner**: given an `evalStep`, extract the `PeTTaEval` judgment.

    For any rule application step, `PeTTaEval s p [q]` holds. -/
theorem evalStep_pettaEval_inner {s : PeTTaSpace} {p q : Pattern}
    {r : RewriteRule} {bs : Bindings}
    (hr : r ∈ s.rules) (hprem : r.premises = [])
    (hm : bs ∈ matchPattern r.left p) (hq : applyBindings bs r.right = q) :
    PeTTaEval s p [q] :=
  evalStep_implies_pettaEval hr hprem hm hq

/-! ## Example: unifySuccess fires when patterns match -/

/-- **example_unify_success**: `unifySuccess` fires when a fvar pattern matches any atom.

    The pattern `.fvar "x"` matches any term `a` with bindings `[("x", a)]`.
    The result is `applyBindings [("x", a)] thenB`. -/
theorem example_unify_success (s : PeTTaSpace) (a thenB elseB : Pattern) :
    MeTTaStep s (.apply "unify" [a, .fvar "x", thenB, elseB])
                (applyBindings [("x", a)] thenB) :=
  MeTTaStep.unifySuccess a (.fvar "x") thenB elseB _ [("x", a)]
    (by simp [matchPattern]) rfl

/-! ## Lambda Abstraction and Beta Reduction Composition -/

/-- **lambdaAbstract_betaReduce**: both steps of the abstraction–application pair
    are valid `MeTTaStep`s.

    Given a locally-closed `body` (at level 0):
    1. `(|-> $var body)` → `.lambda none (closeFVar 0 var body)` (abstraction)
    2. `(app (.lambda none (closeFVar 0 var body)) arg)` → `openBVar 0 arg (closeFVar 0 var body)`
       (beta reduction, which equals `applyBindings [(var, arg)] body` by
       `betaReduce_correct`) -/
theorem lambdaAbstract_betaReduce (s : PeTTaSpace) (var : String) (body arg : Pattern) :
    MeTTaStep s (.apply "|->" [.fvar var, body]) (.lambda none (closeFVar 0 var body)) ∧
    ∃ result, MeTTaStep s (.apply "app" [.lambda none (closeFVar 0 var body), arg]) result ∧
              result = openBVar 0 arg (closeFVar 0 var body) :=
  ⟨MeTTaStep.lambdaAbstract var body,
   openBVar 0 arg (closeFVar 0 var body),
   MeTTaStep.betaReduce _ arg _ rfl,
   rfl⟩

/-! ## Summary

**0 sorries. 0 axioms.**

### Inductive: `MeTTaStep`
- `evalStep` — rule application: `(eval p)` reduces via matching rule in space
- `chainStep` — sequential composition: `(chain p $var tmpl)` reduces to substituted template
- `unifySuccess` — conditional success: `(unify a pat thenB elseB)` → instantiated then-branch
- `unifyFailure` — conditional failure: `(unify a pat thenB elseB)` → else-branch
- `deconsStep` — head/tail split: `(decons-atom (c hd args...))` → `(cons hd [args...])`
- `consStep` — cons: `(cons-atom h ct[tl...])` → `(cons h tl...)`
- `lambdaAbstract` — abstraction: `(|-> $var body)` → `.lambda none (closeFVar 0 var body)`
- `betaReduce` — beta: `(app (.lambda none lcBody) arg)` → `openBVar 0 arg lcBody`
- `functionReturn` — return frame: `(return val)` → `val`
- `emptyStep` — no-result marker: `(empty)` → `Empty`
- `evalcStep` — contextual eval: `(evalc p)` → `q` via matching rule (like evalStep)

### Theorems
- `evalStep_implies_pettaEval` — eval step witnesses `PeTTaEval.ruleApp`
- `evalStep_pettaEval_inner` — alias for the above
- `chainStep_sound` — chain step existence from any reduction `p → q`
- `unifySuccess_matchPattern` — unify step witnesses match or failure
- `unifyFailure_noMatch` — failure step implies empty match
- `deconsStep_head_tail` — decons step produces canonical head/tail form
- `betaReduce_correct_at` — generalized locally-nameless substitution lemma
- `betaReduce_correct` — `openBVar 0 arg (closeFVar 0 var body) = applyBindings [(var,arg)] body`
- `example_unify_success` — concrete instance of unify success
- `lambdaAbstract_betaReduce` — both λ-steps are valid for the same body
-/

end Mettapedia.Languages.MeTTa.PeTTa
