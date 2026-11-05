import Mettapedia.GSLT.LanguageDef.TemplateScope.Query

/-!
# Template scope: the query corpus

The probe battery of the scope study, run in the model by kernel-checked
computation (`decide +kernel`) under each scope rule of `TemplateScope.Query`:

| rule | query patterns | `case` patterns | lambdas |
|---|---|---|---|
| `ruleH0` | fresh | fresh | lexical |
| `ruleH1` | correlated | correlated | lexical |
| `ruleH2` | unit | unit | lexical |
| `ruleH2q` | unit | unit | introduce their query names |
| `ruleCU` | unit | correlated | clause |

A space is the choice of its facts.  Equations are clauses elaborated as their
own forms (`clauseOf`), curried, with head variables bound by `let`s from the
parameters.  Every form is elaborated under lexical fresh with per-call,
reference activation.  In the answers, `qv y` is the query's slot `$y` left
unbound.

Each row is a probe that was also run on HE, PeTTa and the draft; the HE
answer is quoted in the theorem's documentation.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.QueryCorpus

open Mettapedia.GSLT.LanguageDef.TemplateScope

/-- Spellings of the corpus. -/
inductive QSp where
  | k | v | x | y | a | b | u | f | z | r | pat | d | p1 | uu
  deriving DecidableEq, Repr

/-- Symbols of the corpus. -/
inductive QSy where
  | entry | ka | kb | n1 | n2 | n5 | p | q | Pair | foo | ok | yes | sel | edge | d1 | d2
  | x1 | x2 | lookup | isb | unit | hit
  deriving DecidableEq, Repr

abbrev A := QSrc QSy QSp
abbrev T := Tm QSy (Slot QSp)

/-! ## Authored text -/

def sv (n : QSp) : A := .sv n
def pr (n : QSp) : A := .par n
def k (s : QSy) : A := .sym s
def ap (f a : A) : A := .app f a
def ap2 (h : QSy) (a b : A) : A := ap (ap (k h) a) b
def pair (a b : A) : A := ap2 .Pair a b
def lt (n : QSp) (v b : A) : A := .letS (sv n) v b none
def lm (n : QSp) (b : A) : A := .lam n none b
/-- `(match src pat tmpl)` with no crossing set. -/
def qry (pat src tmpl : A) : A := .query pat src tmpl none
/-- A one-branch `(case v ((pat body)))` with no crossing set. -/
def cs (v pat body : A) : A := .caseS v pat body none

/-- The space `(entry a 1) (entry b 2)`. -/
def entries : A := .alt (ap2 .entry (k .ka) (k .n1)) (ap2 .entry (k .kb) (k .n2))
/-- The space `(p 1) (p 2)`. -/
def ps : A := .alt (ap (k .p) (k .n1)) (ap (k .p) (k .n2))
/-- The space `(q 2)`. -/
def qs : A := ap (k .q) (k .n2)
/-- The space `(sel d1)`. -/
def sels : A := ap (k .sel) (k .d1)
/-- The space `(edge d1 x1) (edge d2 x2)`. -/
def edges : A := .alt (ap2 .edge (k .d1) (k .x1)) (ap2 .edge (k .d2) (k .x2))

/-- `(= (lookup $k) (match entries (entry $k $v) $v))` and
`(= (isb $k) (case b (($k yes))))`. -/
def clauses : QSy → Option A
  | .lookup => some (lm .p1 (lt .k (pr .p1) (qry (ap2 .entry (sv .k) (sv .v)) entries (sv .v))))
  | .isb => some (lm .p1 (lt .k (pr .p1) (cs (k .kb) (sv .k) (k .yes))))
  | _ => none

/-- The program of a rule: each clause elaborated as its own form. -/
def progOf (r : QRule) : QSy → Option T :=
  fun F => (clauses F).map fun body => clauseOf cfgLF [5] .uu .unit (QSrc.toSrc r [] body)

/-- Answers of a query under a rule. -/
def ans (r : QRule) (t : A) : Option (List T) :=
  answersCfg cfgLF (progOf r) 80 (QSrc.toSrc r [] t)

/-! ## Answer notation -/

def kT (s : QSy) : T := .sym s
def apT (f a : T) : T := .app f a
def pairT (a b : T) : T := apT (apT (kT .Pair) a) b
/-- The query's slot `$y`, unbound. -/
def qv (n : QSp) : T := .var (.src ([], n))

/-! ## The battery -/

/-- Q1 (a parameter used in a query): `(lookup b)`. -/
def lookupB : A := ap (.fn .lookup) (k .kb)

/-- Q1 (nested queries): `(match sels (sel $d) (match edges (edge $d $x) $x))`. -/
def nested : A := qry (ap (k .sel) (sv .d)) sels (qry (ap2 .edge (sv .d) (sv .x)) edges (sv .x))

/-- Q1 (sibling queries in `let*`): `(let* (($a (match ps (p $x) $x)) ($b (match qs (q $x) $x))) ($a $b))`. -/
def siblings : A :=
  lt .a (qry (ap (k .p) (sv .x)) ps (sv .x))
    (lt .b (qry (ap (k .q) (sv .x)) qs (sv .x)) (pair (sv .a) (sv .b)))

/-- The siblings inside an explicit `(new ($x) …)`, which binds `$x` for both. -/
def siblingsNew : A := .new [.x] siblings

/-- Q1 (a query's name used after it): `(let $r (match ps (p $x) ok) (Pair $r $x))`. -/
def usedAfter : A := lt .r (qry (ap (k .p) (sv .x)) ps (k .ok)) (pair (sv .r) (sv .x))

/-- Q1 (independent calls of a lambda with a query-local name):
`(let $f (lam z (match entries (entry z $v) $v)) (Pair ($f a) ($f b)))`. -/
def twoCalls : A :=
  lt .f (lm .z (qry (ap2 .entry (pr .z) (sv .v)) entries (sv .v)))
    (pair (ap (sv .f) (k .ka)) (ap (sv .f) (k .kb)))

/-- Q4 (sibling `case`s with the same local name):
`(let* (($a (case (foo 1) (((foo $u) $u)))) ($b (case (foo 2) (((foo $u) $u))))) ($a $b))`. -/
def siblingCases : A :=
  lt .a (cs (ap (k .foo) (k .n1)) (ap (k .foo) (sv .u)) (sv .u))
    (lt .b (cs (ap (k .foo) (k .n2)) (ap (k .foo) (sv .u)) (sv .u)) (pair (sv .a) (sv .b)))

/-- Q4 (`case` on a parameter): `(isb a)`. -/
def isbA : A := ap (.fn .isb) (k .ka)

/-- Q6 (a pattern held in a name): `(let $pat (p $x) (match ps $pat $x))`. -/
def heldPattern : A := lt .pat (ap (k .p) (sv .x)) (qry (sv .pat) ps (sv .x))

/-- The context `(let $f (lam z (Pair HOLE $y)) (let $r ($f ok) (unify $y 5 $r)))`:
the lambda's `$y` is the query's slot, which the later `unify` refines. -/
def stabilityCtx (hole : A) : A :=
  lt .f (lm .z (pair hole (sv .y)))
    (lt .r (ap (sv .f) (k .ok)) (.unify (sv .y) (k .n5) (sv .r)))

/-- The hole `ok`. -/
def holeOk : A := k .ok
/-- The hole `(match ps (p $y) ok)`, a query that writes `$y`. -/
def holeQuery : A := qry (ap (k .p) (sv .y)) ps (k .ok)

/-- `let` stays an arrow: `(let $x 1 (let $x 2 $x))`. -/
def letArrow : A := lt .x (k .n1) (lt .x (k .n2) (sv .x))

/-- Q4 (a `case` after a sibling query that wrote the same name):
`(let $r (match ps (p $x) $x) (case 2 (($x (hit $r)))))`. -/
def caseAfter : A := lt .r (qry (ap (k .p) (sv .x)) ps (sv .x)) (cs (k .n2) (sv .x) (ap (k .hit) (sv .r)))

/-! ## Results

Each table lists the answer bags under the five rules, in the order
`[H0, H1, H2, H2q, CU]`. -/

/-- The five rules of the comparison. -/
def rules : List QRule := [ruleH0, ruleH1, ruleH2, ruleH2q, ruleCU]

/-- Answers of a query under the five rules, in the order of `rules`. -/
def five (t : A) : List (Option (List T)) := rules.map fun r => ans r t

/-- **Query transparency** (the lookup control).  A parameter constrains the
query under every rule but `H0`, where the query's `$k` is its own and both
entries answer (HE: `(2)`). -/
theorem transparency :
    five lookupB = [some [kT .n1, kT .n2], some [kT .n2], some [kT .n2], some [kT .n2],
      some [kT .n2]] := by
  decide +kernel

/-- **Nested queries join** under every rule but `H0` (HE: `(x1)`). -/
theorem nested_join :
    five nested = [some [kT .x1, kT .x2], some [kT .x1], some [kT .x1], some [kT .x1],
      some [kT .x1]] := by
  decide +kernel

/-- **The sibling-join separation.**  HE answers `((2 2))` for the sibling
queries: `$x` is one variable across both.  The `unit` rules
reproduce it; `H1` (and `H0`) do not, and also answer `(1 2)`. -/
theorem sibling_join_separation :
    five siblings = [some [pairT (kT .n1) (kT .n2), pairT (kT .n2) (kT .n2)],
      some [pairT (kT .n1) (kT .n2), pairT (kT .n2) (kT .n2)],
      some [pairT (kT .n2) (kT .n2)], some [pairT (kT .n2) (kT .n2)],
      some [pairT (kT .n2) (kT .n2)]] := by
  decide +kernel

/-- `H1` and `H2` differ on the sibling queries. -/
theorem sibling_join_H1_ne_H2 : ans ruleH1 siblings ≠ ans ruleH2 siblings := by
  decide +kernel

/-- **An explicit binder joins the siblings under `H1`.**  `(new ($x) …)` around
the sibling queries introduces `$x` for both: correlated patterns refer to it.
Under `H0` the patterns still make `$x` new. -/
theorem sibling_join_by_new :
    five siblingsNew = [some [pairT (kT .n1) (kT .n2), pairT (kT .n2) (kT .n2)],
      some [pairT (kT .n2) (kT .n2)], some [pairT (kT .n2) (kT .n2)],
      some [pairT (kT .n2) (kT .n2)], some [pairT (kT .n2) (kT .n2)]] := by
  decide +kernel

/-- A name a query binds is the unit's name after it under the `unit` rules (HE:
`(Pair ok 1) (Pair ok 2)`, the idiom of PeTTa's `greedy_chess`), and stays the
query's own under `H0` and `H1`. -/
theorem used_after :
    five usedAfter = [some [pairT (kT .ok) (qv .x), pairT (kT .ok) (qv .x)],
      some [pairT (kT .ok) (qv .x), pairT (kT .ok) (qv .x)],
      some [pairT (kT .ok) (kT .n1), pairT (kT .ok) (kT .n2)],
      some [pairT (kT .ok) (kT .n1), pairT (kT .ok) (kT .n2)],
      some [pairT (kT .ok) (kT .n1), pairT (kT .ok) (kT .n2)]] := by
  decide +kernel

/-- **Independent calls.**  A lambda whose query has a local name, called twice:
the clause-level rule with lexical lambdas (`H2`) shares the name between the
calls and has no answer; the rules that place it in the query (`H0`, `H1`) or
in the lambda (`H2q`, `CU`) answer `(Pair 1 2)`. -/
theorem independent_calls :
    five twoCalls = [some [pairT (kT .n1) (kT .n2)], some [pairT (kT .n1) (kT .n2)], some [],
      some [pairT (kT .n1) (kT .n2)], some [pairT (kT .n1) (kT .n2)]] := by
  decide +kernel

/-- **Sibling `case`s capture each other's local name** when `case` patterns are
the unit's (HE and PeTTa: no answer).  Branch names
that are the construct's own (`fresh`, `correlated`) answer `(Pair 1 2)`. -/
theorem sibling_cases :
    five siblingCases = [some [pairT (kT .n1) (kT .n2)], some [pairT (kT .n1) (kT .n2)],
      some [], some [], some [pairT (kT .n1) (kT .n2)]] := by
  decide +kernel

/-- **`case` on a parameter.**  `(isb a)` with `(= (isb $k) (case b (($k yes))))`:
the branch matches whatever `b` is under `H0`; the parameter constrains it under
the other rules (HE answers `no`, from its second branch). -/
theorem case_transparency :
    five isbA = [some [kT .yes], some [], some [], some [], some []] := by
  decide +kernel

/-- **A pattern held in a name** (Q6).  Under `H0` the query's `$pat` is a new
name: it matches every fact, and the template's `$x` stays unbound (the draft
answers one `$x` for every atom of `&self`).  Correlated and `unit` patterns
read the held pattern `(p $x)` by identity, as HE does: `(1 2)`. -/
theorem held_pattern :
    five heldPattern = [some [qv .x, qv .x], some [kT .n1, kT .n2], some [kT .n1, kT .n2],
      some [kT .n1, kT .n2], some [kT .n1, kT .n2]] := by
  decide +kernel

/-- **Context stability, the hole `ok`.**  The context's `$y` is the query's
slot, refined to 5 by the later `unify`, under every rule with lexical
lambdas and under `H2q`. -/
theorem context_stability_ok :
    [ruleH0, ruleH1, ruleH2, ruleH2q].map (fun r => ans r (stabilityCtx holeOk)) =
      List.replicate 4 (some [pairT (kT .ok) (kT .n5)]) := by
  decide +kernel

/-- **Context stability, the hole a query that writes `$y`.**
* `H0` and `H1` keep the context's `$y` where it was: the query's `$y` is its
  own, and the later `unify` still refines the context's `$y` to 5;
* `H2` keeps it too: the query refines the same slot, which then conflicts
  with 5, so there is no answer;
* `H2q` and `CU` move it into the lambda, which now introduces `$y`: the later
  `unify` no longer reaches it, and the answers carry the query's 1 and 2.

Under `H2q` the binder of an occurrence of the context depends on what is
plugged into the hole. -/
theorem context_stability_query :
    five (stabilityCtx holeQuery) = [some [pairT (kT .ok) (kT .n5), pairT (kT .ok) (kT .n5)],
      some [pairT (kT .ok) (kT .n5), pairT (kT .ok) (kT .n5)], some [],
      some [pairT (kT .ok) (kT .n1), pairT (kT .ok) (kT .n2)],
      some [pairT (kT .ok) (kT .n1), pairT (kT .ok) (kT .n2)]] := by
  decide +kernel

/-- **Clause units change the lambda fragment.**  Under `CU` a lambda introduces
the names it writes that no enclosing binder introduced, so the context's `$y`
in `(lam z (Pair ok $y))` is the lambda's own and the later `unify` does not
reach it: `CU` is not conservative over lexical fresh. -/
theorem clause_units_not_conservative :
    ans ruleCU (stabilityCtx holeOk) ≠ some [pairT (kT .ok) (kT .n5)] := by
  decide +kernel

/-- **`let` stays an arrow** under every rule: `(let $x 1 (let $x 2 $x))`
answers 2 (HE: no answer). -/
theorem let_arrow : five letArrow = List.replicate 5 (some [kT .n2]) := by
  decide +kernel

/-- **A `case` after a sibling query.**  HE answers `((miss 1) (hit 2))`: its
`case` pattern `$x` is the clause's `$x`, which the query bound.  A `case`
whose pattern is the unit's (`H2`, `H2q`) does the same: only `(hit 2)`.  A
`case` whose new names are its own (`H0`, `H1`, `CU`) matches 2 in both
branches of the query: `(hit 1) (hit 2)`.  This is the price of keeping sibling
`case`s apart (`sibling_cases`). -/
theorem case_after :
    five caseAfter = [some [apT (kT .hit) (kT .n1), apT (kT .hit) (kT .n2)],
      some [apT (kT .hit) (kT .n1), apT (kT .hit) (kT .n2)], some [apT (kT .hit) (kT .n2)],
      some [apT (kT .hit) (kT .n2)],
      some [apT (kT .hit) (kT .n1), apT (kT .hit) (kT .n2)]] := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.TemplateScope.QueryCorpus
