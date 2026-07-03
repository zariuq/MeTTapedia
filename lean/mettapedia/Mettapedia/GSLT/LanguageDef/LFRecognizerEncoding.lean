/-
# E2b Route-A' — the LF recognizer re-encoded as a pure `MeTTaIL.Presentation` (in progress, 2026-07-03)

`LFEngineReduce.lean` proved (by `rfl`, axioms `{propext}`) that the certified pure-rewriting
normalizer `MeTTaIL.eval` is kernel-reducible and supports every primitive the recognizer needs:
multi-rule pattern dispatch, Peano arithmetic, and context-descending recursion.  This file begins
the actual re-encoding of `MettaKernel/kernel/lf_recognizer_v0.metta` as pure `.base` rewrites, so
that the universal correspondence `∀ ts, ⟦lf-recognize⟧ ts = recognize ts` (E2b) can be proved
*over the verified engine*, by computation for the corpus and by induction in general.

Discipline: each component is an **orthogonal** rewrite system (disjoint left-hand sides, no
catch-all pattern-variable rule that would over-match a reduced term — the non-determinism / totality
gotcha), and each carries its own `rfl` corpus before the next component builds on it.  Peano
naturals encode both fuel and de Bruijn indices (`0 ↦ Z`, `n+1 ↦ (S n)`); identifiers are distinct
nullary constructors.

This installment: the numeric substrate (`lt`) + **de Bruijn `shift`**, mirroring `LF.shift` /
`lf-shift` clause-for-clause.  `shift` is self-contained (no continuation-passing needed — it is
structural recursion on the AST with a `<`-guard), so it is the right first real brick.

Integrity: 0 sorry / 0 native_decide; corpus closed by `rfl` (kernel computation on the certified
normalizer).
-/
import MeTTaIL.Semantics.Eval

namespace Mettapedia.GSLT.LanguageDef.LFEnc

open MeTTaIL

-- The corpus reductions unfold `eval` through many `oneStep` calls; raise the elaborator's recursion
-- limit for the kernel `rfl`.  This is `maxRecDepth` (an elaboration/whnf stack bound), NOT
-- `native_decide` — every proof below is still kernel-checked.
set_option maxRecDepth 8000

/-! ## Term builders (thin sugar over `AST`) -/

/-- A ground nullary constructor `(c)`. -/
def con0 (s : String) : AST := .sexp (.id s) []
/-- A pattern variable `$v`. -/
def pv (v : String) : AST := .var (.base v)
/-- A base rewrite `lhs ~> rhs` named `name`. -/
def rw (name : String) (lhs rhs : AST) : RewriteDecl := { name := name, rw := .base lhs rhs }

/-- Peano zero / successor (encode fuel and de Bruijn indices alike). -/
def Z : AST := con0 "Z"
def S (n : AST) : AST := .sexp (.id "S") [n]

/-! ## Numeric substrate: strict `<` on Peano naturals, returning `tt`/`ff`.

Four disjoint dispatch rules — exactly the recognizer's `(< $k $c)` guard, Peano-encoded. -/

def ltT (a b : AST) : AST := .sexp (.id "lt") [a, b]

/-- The `lt` rules (reused by every component that needs a `<`-guard). -/
def ltRules : List RewriteDecl := [
    rw "lt-z-s"  (ltT Z (S (pv "m")))          (con0 "tt"),
    rw "lt-z-z"  (ltT Z Z)                      (con0 "ff"),
    rw "lt-s-z"  (ltT (S (pv "n")) Z)           (con0 "ff"),
    rw "lt-s-s"  (ltT (S (pv "n")) (S (pv "m"))) (ltT (pv "n") (pv "m"))
  ]

/-! ## de Bruijn AST constructors (the kernel term language the recognizer emits). -/

def Var (k : AST) : AST := .sexp (.id "Var") [k]
def Con (x : AST) : AST := .sexp (.id "Con") [x]
def Srt (s : AST) : AST := .sexp (.id "Srt") [s]
def Pi (A B : AST) : AST := .sexp (.id "Pi") [A, B]
def Lam (A b : AST) : AST := .sexp (.id "Lam") [A, b]
def App (f a : AST) : AST := .sexp (.id "App") [f, a]

/-! ## de Bruijn `shift` — mirrors `LF.shift` / `lf-shift` clause-for-clause.

The `if (< k c)` guard is desugared to a helper `shiftVar` dispatched on `tt`/`ff`.  Binder clauses
raise the cutoff to `(S c)`.  All left-hand sides are headed by distinct constructors, so the system
is orthogonal and order-independent. -/

def shift (c t : AST) : AST := .sexp (.id "shift") [c, t]
def shiftVar (c k b : AST) : AST := .sexp (.id "shiftVar") [c, k, b]

def shiftRules : List RewriteDecl := ltRules ++ [
    -- variable: lift by one iff its index is at/above the cutoff
    rw "sh-var"  (shift (pv "c") (Var (pv "k"))) (shiftVar (pv "c") (pv "k") (ltT (pv "k") (pv "c"))),
    rw "sh-var-lt" (shiftVar (pv "c") (pv "k") (con0 "tt")) (Var (pv "k")),
    rw "sh-var-ge" (shiftVar (pv "c") (pv "k") (con0 "ff")) (Var (S (pv "k"))),
    -- sorts and constants are unaffected
    rw "sh-srt"  (shift (pv "c") (Srt (pv "s"))) (Srt (pv "s")),
    rw "sh-con"  (shift (pv "c") (Con (pv "x"))) (Con (pv "x")),
    -- binders raise the cutoff on the body
    rw "sh-pi"   (shift (pv "c") (Pi (pv "A") (pv "B")))
                 (Pi (shift (pv "c") (pv "A")) (shift (S (pv "c")) (pv "B"))),
    rw "sh-lam"  (shift (pv "c") (Lam (pv "A") (pv "b")))
                 (Lam (shift (pv "c") (pv "A")) (shift (S (pv "c")) (pv "b"))),
    -- application shifts both sides at the same cutoff
    rw "sh-app"  (shift (pv "c") (App (pv "f") (pv "a")))
                 (App (shift (pv "c") (pv "f")) (shift (pv "c") (pv "a")))
  ]

/-- The `shift` presentation (numeric substrate + shift clauses). -/
def pShift : Presentation := .mk [] [] [] shiftRules []

/-! ### `shift` corpus — proved by `rfl` on the certified normalizer.

These mirror the way the recognizer uses `shift` (the arrow clause lowers `A -> B` to
`Pi A (shift 0 B)`), computed here *through `MeTTaIL.eval`*. -/

/-- A free variable at index 0, cutoff 0, lifts: `shift 0 (Var 0) = Var 1`.  (The arrow-clause case.) -/
theorem shift_var0 : eval pShift 40 (shift Z (Var Z)) = Var (S Z) := by rfl

/-- A variable at index 1, cutoff 0, lifts: `shift 0 (Var 1) = Var 2`. -/
theorem shift_var1 : eval pShift 40 (shift Z (Var (S Z))) = Var (S (S Z)) := by rfl

/-- Constants are unaffected: `shift 0 (Con nat) = Con nat`. -/
theorem shift_con : eval pShift 40 (shift Z (Con (con0 "nat"))) = Con (con0 "nat") := by rfl

/-- Under a binder the cutoff rises, so the bound var (index 0) is *not* lifted:
    `shift 0 (Pi (Con a) (Var 0)) = Pi (Con a) (Var 0)`. -/
theorem shift_pi_bound :
    eval pShift 60 (shift Z (Pi (Con (con0 "a")) (Var Z))) = Pi (Con (con0 "a")) (Var Z) := by rfl

/-- Under a binder, a *free* var (index 1, i.e. cutoff-relative 0 outside) lifts:
    `shift 0 (Pi (Con a) (Var 1)) = Pi (Con a) (Var 2)`. -/
theorem shift_pi_free :
    eval pShift 60 (shift Z (Pi (Con (con0 "a")) (Var (S Z)))) = Pi (Con (con0 "a")) (Var (S (S Z)))
    := by rfl

/-- Application descends into both sides (context recursion):
    `shift 0 (App (Var 0) (Con z)) = App (Var 1) (Con z)`. -/
theorem shift_app :
    eval pShift 60 (shift Z (App (Var Z) (Con (con0 "z")))) = App (Var (S Z)) (Con (con0 "z"))
    := by rfl

/-! ## Named context → de Bruijn: `ctxidx` + `resolve`, mirroring `lf-ctxidx` / `lf-resolve`.

The recognizer's `(if (== $h $s) …)` identifier-equality test is encoded *without* a boolean helper,
by MeTTaIL's **repeated-pattern-variable matching**: a left-hand side that binds the same variable to
the list head and to the query (`ctx-hit`) fires only when they are the same identifier (`matchPat`
checks the second occurrence for consistency).  Identifiers are distinct nullary constructors.

Unlike `shift`, this component is **order-sensitive**: `ctx-hit` must precede the general `ctx-miss`,
because when head = query both match and the deterministic leftmost-outermost `oneStep` (which the
E2b proof runs over) takes the first — exactly the recognizer's first-match `if`.  The recursive
`case` is CPS-desugared through `ctxK` / `resolveK`, whose rules are disjoint on `NF` vs `(Idx k)`. -/

def Nil : AST := con0 "Nil"
def Cons (h t : AST) : AST := .sexp (.id "Cons") [h, t]
def NF : AST := con0 "NF"
def Idx (k : AST) : AST := .sexp (.id "Idx") [k]

def ctxidx (ctx s : AST) : AST := .sexp (.id "ctxidx") [ctx, s]
def ctxK (r : AST) : AST := .sexp (.id "ctxK") [r]
def resolve (ctx s : AST) : AST := .sexp (.id "resolve") [ctx, s]
def resolveK (s r : AST) : AST := .sexp (.id "resolveK") [s, r]

/-- `ctxidx` rules — ORDER MATTERS: nil, then hit (repeated-var equality), then the general miss. -/
def ctxidxRules : List RewriteDecl := [
    rw "ctx-nil"  (ctxidx Nil (pv "s"))                       NF,
    rw "ctx-hit"  (ctxidx (Cons (pv "h") (pv "t")) (pv "h"))  (Idx Z),
    rw "ctx-miss" (ctxidx (Cons (pv "h") (pv "t")) (pv "s"))  (ctxK (ctxidx (pv "t") (pv "s"))),
    rw "ctxK-nf"  (ctxK NF)                                   NF,
    rw "ctxK-idx" (ctxK (Idx (pv "k")))                       (Idx (S (pv "k")))
  ]

/-- `resolve` rules — bound name → `(Var k)`, free name → `(Con name)`. -/
def resolveRules : List RewriteDecl := ctxidxRules ++ [
    rw "res"     (resolve (pv "ctx") (pv "s"))     (resolveK (pv "s") (ctxidx (pv "ctx") (pv "s"))),
    rw "res-idx" (resolveK (pv "s") (Idx (pv "k"))) (Var (pv "k")),
    rw "res-nf"  (resolveK (pv "s") NF)             (Con (pv "s"))
  ]

def pResolve : Presentation := .mk [] [] [] resolveRules []

/-! ### `ctxidx` / `resolve` corpus — proved by `rfl` on the certified normalizer. -/

/-- Innermost binder: `resolve [x] x = Var 0`. -/
theorem resolve_bound0 :
    eval pResolve 40 (resolve (Cons (con0 "x") Nil) (con0 "x")) = Var Z := by rfl

/-- Second binder out: `resolve [y, x] x = Var 1`. -/
theorem resolve_bound1 :
    eval pResolve 40 (resolve (Cons (con0 "y") (Cons (con0 "x") Nil)) (con0 "x")) = Var (S Z)
    := by rfl

/-- Not in scope → free constant: `resolve [y] x = Con x`. -/
theorem resolve_free :
    eval pResolve 40 (resolve (Cons (con0 "y") Nil) (con0 "x")) = Con (con0 "x") := by rfl

/-- Empty context → free constant: `resolve [] x = Con x`. -/
theorem resolve_empty :
    eval pResolve 40 (resolve Nil (con0 "x")) = Con (con0 "x") := by rfl

/-- The raw index too: `ctxidx [x, y] y = Idx 1`. -/
theorem ctxidx_hit1 :
    eval pResolve 40 (ctxidx (Cons (con0 "x") (Cons (con0 "y") Nil)) (con0 "y")) = Idx (S Z) := by rfl

/-! ## The parser family: `lf-atom / lf-app / lf-appmore / lf-arrow / lf-term` + `lf-recognize`.

The mutually-recursive recursive-descent core, mirroring `lf_recognizer_v0.metta` clause-for-clause.
Every `case`-on-a-recursive-result is CPS-desugared to a continuation whose rules match **only** the
closed result-shape set `{P, PErr}` — never a bare pattern variable — so under leftmost-outermost
`oneStep` the inner call is forced to normal form *before* any continuation fires (a bare catch-all
would fire on the un-reduced call and corrupt the reduction).  Token-list sub-dispatch may use
catch-alls, since token suffixes are input-derived and already normal.  Peano fuel is threaded
exactly as `recognize`'s `Nat` fuel (`≤0` → `Z`; `-1` → the `f` under `S f`); the fall-through in
`lf-term` passes the decremented fuel to `lf-arrow`, matching `LF.pTerm`. -/

/-- Tokens (a clean re-lexing of the surface: `(Tid s)` is `(Lex lf-id s)`). -/
def tPI : AST := con0 "PI"
def tLAM : AST := con0 "LAM"
def tARR : AST := con0 "ARR"
def tCOLON : AST := con0 "COLON"
def tDOT : AST := con0 "DOT"
def tLP : AST := con0 "LP"
def tRP : AST := con0 "RP"
def tTYPE : AST := con0 "TYPE"
def tId (s : AST) : AST := .sexp (.id "Tid") [s]

/-- Parser results and top-level verdicts. -/
def Pp (t r : AST) : AST := .sexp (.id "P") [t, r]
def PErr (e : AST) : AST := .sexp (.id "PErr") [e]
def Ok (t : AST) : AST := .sexp (.id "Ok") [t]
def Err (e : AST) : AST := .sexp (.id "Err") [e]

/-- Function symbols + their continuations. -/
def tm (f c t : AST) : AST := .sexp (.id "tm") [f, c, t]
def ar (f c t : AST) : AST := .sexp (.id "ar") [f, c, t]
def ap (f c t : AST) : AST := .sexp (.id "ap") [f, c, t]
def apm (f c acc t : AST) : AST := .sexp (.id "apm") [f, c, acc, t]
def at' (f c t : AST) : AST := .sexp (.id "at") [f, c, t]
def tmPi1 (f c x r : AST) : AST := .sexp (.id "tmPi1") [f, c, x, r]
def tmPi2 (A r : AST) : AST := .sexp (.id "tmPi2") [A, r]
def tmLam1 (f c x r : AST) : AST := .sexp (.id "tmLam1") [f, c, x, r]
def tmLam2 (A r : AST) : AST := .sexp (.id "tmLam2") [A, r]
def arK (f c r : AST) : AST := .sexp (.id "arK") [f, c, r]
def arK2 (a r : AST) : AST := .sexp (.id "arK2") [a, r]
def apK (f c r : AST) : AST := .sexp (.id "apK") [f, c, r]
def apmK (f c acc toks r : AST) : AST := .sexp (.id "apmK") [f, c, acc, toks, r]
def atLPk (f c r : AST) : AST := .sexp (.id "atLPk") [f, c, r]
def recK (r : AST) : AST := .sexp (.id "recK") [r]
def lfrec (t : AST) : AST := .sexp (.id "lfrec") [t]

/-- Peano encoding of a concrete fuel bound. -/
def peano : Nat → AST
  | 0 => Z
  | n + 1 => S (peano n)

/-- `(extra-tokens rest)` error payload. -/
def extraToks (r : AST) : AST := .sexp (.id "extra-tokens") [r]

/-- The parser rewrite rules (order within each head: specific before catch-all). -/
def parserRules : List RewriteDecl := [
    -- lf-term : Pi | Lam | (fall through to) Arrow
    rw "tm-z"   (tm Z (pv "c") (pv "t")) (PErr (con0 "no-fuel")),
    rw "tm-pi"  (tm (S (pv "f")) (pv "c") (Cons tPI (Cons (tId (pv "x")) (Cons tCOLON (pv "rest")))))
                (tmPi1 (pv "f") (pv "c") (pv "x") (ap (pv "f") (pv "c") (pv "rest"))),
    rw "tm-lam" (tm (S (pv "f")) (pv "c") (Cons tLAM (Cons (tId (pv "x")) (Cons tCOLON (pv "rest")))))
                (tmLam1 (pv "f") (pv "c") (pv "x") (ap (pv "f") (pv "c") (pv "rest"))),
    rw "tm-fall" (tm (S (pv "f")) (pv "c") (pv "t")) (ar (pv "f") (pv "c") (pv "t")),
    -- tmPi continuation (on the argument parse, then on the body parse)
    rw "tmPi1-dot"  (tmPi1 (pv "f") (pv "c") (pv "x") (Pp (pv "A") (Cons tDOT (pv "r2"))))
                    (tmPi2 (pv "A") (tm (pv "f") (Cons (pv "x") (pv "c")) (pv "r2"))),
    rw "tmPi1-cons" (tmPi1 (pv "f") (pv "c") (pv "x") (Pp (pv "A") (Cons (pv "tok") (pv "r2"))))
                    (PErr (con0 "pi-malformed")),
    rw "tmPi1-nil"  (tmPi1 (pv "f") (pv "c") (pv "x") (Pp (pv "A") Nil)) (PErr (con0 "pi-malformed")),
    rw "tmPi1-err"  (tmPi1 (pv "f") (pv "c") (pv "x") (PErr (pv "e"))) (PErr (con0 "pi-malformed")),
    rw "tmPi2-p"    (tmPi2 (pv "A") (Pp (pv "B") (pv "r3"))) (Pp (Pi (pv "A") (pv "B")) (pv "r3")),
    rw "tmPi2-err"  (tmPi2 (pv "A") (PErr (pv "e"))) (PErr (pv "e")),
    -- tmLam continuation
    rw "tmLam1-dot"  (tmLam1 (pv "f") (pv "c") (pv "x") (Pp (pv "A") (Cons tDOT (pv "r2"))))
                     (tmLam2 (pv "A") (tm (pv "f") (Cons (pv "x") (pv "c")) (pv "r2"))),
    rw "tmLam1-cons" (tmLam1 (pv "f") (pv "c") (pv "x") (Pp (pv "A") (Cons (pv "tok") (pv "r2"))))
                     (PErr (con0 "lam-malformed")),
    rw "tmLam1-nil"  (tmLam1 (pv "f") (pv "c") (pv "x") (Pp (pv "A") Nil)) (PErr (con0 "lam-malformed")),
    rw "tmLam1-err"  (tmLam1 (pv "f") (pv "c") (pv "x") (PErr (pv "e"))) (PErr (con0 "lam-malformed")),
    rw "tmLam2-p"    (tmLam2 (pv "A") (Pp (pv "b") (pv "r3"))) (Pp (Lam (pv "A") (pv "b")) (pv "r3")),
    rw "tmLam2-err"  (tmLam2 (pv "A") (PErr (pv "e"))) (PErr (pv "e")),
    -- lf-arrow : App -> Term | App
    rw "ar-z" (ar Z (pv "c") (pv "t")) (PErr (con0 "no-fuel")),
    rw "ar-s" (ar (S (pv "f")) (pv "c") (pv "t")) (arK (pv "f") (pv "c") (ap (pv "f") (pv "c") (pv "t"))),
    rw "arK-arr"  (arK (pv "f") (pv "c") (Pp (pv "a") (Cons tARR (pv "rest"))))
                  (arK2 (pv "a") (tm (pv "f") (pv "c") (pv "rest"))),
    rw "arK-cons" (arK (pv "f") (pv "c") (Pp (pv "a") (Cons (pv "tok") (pv "rest"))))
                  (Pp (pv "a") (Cons (pv "tok") (pv "rest"))),
    rw "arK-nil"  (arK (pv "f") (pv "c") (Pp (pv "a") Nil)) (Pp (pv "a") Nil),
    rw "arK-err"  (arK (pv "f") (pv "c") (PErr (pv "e"))) (PErr (pv "e")),
    rw "arK2-p"   (arK2 (pv "a") (Pp (pv "b") (pv "r2"))) (Pp (Pi (pv "a") (shift Z (pv "b"))) (pv "r2")),
    rw "arK2-err" (arK2 (pv "a") (PErr (pv "e"))) (PErr (pv "e")),
    -- lf-app : one atom, then fold trailing atoms
    rw "ap-z" (ap Z (pv "c") (pv "t")) (PErr (con0 "no-fuel")),
    rw "ap-s" (ap (S (pv "f")) (pv "c") (pv "t")) (apK (pv "f") (pv "c") (at' (pv "f") (pv "c") (pv "t"))),
    rw "apK-p"   (apK (pv "f") (pv "c") (Pp (pv "a0") (pv "r0"))) (apm (pv "f") (pv "c") (pv "a0") (pv "r0")),
    rw "apK-err" (apK (pv "f") (pv "c") (PErr (pv "e"))) (PErr (pv "e")),
    -- lf-appmore : left-fold trailing atoms (fuel-out and atom-fail both return the accumulator)
    rw "apm-z" (apm Z (pv "c") (pv "acc") (pv "t")) (Pp (pv "acc") (pv "t")),
    rw "apm-s" (apm (S (pv "f")) (pv "c") (pv "acc") (pv "t"))
               (apmK (pv "f") (pv "c") (pv "acc") (pv "t") (at' (pv "f") (pv "c") (pv "t"))),
    rw "apmK-p"   (apmK (pv "f") (pv "c") (pv "acc") (pv "toks") (Pp (pv "a") (pv "rest")))
                  (apm (pv "f") (pv "c") (App (pv "acc") (pv "a")) (pv "rest")),
    rw "apmK-err" (apmK (pv "f") (pv "c") (pv "acc") (pv "toks") (PErr (pv "e"))) (Pp (pv "acc") (pv "toks")),
    -- lf-atom : ( Term ) | Type | id
    rw "at-z"  (at' Z (pv "c") (pv "t")) (PErr (con0 "no-fuel")),
    rw "at-lp" (at' (S (pv "f")) (pv "c") (Cons tLP (pv "rest")))
               (atLPk (pv "f") (pv "c") (tm (pv "f") (pv "c") (pv "rest"))),
    rw "at-type" (at' (S (pv "f")) (pv "c") (Cons tTYPE (pv "rest"))) (Pp (Srt (con0 "type")) (pv "rest")),
    rw "at-id"   (at' (S (pv "f")) (pv "c") (Cons (tId (pv "s")) (pv "rest")))
                 (Pp (resolve (pv "c") (pv "s")) (pv "rest")),
    rw "at-err"  (at' (S (pv "f")) (pv "c") (pv "t")) (PErr (con0 "atom-expected")),
    rw "atLPk-rp"   (atLPk (pv "f") (pv "c") (Pp (pv "t") (Cons tRP (pv "r2")))) (Pp (pv "t") (pv "r2")),
    rw "atLPk-cons" (atLPk (pv "f") (pv "c") (Pp (pv "t") (Cons (pv "tok") (pv "r2")))) (PErr (con0 "paren-malformed")),
    rw "atLPk-nil"  (atLPk (pv "f") (pv "c") (Pp (pv "t") Nil)) (PErr (con0 "paren-malformed")),
    rw "atLPk-err"  (atLPk (pv "f") (pv "c") (PErr (pv "e"))) (PErr (con0 "paren-malformed")),
    -- lf-recognize : closed term, all tokens consumed
    rw "rec"      (lfrec (pv "t")) (recK (tm (peano 64) Nil (pv "t"))),
    rw "recK-nil"  (recK (Pp (pv "t") Nil)) (Ok (pv "t")),
    rw "recK-cons" (recK (Pp (pv "t") (Cons (pv "h") (pv "r")))) (Err (extraToks (Cons (pv "h") (pv "r")))),
    rw "recK-err"  (recK (PErr (pv "e"))) (Err (pv "e"))
  ]

/-- The full LF recognizer as a pure `MeTTaIL.Presentation`: numeric substrate + shift + resolve +
    the parser family.  (Heads are pairwise distinct across the four rule groups.) -/
def pLF : Presentation := .mk [] [] [] (shiftRules ++ resolveRules ++ parserRules) []

/-! ### First corpus checks through the certified engine (simplest streams first). -/

/-- `rfl z` ⟶ `Ok (App (Con rfl) (Con z))` — the cToks1 stream, run on `MeTTaIL.eval`. -/
theorem lf_c1 :
    eval pLF 100 (lfrec (Cons (tId (con0 "rfl")) (Cons (tId (con0 "z")) Nil)))
      = Ok (App (Con (con0 "rfl")) (Con (con0 "z"))) := by rfl

/-- `eqn z z` ⟶ `Ok (App (App (Con eqn) (Con z)) (Con z))` — cToks2 (left-fold application). -/
theorem lf_c2 :
    eval pLF 100 (lfrec (Cons (tId (con0 "eqn")) (Cons (tId (con0 "z")) (Cons (tId (con0 "z")) Nil))))
      = Ok (App (App (Con (con0 "eqn")) (Con (con0 "z"))) (Con (con0 "z"))) := by rfl

/-- `eqn z (s z)` ⟶ nested application through parentheses — cToks3. -/
theorem lf_c3 :
    eval pLF 150 (lfrec (Cons (tId (con0 "eqn")) (Cons (tId (con0 "z"))
        (Cons tLP (Cons (tId (con0 "s")) (Cons (tId (con0 "z")) (Cons tRP Nil)))))))
      = Ok (App (App (Con (con0 "eqn")) (Con (con0 "z"))) (App (Con (con0 "s")) (Con (con0 "z"))))
    := by rfl

/-- `λ x : nat . x` ⟶ `Ok (Lam (Con nat) (Var 0))` — cToks4 (binder scope resolution). -/
theorem lf_c4 :
    eval pLF 150 (lfrec (Cons tLAM (Cons (tId (con0 "x")) (Cons tCOLON
        (Cons (tId (con0 "nat")) (Cons tDOT (Cons (tId (con0 "x")) Nil)))))))
      = Ok (Lam (Con (con0 "nat")) (Var Z)) := by rfl

/-- `nat → nat` ⟶ `Ok (Pi (Con nat) (Con nat))` — cToks5 (arrow lowers to a non-dependent Pi with a
    shift of the body). -/
theorem lf_c5 :
    eval pLF 150 (lfrec (Cons (tId (con0 "nat")) (Cons tARR (Cons (tId (con0 "nat")) Nil))))
      = Ok (Pi (Con (con0 "nat")) (Con (con0 "nat"))) := by rfl

/-- `( λ x : nat . x ) z` ⟶ `Ok (App (Lam (Con nat) (Var 0)) (Con z))` — cToks6 (parenthesised
    binder applied to an argument). -/
theorem lf_c6 :
    eval pLF 200 (lfrec (Cons tLP (Cons tLAM (Cons (tId (con0 "x")) (Cons tCOLON
        (Cons (tId (con0 "nat")) (Cons tDOT (Cons (tId (con0 "x")) (Cons tRP
        (Cons (tId (con0 "z")) Nil))))))))))
      = Ok (App (Lam (Con (con0 "nat")) (Var Z)) (Con (con0 "z"))) := by rfl

/-- `Π A : Type . ( A → A )` ⟶ `Ok (Pi (Srt type) (Pi (Var 0) (Var 1)))` — cToks7 (dependent Pi over a
    sort, with the inner arrow's body shifted under the binder). The deepest corpus stream. -/
theorem lf_c7 :
    eval pLF 250 (lfrec (Cons tPI (Cons (tId (con0 "A")) (Cons tCOLON (Cons tTYPE (Cons tDOT
        (Cons tLP (Cons (tId (con0 "A")) (Cons tARR (Cons (tId (con0 "A")) (Cons tRP Nil)))))))))))
      = Ok (Pi (Srt (con0 "type")) (Pi (Var Z) (Var (S Z)))) := by rfl

/-- The malformed stream `( .` ⟶ `Err paren-malformed` — cToks8 (the recognizer rejects; `recognize`
    returns `none`). Fail-closed, computed on the engine. -/
theorem lf_c8 :
    eval pLF 100 (lfrec (Cons tLP (Cons tDOT Nil))) = Err (con0 "paren-malformed") := by rfl

end Mettapedia.GSLT.LanguageDef.LFEnc
