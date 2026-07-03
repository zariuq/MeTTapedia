/-
# E2b Route-A' — the certified `MeTTaIL.eval` supports every primitive the recognizer needs (2026-07-03)

`LFEngineProbe.lean` established that the *full* HE driver (`runMinimalSource`) computes correctly
but does **not** reduce by `rfl`/`decide` (it threads `Std.HashMap`, parses a `String`, and
pretty-prints), and `native_decide` is banned — so no corpus-through-the-real-engine proof by
computation is available there.

This file de-risks the alternative that E2b rests on: `MeTTaIL.eval`, the certified pure-rewriting
normalizer (`eval_sound`, "trusted boundary: none").  Its whole call graph —
`eval → oneStep → baseReducts → applyBaseRewrite → AST.matchPat / AST.inst` — is plain structural
recursion over `AST`/`List` with `String`-`BEq` comparisons, no `HashMap`/parse/pretty.

The recognizer (`lf_recognizer_v0.metta`) needs exactly three things to survive re-encoding as a
pure `Presentation`:

  1. **multi-rule pattern dispatch** — the `case`/`if` of the recognizer becomes several `.base`
     rewrites with distinct pattern left-hand sides (first match wins, leftmost-outermost);
  2. **Peano arithmetic** — fuel `≤ 0` / `- 1` and de Bruijn `< c` / `+ 1` become `Z`/`S` rules;
  3. **context-descending recursion** — reduction under constructors (the `arg` rule).

Each is shown below to reduce by `rfl` in `MeTTaIL.eval`, so re-encoding the recognizer is a
*mechanical* translation, not a hoped-for one.  (Identifier equality `==` in the recognizer becomes
structural matching of distinct nullary constructors, covered by dispatch.)

Integrity: 0 sorry / 0 native_decide; `eval_fires` axioms = `{propext}`.
-/
import MeTTaIL.Semantics.Eval

namespace Mettapedia.GSLT.LanguageDef.EngineReduce

open MeTTaIL

/-! ## Term builders (thin sugar over `AST`) -/

/-- A ground nullary constructor `(c)`. -/
def con (s : String) : AST := .sexp (.id s) []
/-- A pattern variable `$v`. -/
def pv (v : String) : AST := .var (.base v)
/-- A base rewrite `lhs ~> rhs` named `name`. -/
def rw (name : String) (lhs rhs : AST) : RewriteDecl := { name := name, rw := .base lhs rhs }

/-! ## GO/NO-GO: a single rule fires and a normal form is a fixpoint. -/

/-- The ground redex `(f a)`. -/
def fa : AST := .sexp (.id "f") [con "a"]
/-- A one-rule presentation carrying only `(f a) ~> b`. -/
def pFAB : Presentation := .mk [] [] [] [rw "r" fa (con "b")] []

/-- The certified normalizer reduces the redex to its contractum, checked by the kernel (`rfl`). -/
theorem eval_fires : eval pFAB 10 fa = con "b" := by rfl
/-- A normal form is a fixpoint under the same kernel computation. -/
theorem eval_normal : eval pFAB 10 (con "b") = con "b" := by rfl

/-! ## Primitive 2 + 3: Peano arithmetic under context-descending recursion.

`plus` recurses by pushing `S` outward — every step after the first fires *inside* an `S`, so this
exercises the `arg`/`oneStepList` context descent that the nested recognizer relies on. -/

/-- Peano zero. -/
def z : AST := con "Z"
/-- Peano successor. -/
def s (n : AST) : AST := .sexp (.id "S") [n]
/-- `(plus a b)`. -/
def plus (a b : AST) : AST := .sexp (.id "plus") [a, b]

/-- Peano addition: two rules, dispatched by whether the first argument is `Z` or `S`. -/
def pArith : Presentation := .mk [] [] [] [
    rw "plus-z" (plus z (pv "m")) (pv "m"),
    rw "plus-s" (plus (s (pv "n")) (pv "m")) (s (plus (pv "n") (pv "m")))
  ] []

/-- `2 + 1 = 3`, computed by the certified normalizer through three context-descending steps. -/
theorem plus_2_1 : eval pArith 20 (plus (s (s z)) (s z)) = s (s (s z)) := by rfl
/-- `0 + 2 = 2` (the base rule alone). -/
theorem plus_0_2 : eval pArith 20 (plus z (s (s z))) = s (s z) := by rfl

/-! ## Primitive 1 + 2: strict `<` on Peano naturals — the fuel-`≤0` and de Bruijn-`<c` tests.

Four dispatch rules, exactly the shape the recognizer's `(< $k $c)` / `(<= $f 0)` guards take once
Peano-encoded. `lt` returns the nullary constructors `tt` / `ff`. -/

/-- `(lt a b)`. -/
def lt (a b : AST) : AST := .sexp (.id "lt") [a, b]

/-- Strict less-than by structural dispatch on both arguments. -/
def pLt : Presentation := .mk [] [] [] [
    rw "lt-z-s"  (lt z (s (pv "m")))          (con "tt"),
    rw "lt-z-z"  (lt z z)                      (con "ff"),
    rw "lt-s-z"  (lt (s (pv "n")) z)           (con "ff"),
    rw "lt-s-s"  (lt (s (pv "n")) (s (pv "m"))) (lt (pv "n") (pv "m"))
  ] []

/-- `1 < 2 = tt` — recurses via `lt-s-s` down to `lt-z-s`. -/
theorem lt_1_2 : eval pLt 20 (lt (s z) (s (s z))) = con "tt" := by rfl
/-- `2 < 2 = ff` — recurses down to `lt-z-z`. -/
theorem lt_2_2 : eval pLt 20 (lt (s (s z)) (s (s z))) = con "ff" := by rfl
/-- `2 < 1 = ff` — recurses down to `lt-s-z`. -/
theorem lt_2_1 : eval pLt 20 (lt (s (s z)) (s z)) = con "ff" := by rfl

end Mettapedia.GSLT.LanguageDef.EngineReduce
