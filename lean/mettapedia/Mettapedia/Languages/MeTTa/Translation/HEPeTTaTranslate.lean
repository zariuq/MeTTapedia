import Mettapedia.Languages.MeTTa.OSLFCore.Bridge
import Mettapedia.Languages.MeTTa.Translation.HEPeTTaSound

/-!
# Executable HE ↔ PeTTa Translator

Computable Lean functions mirroring the relational Prolog translator
`hyperon/translators/he_petta_relational.pl`. Each function threads an
explicit freshness supply `Nat` (no side effects).

## Design

The Prolog reference is:
```prolog
he_to_petta(+HE, -PeTTa, +S0, -S1).
petta_to_he(+PeTTa, -HE, +S0, -S1).
```

We mirror this as:
```lean
translateHE   : Atom → Nat → Atom × Nat
translatePeTTa : Atom → Nat → Atom × Nat
```

Both are total (return unchanged on unrecognized input).

## Correctness Target

Roundtrip up to administrative equivalence (`≈admin`), NOT literal `=`.
Administrative forms: fresh variables (`$__tr_*`), inserted lets (from `nop`).

## References

- Prolog spec: `hyperon/translators/he_petta_relational.pl`
- Lean soundness: `Translation/HEPeTTaSound.lean`
- AST bridge: `OSLFCore/Bridge.lean` (`atomToPattern`)
-/

namespace Mettapedia.Languages.MeTTa.Translation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Fresh name generation -/

/-- Generate a fresh variable name with a prefix and supply counter.
    Mirrors Prolog's `fresh_name(Prefix, S0, S1, Var)`. -/
def freshVar (tag : String) (supply : Nat) : Atom × Nat :=
  let s1 := supply + 1
  (.var ("$__tr_" ++ tag ++ "_" ++ toString s1), s1)

/-! ## HE → PeTTa Translation

Mirrors `he_to_petta/4` from `he_petta_relational.pl`. -/

/-- Translate an HE MeTTa atom to PeTTa MeTTa, threading freshness supply.

    | HE construct                  | PeTTa result             |
    |-------------------------------|--------------------------|
    | `(chain E V B)`               | `(let V E' B')`          |
    | `(collapse-bind X)`           | `(collapse X')`          |
    | `(superpose-bind X)`          | `(superpose X')`         |
    | `(switch S Bs...)`            | `(case S' Bs'...)`       |
    | `(switch-minimal S Bs...)`    | `(case S' Bs'...)`       |
    | `(atom-subst A V T)`          | `(let V A' T')`          |
    | `(nop X)`                     | `(let $fresh X' ())`     |
    | `(function (return X))`       | `X'`                     |
    | `(expr ...)`                  | recurse into subterms    |
    | variable / symbol / other     | identity                 | -/
def translateHE (a : Atom) (supply : Nat) : Atom × Nat :=
  match a with
  -- chain → let (with operand order swap: chain E V B → let V E' B')
  | .expression [.symbol "chain", e, v, body] =>
    let (te, s1) := translateHE e supply
    let (tb, s2) := translateHE body s1
    (.expression [.symbol "let", v, te, tb], s2)
  -- collapse-bind → collapse
  | .expression [.symbol "collapse-bind", inner] =>
    let (ti, s1) := translateHE inner supply
    (.expression [.symbol "collapse", ti], s1)
  -- superpose-bind → superpose
  | .expression [.symbol "superpose-bind", inner] =>
    let (ti, s1) := translateHE inner supply
    (.expression [.symbol "superpose", ti], s1)
  -- switch / switch-minimal → case (with recursive branch translation)
  | .expression (.symbol "switch" :: scrut :: branches) =>
    let (ts, s1) := translateHE scrut supply
    let (tbs, s2) := translateHEList branches s1
    (.expression (.symbol "case" :: ts :: tbs), s2)
  | .expression (.symbol "switch-minimal" :: scrut :: branches) =>
    let (ts, s1) := translateHE scrut supply
    let (tbs, s2) := translateHEList branches s1
    (.expression (.symbol "case" :: ts :: tbs), s2)
  -- atom-subst → let
  | .expression [.symbol "atom-subst", atom, v, tmpl] =>
    let (ta, s1) := translateHE atom supply
    let (tt, s2) := translateHE tmpl s1
    (.expression [.symbol "let", v, ta, tt], s2)
  -- nop → let with fresh discard variable
  | .expression [.symbol "nop", x] =>
    let (fresh, s1) := freshVar "discard" supply
    let (tx, s2) := translateHE x s1
    (.expression [.symbol "let", fresh, tx, .symbol "()"], s2)
  -- function (return X) → unwrap
  | .expression [.symbol "function", .expression [.symbol "return", x]] =>
    translateHE x supply
  -- generic expression: recurse into subterms
  | .expression es =>
    let (tes, s1) := translateHEList es supply
    (.expression tes, s1)
  -- variables, symbols, grounded: identity
  | other => (other, supply)
where
  /-- Translate a list of atoms, threading supply. -/
  translateHEList (xs : List Atom) (supply : Nat) : List Atom × Nat :=
    match xs with
    | [] => ([], supply)
    | x :: rest =>
      let (tx, s1) := translateHE x supply
      let (trest, s2) := translateHEList rest s1
      (tx :: trest, s2)

/-! ## PeTTa → HE Translation

Mirrors `petta_to_he/4` from `he_petta_relational.pl`. -/

/-- Translate a PeTTa MeTTa atom to HE MeTTa, threading freshness supply.

    | PeTTa construct               | HE result                |
    |-------------------------------|--------------------------|
    | `(progn)`                     | `()`                     |
    | `(progn A)`                   | `A'`                     |
    | `(progn A ... Z)`             | nested discard lets      |
    | `(prog1)`                     | `()`                     |
    | `(prog1 A)`                   | `A'`                     |
    | `(prog1 A ... Z)`             | capture first, eval rest |
    | `(foldall F G I)`             | `let(collapse G') + fold`|
    | `(@< A B)`                    | `(<s A' B')`             |
    | `(@> A B)`                    | `(not (<s A' B'))`       |
    | `(expr ...)`                  | recurse into subterms    |
    | variable / symbol / other     | identity                 | -/
def translatePeTTa (a : Atom) (supply : Nat) : Atom × Nat :=
  match a with
  -- progn A ... Z → nested lets that discard every value except the last
  | .expression (.symbol "progn" :: args) =>
    translatePeTTaProgn args supply
  -- prog1 A ... Z → let $r A' (let $d B' ... $r)
  | .expression (.symbol "prog1" :: args) =>
    translatePeTTaProg1 args supply
  -- foldall Agg Goal Init → let $xs (collapse Goal') (foldl-atom ...)
  | .expression [.symbol "foldall", agg, goal, init] =>
    let (tagg, s1) := translatePeTTa agg supply
    let (tgoal, s2) := translatePeTTa goal s1
    let (tinit, s3) := translatePeTTa init s2
    let (listVar, s4) := freshVar "collapsed" s3
    let (accVar, s5) := freshVar "acc" s4
    let (itemVar, s6) := freshVar "item" s5
    (.expression
      [.symbol "let", listVar,
        .expression [.symbol "collapse", tgoal],
        .expression
          [.symbol "foldl-atom", listVar, tinit, accVar, itemVar,
            .expression [.symbol "eval", .expression [tagg, accVar, itemVar]]]], s6)
  -- @< → <s
  | .expression [.symbol "@<", a', b'] =>
    let (ta, s1) := translatePeTTa a' supply
    let (tb, s2) := translatePeTTa b' s1
    (.expression [.symbol "<s", ta, tb], s2)
  -- @> → not (<s ...)
  | .expression [.symbol "@>", a', b'] =>
    let (ta, s1) := translatePeTTa a' supply
    let (tb, s2) := translatePeTTa b' s1
    (.expression [.symbol "not", .expression [.symbol "<s", ta, tb]], s2)
  -- generic expression: recurse
  | .expression es =>
    let (tes, s1) := translatePeTTaList es supply
    (.expression tes, s1)
  -- identity
  | other => (other, supply)
where
  /-- Translate a variadic `progn`, returning unit on `[]`, the translated
      element on singletons, and nested discard-`let`s otherwise. -/
  translatePeTTaProgn (args : List Atom) (supply : Nat) : Atom × Nat :=
    match args with
    | [] => (.symbol "()", supply)
    | [last] => translatePeTTa last supply
    | expr :: rest =>
      let (fresh, s1) := freshVar "discard" supply
      let (texpr, s2) := translatePeTTa expr s1
      let (trest, s3) := translatePeTTaProgn rest s2
      (.expression [.symbol "let", fresh, texpr, trest], s3)

  /-- Translate the tail of a variadic `prog1`, evaluating each term for side
      effects and finally returning the already-bound first result. -/
  translatePeTTaProg1Rest (args : List Atom) (resultVar : Atom) (supply : Nat) : Atom × Nat :=
    match args with
    | [] => (resultVar, supply)
    | expr :: rest =>
      let (fresh, s1) := freshVar "discard" supply
      let (texpr, s2) := translatePeTTa expr s1
      let (trest, s3) := translatePeTTaProg1Rest rest resultVar s2
      (.expression [.symbol "let", fresh, texpr, trest], s3)

  /-- Translate a variadic `prog1`, returning unit on `[]`, the translated
      element on singletons, and capturing the first result otherwise. -/
  translatePeTTaProg1 (args : List Atom) (supply : Nat) : Atom × Nat :=
    match args with
    | [] => (.symbol "()", supply)
    | [first] => translatePeTTa first supply
    | first :: rest =>
      let (freshR, s1) := freshVar "result" supply
      let (tfirst, s2) := translatePeTTa first s1
      let (trest, s3) := translatePeTTaProg1Rest rest freshR s2
      (.expression [.symbol "let", freshR, tfirst, trest], s3)

  translatePeTTaList (xs : List Atom) (supply : Nat) : List Atom × Nat :=
    match xs with
    | [] => ([], supply)
    | x :: rest =>
      let (tx, s1) := translatePeTTa x supply
      let (trest, s2) := translatePeTTaList rest s1
      (tx :: trest, s2)

/-! ## Extended foldall boundary

The proven core translator keeps `foldall` lowering on the pure HE surface via
`collapse`. The executable Prolog translator also supports an optional
HE-extended lowering that swaps this single collector head to `collect`.

This section makes that boundary explicit in Lean, without changing the proven
core translator.
-/

/-- Extended-only foldall lowering: same as the core lowering, except it uses
`collect` instead of `collapse` for the collector step. -/
def translatePeTTaFoldallExtended (agg goal init : Atom) (supply : Nat) : Atom × Nat :=
  let (tagg, s1) := translatePeTTa agg supply
  let (tgoal, s2) := translatePeTTa goal s1
  let (tinit, s3) := translatePeTTa init s2
  let (listVar, s4) := freshVar "collapsed" s3
  let (accVar, s5) := freshVar "acc" s4
  let (itemVar, s6) := freshVar "item" s5
  (.expression
    [.symbol "let", listVar,
      .expression [.symbol "collect", tgoal],
      .expression
        [.symbol "foldl-atom", listVar, tinit, accVar, itemVar,
          .expression [.symbol "eval", .expression [tagg, accVar, itemVar]]]], s6)

/-- Normalization map from the extended foldall collector to the pure one. -/
def normalizeExtendedFoldallCollector : Atom → Atom
  | .expression [.symbol "let", listVar, .expression [.symbol "collect", goal], tail] =>
      .expression [.symbol "let", listVar, .expression [.symbol "collapse", goal], tail]
  | a => a

/-- Boundary theorem: extended foldall lowering agrees with the proven pure
lowering after replacing `collect` with `collapse`; fresh-supply threading is
identical. -/
theorem translatePeTTa_foldall_extended_boundary (agg goal init : Atom) (s : Nat) :
    let pure := translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s
    let ext := translatePeTTaFoldallExtended agg goal init s
    normalizeExtendedFoldallCollector ext.1 = pure.1 ∧ ext.2 = pure.2 := by
  simp [translatePeTTa, translatePeTTaFoldallExtended, normalizeExtendedFoldallCollector]

/-! ## Optional HE optimization for translated PeTTa→HE output

This mirrors the executable post-translation optimizer while keeping it separate
from the core `translatePeTTa` lowering. The optimizer improves the generated HE
surface but intentionally does *not* preserve the current stable-common-fragment
fixed-point proofs, because it may reintroduce HE-native administrative heads
such as `chain` and `nop`.
-/

/-- Recognize translator-generated discard binders. -/
def isTranslatorDiscardVar : Atom → Bool
  | .var v => v.startsWith "$__tr_discard_"
  | _ => false

/-- Recognize translator-generated result binders. -/
def isTranslatorResultVar : Atom → Bool
  | .var v => v.startsWith "$__tr_result_"
  | _ => false

mutual
  /-- Syntactic occurrence check used by the optimizer guards. -/
  def containsAtom (needle : Atom) : Atom → Bool
    | .expression es =>
        if .expression es == needle then true else containsAtomList needle es
    | a => a == needle
  termination_by a => sizeOf a
  decreasing_by
    all_goals
      first
      | simp_wf; omega
      | simp_wf

  def containsAtomList (needle : Atom) : List Atom → Bool
    | [] => false
    | x :: xs => containsAtom needle x || containsAtomList needle xs
  termination_by xs => sizeOf xs
  decreasing_by
    all_goals
      first
      | simp_wf; omega
      | simp_wf
end

mutual
  /-- Detect whether a symbol appears as the head of any nested expression. -/
  def containsHeadSymbol (sym : String) : Atom → Bool
    | .expression [] => false
    | .expression (hd :: args) =>
        let matchesHead :=
          match hd with
          | .symbol head => head = sym
          | _ => false
        matchesHead || containsHeadSymbol sym hd || containsHeadSymbolList sym args
    | _ => false
  termination_by a => sizeOf a
  decreasing_by
    all_goals
      first
      | simp_wf; omega
      | simp_wf

  def containsHeadSymbolList (sym : String) : List Atom → Bool
    | [] => false
    | x :: xs => containsHeadSymbol sym x || containsHeadSymbolList sym xs
  termination_by xs => sizeOf xs
  decreasing_by
    all_goals
      first
      | simp_wf; omega
      | simp_wf
end

/-- The executable optimizer avoids turning `let (collapse ...)` into `chain`
because that path is not a stable common HE/CeTTa surface today. -/
def safeChainSource (a : Atom) : Bool :=
  !(containsHeadSymbol "collapse" a || containsHeadSymbol "collapse-bind" a)

mutual
  /-- Optimize translator-generated administrative lets in translated HE output. -/
  def optimizeTranslatedHE : Atom → Atom
    | .expression [.symbol "let", v, expr, body] =>
        let texpr := optimizeTranslatedHE expr
        let tbody := optimizeTranslatedHE body
        if isTranslatorDiscardVar v then
          if tbody == .symbol "()" then
            .expression [.symbol "nop", texpr]
          else if !(containsAtom v tbody) && safeChainSource texpr then
            .expression [.symbol "chain", texpr, v, tbody]
          else
            .expression [.symbol "let", v, texpr, tbody]
        else if isTranslatorResultVar v && tbody == v && !(containsAtom v texpr) then
          texpr
        else
          .expression [.symbol "let", v, texpr, tbody]
    | .expression es =>
        .expression (optimizeTranslatedHEList es)
    | other => other
  termination_by a => sizeOf a
  decreasing_by
    all_goals
      first
      | simp_wf; omega
      | simp_wf

  /-- Optimize each atom in a list. -/
  def optimizeTranslatedHEList : List Atom → List Atom
    | [] => []
    | x :: xs => optimizeTranslatedHE x :: optimizeTranslatedHEList xs
  termination_by xs => sizeOf xs
  decreasing_by
    all_goals
      first
      | simp_wf; omega
      | simp_wf
end

/-- Optimized PeTTa→HE translation used by the executable file translator. -/
def translatePeTTaOptimized (a : Atom) (supply : Nat) : Atom × Nat :=
  let (he, s1) := translatePeTTa a supply
  (optimizeTranslatedHE he, s1)

/-! ## Executable Tests

These `#eval` tests validate the Lean translator against the Prolog reference. -/

-- chain → let
#eval
  let (result, supply) := translateHE
    (.expression [.symbol "chain",
      .expression [.symbol "+", .symbol "1", .symbol "2"],
      .var "$x",
      .expression [.symbol "nop", .var "$x"]]) 0
  (repr result, supply)
  -- Expected: (let $x (+ 1 2) (let $__tr_discard_1 $x ())), supply = 1

-- collapse-bind → collapse
#eval
  let (result, _) := translateHE
    (.expression [.symbol "collapse-bind", .expression [.symbol "foo"]]) 0
  repr result
  -- Expected: (collapse (foo))

-- superpose-bind → superpose
#eval
  let (result, _) := translateHE
    (.expression [.symbol "superpose-bind",
      .expression [.symbol "a", .symbol "b"]]) 0
  repr result
  -- Expected: (superpose (a b))

-- function (return X) → unwrap
#eval
  let (result, _) := translateHE
    (.expression [.symbol "function",
      .expression [.symbol "return", .symbol "42"]]) 0
  repr result
  -- Expected: 42 (just the symbol)

-- nop → let with fresh
#eval
  let (result, supply) := translateHE
    (.expression [.symbol "nop", .var "$x"]) 0
  (repr result, supply)
  -- Expected: (let $__tr_discard_1 $x ()), supply = 1

-- PeTTa: progn (2-arg) → let with fresh
#eval
  let (result, supply) := translatePeTTa
    (.expression [.symbol "progn",
      .expression [.symbol "println!", .symbol "hello"],
      .symbol "ok"]) 0
  (repr result, supply)
  -- Expected: (let $__tr_discard_1 (println! hello) ok), supply = 1

-- PeTTa: prog1 (2-arg) → let with result capture
#eval
  let (result, supply) := translatePeTTa
    (.expression [.symbol "prog1",
      .expression [.symbol "compute"],
      .expression [.symbol "side-effect"]]) 0
  (repr result, supply)
  -- Expected: (let $__tr_result_1 (compute) (let $__tr_discard_2 (side-effect) $__tr_result_1))

-- PeTTa: progn / prog1 are variadic
example : (translatePeTTa (.expression [.symbol "progn"]) 0).1 = .symbol "()" := rfl

example : (translatePeTTa (.expression [.symbol "progn",
    .symbol "a", .symbol "b", .symbol "c", .symbol "d"]) 0).1 =
    .expression [.symbol "let", .var "$__tr_discard_1", .symbol "a",
      .expression [.symbol "let", .var "$__tr_discard_2", .symbol "b",
        .expression [.symbol "let", .var "$__tr_discard_3", .symbol "c", .symbol "d"]]] := rfl

example : (translatePeTTa (.expression [.symbol "prog1",
    .symbol "a", .symbol "b", .symbol "c"]) 0).1 =
    .expression [.symbol "let", .var "$__tr_result_1", .symbol "a",
      .expression [.symbol "let", .var "$__tr_discard_2", .symbol "b",
        .expression [.symbol "let", .var "$__tr_discard_3", .symbol "c",
          .var "$__tr_result_1"]]] := rfl

example : (translatePeTTa (.expression
    [.symbol "foldall", .symbol "merge", .expression [.symbol "twohop-item"], .symbol "0"]) 0).1 =
    .expression
      [.symbol "let", .var "$__tr_collapsed_1",
        .expression [.symbol "collapse", .expression [.symbol "twohop-item"]],
        .expression
          [.symbol "foldl-atom", .var "$__tr_collapsed_1", .symbol "0",
            .var "$__tr_acc_2", .var "$__tr_item_3",
            .expression [.symbol "eval",
              .expression [.symbol "merge", .var "$__tr_acc_2", .var "$__tr_item_3"]]]]
    := rfl

example : optimizeTranslatedHE
    (.expression [.symbol "let", .var "$__tr_discard_1",
      .expression [.symbol "println!", .symbol "hello"], .symbol "result"]) =
    .expression [.symbol "chain", .expression [.symbol "println!", .symbol "hello"],
      .var "$__tr_discard_1", .symbol "result"] := by native_decide

example : optimizeTranslatedHE
    (.expression [.symbol "let", .var "$__tr_discard_1",
      .expression [.symbol "println!", .symbol "hello"], .symbol "()"]) =
    .expression [.symbol "nop", .expression [.symbol "println!", .symbol "hello"]] := by native_decide

example : optimizeTranslatedHE
    (.expression [.symbol "let", .var "$__tr_result_1",
      .expression [.symbol "foo", .symbol "bar"], .var "$__tr_result_1"]) =
    .expression [.symbol "foo", .symbol "bar"] := by native_decide

example : optimizeTranslatedHE
    (.expression [.symbol "let", .var "$__tr_collapsed_1",
      .expression [.symbol "collapse", .expression [.symbol "twohop-item"]],
      .expression [.symbol "foldl-atom", .var "$__tr_collapsed_1", .symbol "0",
        .var "$__tr_acc_2", .var "$__tr_item_3",
        .expression [.symbol "eval",
          .expression [.symbol "merge", .var "$__tr_acc_2", .var "$__tr_item_3"]]]]) =
    .expression [.symbol "let", .var "$__tr_collapsed_1",
      .expression [.symbol "collapse", .expression [.symbol "twohop-item"]],
      .expression [.symbol "foldl-atom", .var "$__tr_collapsed_1", .symbol "0",
        .var "$__tr_acc_2", .var "$__tr_item_3",
        .expression [.symbol "eval",
          .expression [.symbol "merge", .var "$__tr_acc_2", .var "$__tr_item_3"]]]]
    := by native_decide

-- Roundtrip: HE → PeTTa → HE
#eval
  let (petta, s1) := translateHE
    (.expression [.symbol "chain",
      .expression [.symbol "+", .symbol "1", .symbol "2"],
      .var "$x",
      .var "$x"]) 0
  let (he2, _) := translatePeTTa petta s1
  (repr petta, repr he2)
  -- PeTTa: (let $x (+ 1 2) $x)
  -- HE2:   (let $x (+ 1 2) $x) — same! (no admin forms in this case)

-- Identity on variables and symbols
#eval
  let (v, _) := translateHE (.var "$foo") 0
  let (s, _) := translateHE (.symbol "bar") 0
  (repr v, repr s)
  -- Expected: ($foo, bar) — unchanged

/-! ## Step 2: Correctness Properties -/

open Mettapedia.Languages.MeTTa.OSLFCore.Bridge (atomToPattern patternToAtom)
open Mettapedia.Languages.MeTTa.Translation (heSpaceToPeTTaSpace)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (isMatchCorrectAux isMatchCorrectListAux)

/-- `translateHE` is the identity on variables. -/
theorem translateHE_var (v : String) (s : Nat) :
    translateHE (.var v) s = (.var v, s) := rfl

/-- `translateHE` is the identity on symbols. -/
theorem translateHE_symbol (name : String) (s : Nat) :
    translateHE (.symbol name) s = (.symbol name, s) := rfl

/-- `translateHE` on `(chain E V B)` produces `(let V E' B')`. -/
theorem translateHE_chain (e v body : Atom) (s : Nat) :
    translateHE (.expression [.symbol "chain", e, v, body]) s =
    let (te, s1) := translateHE e s
    let (tb, s2) := translateHE body s1
    (.expression [.symbol "let", v, te, tb], s2) := rfl

/-- `translateHE` on `(collapse-bind X)` produces `(collapse X')`. -/
theorem translateHE_collapse (x : Atom) (s : Nat) :
    translateHE (.expression [.symbol "collapse-bind", x]) s =
    let (tx, s1) := translateHE x s
    (.expression [.symbol "collapse", tx], s1) := rfl

/-- `translateHE` on `(superpose-bind X)` produces `(superpose X')`. -/
theorem translateHE_superpose (x : Atom) (s : Nat) :
    translateHE (.expression [.symbol "superpose-bind", x]) s =
    let (tx, s1) := translateHE x s
    (.expression [.symbol "superpose", tx], s1) := rfl

/-- `translateHE` on `(function (return X))` unwraps to `X'`. -/
theorem translateHE_function_return (x : Atom) (s : Nat) :
    translateHE (.expression [.symbol "function",
      .expression [.symbol "return", x]]) s =
    translateHE x s := rfl

/-- `translateHE` on `(nop X)` produces `(let $fresh X' ())` with fresh supply. -/
theorem translateHE_nop (x : Atom) (s : Nat) :
    translateHE (.expression [.symbol "nop", x]) s =
    let (fresh, s1) := freshVar "discard" s
    let (tx, s2) := translateHE x s1
    (.expression [.symbol "let", fresh, tx, .symbol "()"], s2) := rfl

/-- `translateHE` preserves `atomToPattern` on identity cases. -/
theorem translateHE_identity_preserves (a : Atom) (s : Nat)
    (h : translateHE a s = (a, s)) :
    ∀ p, atomToPattern a = some p → atomToPattern (translateHE a s).1 = some p := by
  intro p hp; simp [h, hp]

/-- Concrete validation: chain translation preserves atomToPattern.
    Verified computationally via `#eval` above; stated as `example` for the record. -/
example : (translateHE (.expression [.symbol "chain",
    .expression [.symbol "+", .symbol "1", .symbol "2"],
    .var "$x", .var "$x"]) 0).1 =
    .expression [.symbol "let", .var "$x",
      .expression [.symbol "+", .symbol "1", .symbol "2"], .var "$x"] := rfl

/-- collapse-bind → collapse preserves structure. -/
example : (translateHE (.expression [.symbol "collapse-bind",
    .expression [.symbol "foo"]]) 0).1 =
    .expression [.symbol "collapse", .expression [.symbol "foo"]] := rfl

/-- function (return X) → X (unwrap). -/
example : (translateHE (.expression [.symbol "function",
    .expression [.symbol "return", .var "$x"]]) 0).1 = .var "$x" := rfl

/-- nop → let with fresh variable. -/
example : (translateHE (.expression [.symbol "nop", .var "$x"]) 0).1 =
    .expression [.symbol "let", .var "$__tr_discard_1", .var "$x", .symbol "()"] := rfl

/-- Variables pass through. -/
example : (translateHE (.var "$y") 42).1 = .var "$y" := rfl

/-- Symbols pass through. -/
example : (translateHE (.symbol "if") 0).1 = .symbol "if" := rfl

/-! ## Step 3: Connection to space-based proof

The key insight: `heSpaceToPeTTaSpace` translates equations via `atomToRule?`,
which uses `atomToPattern` on both sides. `translateHE` rewrites the TERM structure
(chain→let, etc.). These connect because `atomToPattern` maps both the original
and translated forms to patterns — the patterns just have different head symbols.

The space-based proof (`HEPeTTaSound.lean`) already handles the equation-level
correspondence. The translator adds the term-level rewriting that the evaluator
performs BEFORE equations are matched.

So the full picture:
1. HE evaluator calls `metta_call` → matches equations via `queryEquations`
2. The equation LHS (e.g., `(chain E V B)`) matches the current atom
3. The equation RHS is the rewritten form
4. `translateHE` mirrors this: it rewrites `(chain E V B)` to `(let V E B)`
5. `heSpaceToPeTTaSpace` turns both forms into PeTTa rules
6. `simpleMatch_applyBindings_comm` bridges the matching

The connection theorem: translateHE produces atoms whose atomToPattern
corresponds to what heSpaceToPeTTaSpace would produce for the translated equations. -/

/-- If an expression is Translatable, each sub-argument is Translatable. -/
private theorem translatable_args_of_expr (c : String) (args : List Atom)
    (h : Translatable (.expression (.symbol c :: args))) :
    ∀ a ∈ args, Translatable a := by
  simp only [Translatable] at h ⊢
  intro a ha
  unfold atomToPattern at h
  split at h
  · -- c = "λ"
    cases args with
    | nil => cases ha
    | cons body rest =>
      cases rest with
      | nil =>
        simp at h
        cases hb : atomToPattern body <;> simp [hb] at h
        cases ha with | head _ => simp [hb] | tail _ h' => cases h'
      | cons _ _ => simp at h
  · split at h
    · -- c = "subst"
      cases args with
      | nil => cases ha
      | cons body rest =>
        cases rest with
        | nil => simp at h
        | cons repl tail =>
          cases tail with
          | nil =>
            simp at h
            cases hb : atomToPattern body <;> cases hr : atomToPattern repl <;>
              simp [hb, hr] at h
            cases ha with
            | head _ => simp [hb]
            | tail _ h' => cases h' with | head _ => simp [hr] | tail _ h'' => cases h''
          | cons _ _ => simp at h
    · -- general case: simp already simplified h to ∀ a ∈ args, ...
      simp at h
      exact h a ha

/-- An expression with a standard head and Translatable args is Translatable.
    "Standard" = not "λ" and not "subst". -/
private theorem translatable_expr_of_args (c : String) (args : List Atom)
    (hc1 : c ≠ "λ") (hc2 : c ≠ "subst")
    (hall : ∀ a ∈ args, Translatable a) :
    Translatable (.expression (.symbol c :: args)) := by
  simp only [Translatable]
  unfold atomToPattern
  simp only [beq_iff_eq, hc1, ↓reduceIte, hc2]
  -- Need: (filterMap atomToPattern args).length == args.length
  suffices hlen : (args.filterMap atomToPattern).length = args.length by
    simp [hlen]
  induction args with
  | nil => simp
  | cons a as ih =>
    have ⟨p, hp⟩ := translatable_witness a (hall a (.head _))
    simp [hp, ih (fun a' ha' => hall a' (.tail _ ha'))]

private theorem translatable_lambda_singleton (args : List Atom)
    (h : Translatable (.expression (.symbol "λ" :: args))) :
    ∃ body, args = [body] := by
  cases args with
  | nil =>
    unfold Translatable at h
    unfold atomToPattern at h
    simp at h
  | cons body rest =>
    cases rest with
    | nil => exact ⟨body, rfl⟩
    | cons x xs =>
      unfold Translatable at h
      unfold atomToPattern at h
      simp at h

private theorem translatable_subst_pair (args : List Atom)
    (h : Translatable (.expression (.symbol "subst" :: args))) :
    ∃ body repl, args = [body, repl] := by
  cases args with
  | nil =>
    unfold Translatable at h
    unfold atomToPattern at h
    simp at h
  | cons body rest =>
    cases rest with
    | nil =>
      unfold Translatable at h
      unfold atomToPattern at h
      simp at h
    | cons repl tail =>
      cases tail with
      | nil => exact ⟨body, repl, rfl⟩
      | cons x xs =>
        unfold Translatable at h
        unfold atomToPattern at h
        simp at h

private theorem translatable_lambda_of_body (body : Atom) (hbody : Translatable body) :
    Translatable (.expression [.symbol "λ", body]) := by
  obtain ⟨p, hp⟩ := translatable_witness body hbody
  unfold Translatable
  unfold atomToPattern
  simp [hp]

private theorem translatable_subst_of_parts (body repl : Atom)
    (hbody : Translatable body) (hrepl : Translatable repl) :
    Translatable (.expression [.symbol "subst", body, repl]) := by
  obtain ⟨pb, hpb⟩ := translatable_witness body hbody
  obtain ⟨pr, hpr⟩ := translatable_witness repl hrepl
  unfold Translatable
  unfold atomToPattern
  simp [hpb, hpr]

private theorem rebuild_same_head
    (c : String) (args outArgs : List Atom)
    (hsrc : Translatable (.expression (.symbol c :: args)))
    (hlen : outArgs.length = args.length)
    (hall : ∀ a ∈ outArgs, Translatable a) :
    Translatable (.expression (.symbol c :: outArgs)) := by
  by_cases hc1 : c = "λ"
  · subst hc1
    obtain ⟨body, hargs⟩ := translatable_lambda_singleton args hsrc
    subst hargs
    cases outArgs with
    | nil => simp at hlen
    | cons body' rest =>
      cases rest with
      | nil => exact translatable_lambda_of_body body' (hall body' (by simp))
      | cons x xs => simp at hlen
  · by_cases hc2 : c = "subst"
    · subst hc2
      obtain ⟨body, repl, hargs⟩ := translatable_subst_pair args hsrc
      subst hargs
      cases outArgs with
      | nil => simp at hlen
      | cons body' rest =>
        cases rest with
        | nil => simp at hlen
        | cons repl' tail =>
          cases tail with
          | nil =>
            exact translatable_subst_of_parts body' repl'
              (hall body' (by simp)) (hall repl' (by simp))
          | cons x xs => simp at hlen
    · exact translatable_expr_of_args c outArgs hc1 hc2 hall

-- translateHE preserves Translatable: if the input has a successful
-- `atomToPattern`, so does the output.
-- Strategy: the non-expression cases are identity. For expressions,
-- translateHE either rewrites (chain→let, etc.) producing an expression
-- with a standard head + Translatable args, or falls through to the
-- generic case which recurses via translateHEList preserving the head symbol.
--
-- Key helpers: translatable_args_of_expr (extract), translatable_expr_of_args (reassemble).
-- IH provided by well-founded induction on sizeOf.

/-- translateHEList preserves Translatable on each element. -/
private theorem translateHEList_mem_translatable
    (ih : ∀ a' : Atom, sizeOf a' < bound → ∀ s, Translatable a' → Translatable (translateHE a' s).1)
    (xs : List Atom) (s : Nat)
    (hsize : ∀ x ∈ xs, sizeOf x < bound)
    (hall : ∀ x ∈ xs, Translatable x) :
    ∀ x ∈ (translateHE.translateHEList xs s).1, Translatable x := by
  induction xs generalizing s with
  | nil => simp [translateHE.translateHEList]
  | cons a as ih_list =>
    simp only [translateHE.translateHEList]
    intro x hx
    cases hx with
    | head _ => exact ih a (hsize a (.head _)) s (hall a (.head _))
    | tail _ hx' =>
      exact ih_list _
        (fun x hx => hsize x (.tail _ hx))
        (fun x hx => hall x (.tail _ hx)) x hx'

/-- translateHEList preserves list length. -/
private theorem translateHEList_length (xs : List Atom) (s : Nat) :
    (translateHE.translateHEList xs s).1.length = xs.length := by
  induction xs generalizing s with
  | nil => simp [translateHE.translateHEList]
  | cons a as ih => simp [translateHE.translateHEList, ih]

/-- translateHEList on (.symbol c :: args) preserves the symbol head. -/
private theorem translateHEList_cons_symbol (c : String) (args : List Atom) (s : Nat) :
    (translateHE.translateHEList (.symbol c :: args) s).1 =
      .symbol c :: (translateHE.translateHEList args (translateHE (.symbol c) s).2).1 := by
  simp [translateHE.translateHEList, translateHE]

/-! ## Step 4: Stronger Pure-Fragment Preservation -/

/-- `isMatchCorrectAux` propagates from a whole list to any member. -/
private theorem isMatchCorrectAux_of_mem_list
    {ps : List Pattern} {p : Pattern}
    (h : isMatchCorrectListAux ps = true) (hp : p ∈ ps) :
    isMatchCorrectAux p = true := by
  induction ps with
  | nil => cases hp
  | cons q qs ih =>
    simp only [isMatchCorrectListAux, Bool.and_eq_true] at h
    cases hp with
    | head _ => exact h.1
    | tail _ hp' => exact ih h.2 hp'

/-- A pure expression translates to an `.apply` with matching translated arguments. -/
private theorem pure_expr_translation_shape
    (c : String) (args : List Atom) (p : Pattern)
    (hpat : atomToPattern (.expression (.symbol c :: args)) = some p)
    (hmc : isMatchCorrectAux p = true) :
    ∃ patArgs, p = .apply c patArgs ∧
      patArgs = args.filterMap atomToPattern ∧
      patArgs.length = args.length := by
  by_cases hlam : c = "λ"
  · subst hlam
    unfold atomToPattern at hpat
    simp only [beq_self_eq_true, ↓reduceIte] at hpat
    cases args with
    | nil => simp at hpat
    | cons body rest =>
      cases rest with
      | nil =>
        cases hbody : atomToPattern body <;> simp [hbody] at hpat
        subst hpat
        simp [isMatchCorrectAux] at hmc
      | cons _ _ => simp at hpat
  · by_cases hsubst : c = "subst"
    · subst hsubst
      unfold atomToPattern at hpat
      simp only [beq_iff_eq, show "subst" ≠ "λ" by decide, ↓reduceIte, beq_self_eq_true] at hpat
      cases args with
      | nil => simp at hpat
      | cons body rest =>
        cases rest with
        | nil => simp at hpat
        | cons repl tail =>
          cases tail with
          | nil =>
            cases hbody : atomToPattern body <;>
              cases hrepl : atomToPattern repl <;>
              simp [hbody, hrepl] at hpat
            subst hpat
            simp [isMatchCorrectAux] at hmc
          | cons _ _ => simp at hpat
    · unfold atomToPattern at hpat
      simp only [beq_iff_eq, hlam, ↓reduceIte, hsubst] at hpat
      split at hpat
      · rename_i hlen
        injection hpat with hp
        subst hp
        exact ⟨args.filterMap atomToPattern, rfl, rfl, hlen⟩
      · simp at hpat

/-- All arguments of a pure expression are themselves pure. -/
private theorem pure_args_of_expr_translation
    (c : String) (args : List Atom) (p : Pattern)
    (hpat : atomToPattern (.expression (.symbol c :: args)) = some p)
    (hmc : isMatchCorrectAux p = true) :
    ∀ a ∈ args, PureTranslatable a := by
  obtain ⟨patArgs, hpEq, hfm, _⟩ := pure_expr_translation_shape c args p hpat hmc
  subst hpEq
  have hlistmc : isMatchCorrectListAux patArgs = true := by
    simpa [isMatchCorrectAux] using hmc
  intro a ha
  have ⟨q, hq⟩ := filterMap_length_eq_length_implies_some atomToPattern args
    (by rwa [← hfm]) a ha
  exact ⟨q, hq, isMatchCorrectAux_of_mem_list hlistmc
    (hfm ▸ List.mem_filterMap.mpr ⟨a, ha, hq⟩)⟩

/-- A pure symbol-headed expression cannot use the special `atomToPattern` heads. -/
private theorem pureTranslatable_head_standard
    (c : String) (args : List Atom)
    (h : PureTranslatable (.expression (.symbol c :: args))) :
    c ≠ "λ" ∧ c ≠ "subst" := by
  obtain ⟨p, hp, hmc⟩ := h
  constructor
  · intro hlam
    subst hlam
    unfold atomToPattern at hp
    simp only [beq_self_eq_true, ↓reduceIte] at hp
    cases args with
    | nil => simp at hp
    | cons body rest =>
      cases rest with
      | nil =>
        cases hbody : atomToPattern body <;> simp [hbody] at hp
        subst hp
        simp [isMatchCorrectAux] at hmc
      | cons _ _ => simp at hp
  · intro hsubst
    subst hsubst
    unfold atomToPattern at hp
    simp only [beq_iff_eq, show "subst" ≠ "λ" by decide, ↓reduceIte, beq_self_eq_true] at hp
    cases args with
    | nil => simp at hp
    | cons body rest =>
      cases rest with
      | nil => simp at hp
      | cons repl tail =>
        cases tail with
        | nil =>
          cases hbody : atomToPattern body <;>
            cases hrepl : atomToPattern repl <;>
            simp [hbody, hrepl] at hp
          subst hp
          simp [isMatchCorrectAux] at hmc
        | cons _ _ => simp at hp

/-- Wrapper around `pure_args_of_expr_translation` from a `PureTranslatable` premise. -/
private theorem pureTranslatable_args_of_expr
    (c : String) (args : List Atom)
    (h : PureTranslatable (.expression (.symbol c :: args))) :
    ∀ a ∈ args, PureTranslatable a := by
  obtain ⟨p, hp, hmc⟩ := h
  exact pure_args_of_expr_translation c args p hp hmc

/-- `translateHEList` preserves `PureTranslatable` on each element. -/
private theorem translateHEList_mem_pure
    (ih : ∀ a' : Atom, sizeOf a' < bound →
      ∀ s, PureTranslatable a' → PureTranslatable (translateHE a' s).1)
    (xs : List Atom) (s : Nat)
    (hsize : ∀ x ∈ xs, sizeOf x < bound)
    (hall : ∀ x ∈ xs, PureTranslatable x) :
    ∀ x ∈ (translateHE.translateHEList xs s).1, PureTranslatable x := by
  induction xs generalizing s with
  | nil => simp [translateHE.translateHEList]
  | cons a as ih_list =>
    simp only [translateHE.translateHEList]
    intro x hx
    cases hx with
    | head _ => exact ih a (hsize a (.head _)) s (hall a (.head _))
    | tail _ hx' =>
      exact ih_list _
        (fun x hx => hsize x (.tail _ hx))
        (fun x hx => hall x (.tail _ hx)) x hx'

theorem translateHE_translatable (a : Atom) (s : Nat)
    (h : Translatable a) : Translatable (translateHE a s).1 := by
  -- Well-founded induction on sizeOf a
  have : ∀ (bound : Nat) (a : Atom), sizeOf a ≤ bound →
      ∀ s, Translatable a → Translatable (translateHE a s).1 := by
    intro bound
    induction bound with
    | zero =>
      intro a ha s _
      exfalso
      cases a <;> simp_all
    | succ n ih_bound =>
      intro a ha s ht
      cases a with
      | var v => exact ht
      | symbol nm => exact ht
      | grounded g => exact ht
      | expression es =>
        -- translateHE (.expression es) s: case-splits on es
        -- All rewrite cases produce .expression [.symbol head, ...] with standard head.
        -- Generic case: .expression (translateHEList es s).1
        -- Need: the output is Translatable.
        --
        -- From ht: atomToPattern (.expression es) succeeds, so es = .symbol c :: args
        -- with all args Translatable.
        cases es with
        | nil => exfalso; simp [Translatable, atomToPattern] at ht
        | cons hd args =>
          cases hd with
          | symbol c =>
            have hargs := translatable_args_of_expr c args ht
            have harg_le : ∀ a' ∈ args, sizeOf a' ≤ n := by
              intro a' ha'
              have hlt : sizeOf a' < sizeOf (.symbol c :: args) :=
                List.sizeOf_lt_of_mem (a := a') (as := .symbol c :: args)
                  (by exact List.mem_cons_of_mem _ ha')
              simp at hlt ha
              omega
            have harg_ih : ∀ a' ∈ args, ∀ s', Translatable a' →
                Translatable (translateHE a' s').1 := by
              intro a' ha' s' ht'
              exact ih_bound a'
                (harg_le a' ha') s' ht'
            have hall_translated : ∀ x ∈ (translateHE.translateHEList args s).1, Translatable x := by
              exact translateHEList_mem_translatable (bound := Nat.succ n)
                (fun a' hlt s' ht' => ih_bound a' (Nat.le_of_lt_succ hlt) s' ht')
                args s
                (fun x hx => Nat.lt_succ_of_le (harg_le x hx))
                hargs
            have hgeneric :
                Translatable (.expression (.symbol c :: (translateHE.translateHEList args s).1)) := by
              exact rebuild_same_head c args (translateHE.translateHEList args s).1
                ht (translateHEList_length args s) hall_translated
            by_cases hswitch : c = "switch"
            · subst hswitch
              cases args with
              | nil =>
                simpa [translateHE, translateHE.translateHEList] using hgeneric
              | cons scrut branches =>
                have hscrut : Translatable (translateHE scrut s).1 :=
                  harg_ih scrut (by simp) s (hargs scrut (by simp))
                have hbranches :
                    ∀ x ∈ (translateHE.translateHEList branches (translateHE scrut s).2).1,
                      Translatable x := by
                  exact translateHEList_mem_translatable (bound := Nat.succ n)
                    (fun a' hlt s' ht' => ih_bound a' (Nat.le_of_lt_succ hlt) s' ht')
                    branches (translateHE scrut s).2
                    (fun x hx => Nat.lt_succ_of_le (harg_le x (by simp [hx])))
                    (fun x hx => hargs x (by simp [hx]))
                apply translatable_expr_of_args "case" ((translateHE scrut s).1 ::
                  (translateHE.translateHEList branches (translateHE scrut s).2).1)
                · decide
                · decide
                · intro x hx
                  simp at hx
                  rcases hx with rfl | hx
                  · exact hscrut
                  · exact hbranches x hx
            · by_cases hswitchm : c = "switch-minimal"
              · subst hswitchm
                cases args with
                | nil =>
                  simpa [translateHE, translateHE.translateHEList] using hgeneric
                | cons scrut branches =>
                  have hscrut : Translatable (translateHE scrut s).1 :=
                    harg_ih scrut (by simp) s (hargs scrut (by simp))
                  have hbranches :
                      ∀ x ∈ (translateHE.translateHEList branches (translateHE scrut s).2).1,
                        Translatable x := by
                    exact translateHEList_mem_translatable (bound := Nat.succ n)
                      (fun a' hlt s' ht' => ih_bound a' (Nat.le_of_lt_succ hlt) s' ht')
                      branches (translateHE scrut s).2
                      (fun x hx => Nat.lt_succ_of_le (harg_le x (by simp [hx])))
                      (fun x hx => hargs x (by simp [hx]))
                  apply translatable_expr_of_args "case" ((translateHE scrut s).1 ::
                    (translateHE.translateHEList branches (translateHE scrut s).2).1)
                  · decide
                  · decide
                  · intro x hx
                    simp at hx
                    rcases hx with rfl | hx
                    · exact hscrut
                    · exact hbranches x hx
              · by_cases hchain : c = "chain"
                · subst hchain
                  cases args with
                  | nil =>
                    simpa [translateHE, translateHE.translateHEList] using hgeneric
                  | cons e rest =>
                    cases rest with
                    | nil =>
                      simpa [translateHE, translateHE.translateHEList] using hgeneric
                    | cons v rest =>
                      cases rest with
                      | nil =>
                        simpa [translateHE, translateHE.translateHEList] using hgeneric
                      | cons body rest =>
                        cases rest with
                        | nil =>
                          have hv : Translatable v := hargs v (by simp)
                          have he : Translatable (translateHE e s).1 :=
                            harg_ih e (by simp) s (hargs e (by simp))
                          have hbody : Translatable (translateHE body (translateHE e s).2).1 :=
                            harg_ih body (by simp) (translateHE e s).2 (hargs body (by simp))
                          apply translatable_expr_of_args "let"
                            [v, (translateHE e s).1, (translateHE body (translateHE e s).2).1]
                          · decide
                          · decide
                          · intro x hx
                            simp at hx
                            rcases hx with rfl | rfl | rfl
                            · exact hv
                            · exact he
                            · exact hbody
                        | cons x xs =>
                          simpa [translateHE, translateHE.translateHEList] using hgeneric
                · by_cases hcollapse : c = "collapse-bind"
                  · subst hcollapse
                    cases args with
                    | nil =>
                      simpa [translateHE, translateHE.translateHEList] using hgeneric
                    | cons inner rest =>
                      cases rest with
                      | nil =>
                        have hinner : Translatable (translateHE inner s).1 :=
                          harg_ih inner (by simp) s (hargs inner (by simp))
                        apply translatable_expr_of_args "collapse" [(translateHE inner s).1]
                        · decide
                        · decide
                        · intro x hx
                          simp at hx
                          rcases hx with rfl
                          exact hinner
                      | cons x xs =>
                        simpa [translateHE, translateHE.translateHEList] using hgeneric
                  · by_cases hsuperpose : c = "superpose-bind"
                    · subst hsuperpose
                      cases args with
                      | nil =>
                        simpa [translateHE, translateHE.translateHEList] using hgeneric
                      | cons inner rest =>
                        cases rest with
                        | nil =>
                          have hinner : Translatable (translateHE inner s).1 :=
                            harg_ih inner (by simp) s (hargs inner (by simp))
                          apply translatable_expr_of_args "superpose" [(translateHE inner s).1]
                          · decide
                          · decide
                          · intro x hx
                            simp at hx
                            rcases hx with rfl
                            exact hinner
                        | cons x xs =>
                          simpa [translateHE, translateHE.translateHEList] using hgeneric
                    · by_cases hatomsubst : c = "atom-subst"
                      · subst hatomsubst
                        cases args with
                        | nil =>
                          simpa [translateHE, translateHE.translateHEList] using hgeneric
                        | cons atom rest =>
                          cases rest with
                          | nil =>
                            simpa [translateHE, translateHE.translateHEList] using hgeneric
                          | cons v rest =>
                            cases rest with
                            | nil =>
                              simpa [translateHE, translateHE.translateHEList] using hgeneric
                            | cons tmpl rest =>
                              cases rest with
                              | nil =>
                                have hv : Translatable v := hargs v (by simp)
                                have hatom : Translatable (translateHE atom s).1 :=
                                  harg_ih atom (by simp) s (hargs atom (by simp))
                                have htmpl : Translatable (translateHE tmpl (translateHE atom s).2).1 :=
                                  harg_ih tmpl (by simp) (translateHE atom s).2 (hargs tmpl (by simp))
                                apply translatable_expr_of_args "let"
                                  [v, (translateHE atom s).1, (translateHE tmpl (translateHE atom s).2).1]
                                · decide
                                · decide
                                · intro x hx
                                  simp at hx
                                  rcases hx with rfl | rfl | rfl
                                  · exact hv
                                  · exact hatom
                                  · exact htmpl
                              | cons x xs =>
                                simpa [translateHE, translateHE.translateHEList] using hgeneric
                      · by_cases hnop : c = "nop"
                        · subst hnop
                          cases args with
                          | nil =>
                            simpa [translateHE, translateHE.translateHEList] using hgeneric
                          | cons x rest =>
                            cases rest with
                            | nil =>
                              have htx : Translatable (translateHE x (freshVar "discard" s).2).1 :=
                                harg_ih x (by simp) (freshVar "discard" s).2 (hargs x (by simp))
                              have hfresh : Translatable (freshVar "discard" s).1 := by
                                simp [freshVar, Translatable, atomToPattern]
                              have hlet :
                                  Translatable
                                    (.expression
                                      [.symbol "let", (freshVar "discard" s).1,
                                        (translateHE x (freshVar "discard" s).2).1, .symbol "()"]) := by
                                apply translatable_expr_of_args "let"
                                  [(freshVar "discard" s).1,
                                    (translateHE x (freshVar "discard" s).2).1, .symbol "()"]
                                · decide
                                · decide
                                · intro a ha
                                  simp at ha
                                  rcases ha with rfl | rfl | rfl
                                  · exact hfresh
                                  · exact htx
                                  · simp [Translatable, atomToPattern]
                              simpa [translateHE, freshVar] using hlet
                            | cons y ys =>
                              simpa [translateHE, translateHE.translateHEList] using hgeneric
                        · by_cases hfunction : c = "function"
                          · subst hfunction
                            cases args with
                            | nil =>
                              simpa [translateHE, translateHE.translateHEList] using hgeneric
                            | cons x rest =>
                              cases rest with
                              | nil =>
                                cases x with
                                | var v =>
                                  simpa [translateHE, translateHE.translateHEList] using hgeneric
                                | symbol nm =>
                                  simpa [translateHE, translateHE.translateHEList] using hgeneric
                                | grounded g =>
                                  simpa [translateHE, translateHE.translateHEList] using hgeneric
                                | expression es' =>
                                  cases es' with
                                  | nil =>
                                    simpa [translateHE, translateHE.translateHEList] using hgeneric
                                  | cons hd' tail' =>
                                    cases hd' with
                                    | symbol c' =>
                                      by_cases hreturn : c' = "return"
                                      · subst hreturn
                                        cases tail' with
                                        | nil =>
                                          simpa [translateHE, translateHE.translateHEList] using hgeneric
                                        | cons inner rest' =>
                                          cases rest' with
                                          | nil =>
                                            have hret : Translatable (Atom.expression [Atom.symbol "return", inner]) :=
                                              hargs (Atom.expression [Atom.symbol "return", inner]) (by simp)
                                            have hinner : Translatable inner :=
                                              translatable_args_of_expr "return" [inner] hret inner (by simp)
                                            have hret_le : sizeOf (Atom.expression [Atom.symbol "return", inner]) ≤ n :=
                                              harg_le (Atom.expression [Atom.symbol "return", inner]) (by simp)
                                            have hinner_le : sizeOf inner ≤ n := by
                                              have hlt : sizeOf inner < sizeOf (.symbol "return" :: [inner]) :=
                                                List.sizeOf_lt_of_mem (a := inner)
                                                  (as := [.symbol "return", inner]) (by simp)
                                              simp at hlt hret_le
                                              omega
                                            simpa [translateHE] using ih_bound inner hinner_le s hinner
                                          | cons y ys =>
                                            simpa [translateHE, translateHE.translateHEList] using hgeneric
                                      · simpa [translateHE, translateHE.translateHEList, hreturn] using hgeneric
                                    | _ =>
                                      simpa [translateHE, translateHE.translateHEList] using hgeneric
                              | cons y ys =>
                                simpa [translateHE, translateHE.translateHEList] using hgeneric
                          · simpa [translateHE, translateHE.translateHEList, hswitch, hswitchm, hchain,
                              hcollapse, hsuperpose, hatomsubst, hnop, hfunction] using hgeneric
          | _ =>
            -- non-symbol head: atomToPattern fails, contradicting Translatable
            exfalso; simp [Translatable, atomToPattern] at ht
  exact this (sizeOf a) a (Nat.le_refl _) s h

/-- `translateHE` preserves the stronger pure fragment used by the soundness bridge. -/
theorem translateHE_preserves_pureTranslatable (a : Atom) (s : Nat)
    (h : PureTranslatable a) : PureTranslatable (translateHE a s).1 := by
  have : ∀ (bound : Nat) (a : Atom), sizeOf a ≤ bound →
      ∀ s, PureTranslatable a → PureTranslatable (translateHE a s).1 := by
    intro bound
    induction bound with
    | zero =>
      intro a ha s h
      exfalso
      cases a <;> simp_all
    | succ n ih_bound =>
      intro a ha s ht
      cases a with
      | var v => exact pureTranslatable_var v
      | symbol nm => exact pureTranslatable_symbol nm
      | grounded g =>
        exfalso
        obtain ⟨_, hp, _⟩ := ht
        simp [atomToPattern] at hp
      | expression es =>
        cases es with
        | nil =>
          exfalso
          obtain ⟨_, hp, _⟩ := ht
          simp [atomToPattern] at hp
        | cons hd args =>
          cases hd with
          | symbol c =>
            have hargs : ∀ a ∈ args, PureTranslatable a :=
              pureTranslatable_args_of_expr c args ht
            have hcstd : c ≠ "λ" ∧ c ≠ "subst" :=
              pureTranslatable_head_standard c args ht
            have harg_le : ∀ a' ∈ args, sizeOf a' ≤ n := by
              intro a' ha'
              have hlt : sizeOf a' < sizeOf (.symbol c :: args) :=
                List.sizeOf_lt_of_mem (a := a') (as := .symbol c :: args)
                  (by exact List.mem_cons_of_mem _ ha')
              simp at hlt ha
              omega
            have harg_ih : ∀ a' ∈ args, ∀ s', PureTranslatable a' →
                PureTranslatable (translateHE a' s').1 := by
              intro a' ha' s' ht'
              exact ih_bound a' (harg_le a' ha') s' ht'
            have hall_translated :
                ∀ x ∈ (translateHE.translateHEList args s).1,
                  PureTranslatable x := by
              exact translateHEList_mem_pure (bound := Nat.succ n)
                (fun a' hlt s' ht' => ih_bound a' (Nat.le_of_lt_succ hlt) s' ht')
                args s
                (fun x hx => Nat.lt_succ_of_le (harg_le x hx))
                hargs
            have hgeneric :
                PureTranslatable (.expression (.symbol c :: (translateHE.translateHEList args s).1)) := by
              exact pureTranslatable_expr c (translateHE.translateHEList args s).1
                hcstd.1 hcstd.2 hall_translated
            by_cases hswitch : c = "switch"
            · subst hswitch
              cases args with
              | nil =>
                simpa [translateHE, translateHE.translateHEList] using hgeneric
              | cons scrut branches =>
                have hscrut : PureTranslatable (translateHE scrut s).1 :=
                  harg_ih scrut (by simp) s (hargs scrut (by simp))
                have hbranches :
                    ∀ x ∈ (translateHE.translateHEList branches (translateHE scrut s).2).1,
                      PureTranslatable x := by
                  exact translateHEList_mem_pure (bound := Nat.succ n)
                    (fun a' hlt s' ht' => ih_bound a' (Nat.le_of_lt_succ hlt) s' ht')
                    branches (translateHE scrut s).2
                    (fun x hx => Nat.lt_succ_of_le (harg_le x (by simp [hx])))
                    (fun x hx => hargs x (by simp [hx]))
                exact pureTranslatable_expr "case"
                  ((translateHE scrut s).1 ::
                    (translateHE.translateHEList branches (translateHE scrut s).2).1)
                  (by decide) (by decide) (by
                    intro x hx
                    simp at hx
                    rcases hx with rfl | hx
                    · exact hscrut
                    · exact hbranches x hx)
            · by_cases hswitchm : c = "switch-minimal"
              · subst hswitchm
                cases args with
                | nil =>
                  simpa [translateHE, translateHE.translateHEList] using hgeneric
                | cons scrut branches =>
                  have hscrut : PureTranslatable (translateHE scrut s).1 :=
                    harg_ih scrut (by simp) s (hargs scrut (by simp))
                  have hbranches :
                      ∀ x ∈ (translateHE.translateHEList branches (translateHE scrut s).2).1,
                        PureTranslatable x := by
                    exact translateHEList_mem_pure (bound := Nat.succ n)
                      (fun a' hlt s' ht' => ih_bound a' (Nat.le_of_lt_succ hlt) s' ht')
                      branches (translateHE scrut s).2
                      (fun x hx => Nat.lt_succ_of_le (harg_le x (by simp [hx])))
                      (fun x hx => hargs x (by simp [hx]))
                  exact pureTranslatable_expr "case"
                    ((translateHE scrut s).1 ::
                      (translateHE.translateHEList branches (translateHE scrut s).2).1)
                    (by decide) (by decide) (by
                      intro x hx
                      simp at hx
                      rcases hx with rfl | hx
                      · exact hscrut
                      · exact hbranches x hx)
              · by_cases hchain : c = "chain"
                · subst hchain
                  cases args with
                  | nil =>
                    simpa [translateHE, translateHE.translateHEList] using hgeneric
                  | cons e rest =>
                    cases rest with
                    | nil =>
                      simpa [translateHE, translateHE.translateHEList] using hgeneric
                    | cons v rest =>
                      cases rest with
                      | nil =>
                        simpa [translateHE, translateHE.translateHEList] using hgeneric
                      | cons body rest =>
                        cases rest with
                        | nil =>
                          have hv : PureTranslatable v := hargs v (by simp)
                          have he : PureTranslatable (translateHE e s).1 :=
                            harg_ih e (by simp) s (hargs e (by simp))
                          have hbody : PureTranslatable (translateHE body (translateHE e s).2).1 :=
                            harg_ih body (by simp) (translateHE e s).2 (hargs body (by simp))
                          exact pureTranslatable_expr "let"
                            [v, (translateHE e s).1, (translateHE body (translateHE e s).2).1]
                            (by decide) (by decide) (by
                              intro x hx
                              simp at hx
                              rcases hx with rfl | rfl | rfl
                              · exact hv
                              · exact he
                              · exact hbody)
                        | cons x xs =>
                          simpa [translateHE, translateHE.translateHEList] using hgeneric
                · by_cases hcollapse : c = "collapse-bind"
                  · subst hcollapse
                    cases args with
                    | nil =>
                      simpa [translateHE, translateHE.translateHEList] using hgeneric
                    | cons inner rest =>
                      cases rest with
                      | nil =>
                        have hinner : PureTranslatable (translateHE inner s).1 :=
                          harg_ih inner (by simp) s (hargs inner (by simp))
                        exact pureTranslatable_expr "collapse" [(translateHE inner s).1]
                          (by decide) (by decide) (by
                            intro x hx
                            simp at hx
                            rcases hx with rfl
                            exact hinner)
                      | cons x xs =>
                        simpa [translateHE, translateHE.translateHEList] using hgeneric
                  · by_cases hsuperpose : c = "superpose-bind"
                    · subst hsuperpose
                      cases args with
                      | nil =>
                        simpa [translateHE, translateHE.translateHEList] using hgeneric
                      | cons inner rest =>
                        cases rest with
                        | nil =>
                          have hinner : PureTranslatable (translateHE inner s).1 :=
                            harg_ih inner (by simp) s (hargs inner (by simp))
                          exact pureTranslatable_expr "superpose" [(translateHE inner s).1]
                            (by decide) (by decide) (by
                              intro x hx
                              simp at hx
                              rcases hx with rfl
                              exact hinner)
                        | cons x xs =>
                          simpa [translateHE, translateHE.translateHEList] using hgeneric
                    · by_cases hatomsubst : c = "atom-subst"
                      · subst hatomsubst
                        cases args with
                        | nil =>
                          simpa [translateHE, translateHE.translateHEList] using hgeneric
                        | cons atom rest =>
                          cases rest with
                          | nil =>
                            simpa [translateHE, translateHE.translateHEList] using hgeneric
                          | cons v rest =>
                            cases rest with
                            | nil =>
                              simpa [translateHE, translateHE.translateHEList] using hgeneric
                            | cons tmpl rest =>
                              cases rest with
                              | nil =>
                                have hv : PureTranslatable v := hargs v (by simp)
                                have hatom : PureTranslatable (translateHE atom s).1 :=
                                  harg_ih atom (by simp) s (hargs atom (by simp))
                                have htmpl :
                                    PureTranslatable (translateHE tmpl (translateHE atom s).2).1 :=
                                  harg_ih tmpl (by simp) (translateHE atom s).2 (hargs tmpl (by simp))
                                exact pureTranslatable_expr "let"
                                  [v, (translateHE atom s).1,
                                    (translateHE tmpl (translateHE atom s).2).1]
                                  (by decide) (by decide) (by
                                    intro x hx
                                    simp at hx
                                    rcases hx with rfl | rfl | rfl
                                    · exact hv
                                    · exact hatom
                                    · exact htmpl)
                              | cons x xs =>
                                simpa [translateHE, translateHE.translateHEList] using hgeneric
                      · by_cases hnop : c = "nop"
                        · subst hnop
                          cases args with
                          | nil =>
                            simpa [translateHE, translateHE.translateHEList] using hgeneric
                          | cons x rest =>
                            cases rest with
                            | nil =>
                              have htx :
                                  PureTranslatable (translateHE x (freshVar "discard" s).2).1 :=
                                harg_ih x (by simp) (freshVar "discard" s).2 (hargs x (by simp))
                              have hfresh : PureTranslatable (freshVar "discard" s).1 := by
                                simp [freshVar, pureTranslatable_var]
                              have hunit : PureTranslatable (.symbol "()") :=
                                pureTranslatable_symbol "()"
                              have hlet :
                                  PureTranslatable
                                    (.expression
                                      [.symbol "let", (freshVar "discard" s).1,
                                        (translateHE x (freshVar "discard" s).2).1, .symbol "()"]) := by
                                exact pureTranslatable_expr "let"
                                  [(freshVar "discard" s).1,
                                    (translateHE x (freshVar "discard" s).2).1, .symbol "()"]
                                  (by decide) (by decide) (by
                                    intro a ha
                                    simp at ha
                                    rcases ha with rfl | rfl | rfl
                                    · exact hfresh
                                    · exact htx
                                    · exact hunit)
                              simpa [translateHE, freshVar] using hlet
                            | cons y ys =>
                              simpa [translateHE, translateHE.translateHEList] using hgeneric
                        · by_cases hfunction : c = "function"
                          · subst hfunction
                            cases args with
                            | nil =>
                              simpa [translateHE, translateHE.translateHEList] using hgeneric
                            | cons x rest =>
                              cases rest with
                              | nil =>
                                cases x with
                                | var v =>
                                  simpa [translateHE, translateHE.translateHEList] using hgeneric
                                | symbol nm =>
                                  simpa [translateHE, translateHE.translateHEList] using hgeneric
                                | grounded g =>
                                  simpa [translateHE, translateHE.translateHEList] using hgeneric
                                | expression es' =>
                                  cases es' with
                                  | nil =>
                                    simpa [translateHE, translateHE.translateHEList] using hgeneric
                                  | cons hd' tail' =>
                                    cases hd' with
                                    | symbol c' =>
                                      by_cases hreturn : c' = "return"
                                      · subst hreturn
                                        cases tail' with
                                        | nil =>
                                          simpa [translateHE, translateHE.translateHEList] using hgeneric
                                        | cons inner rest' =>
                                          cases rest' with
                                          | nil =>
                                            have hret :
                                                PureTranslatable
                                                  (Atom.expression [Atom.symbol "return", inner]) :=
                                              hargs (Atom.expression [Atom.symbol "return", inner]) (by simp)
                                            have hinner : PureTranslatable inner :=
                                              pureTranslatable_args_of_expr "return" [inner] hret inner (by simp)
                                            have hret_le :
                                                sizeOf (Atom.expression [Atom.symbol "return", inner]) ≤ n :=
                                              harg_le (Atom.expression [Atom.symbol "return", inner]) (by simp)
                                            have hinner_le : sizeOf inner ≤ n := by
                                              have hlt : sizeOf inner < sizeOf (.symbol "return" :: [inner]) :=
                                                List.sizeOf_lt_of_mem (a := inner)
                                                  (as := [.symbol "return", inner]) (by simp)
                                              simp at hlt hret_le
                                              omega
                                            simpa [translateHE] using ih_bound inner hinner_le s hinner
                                          | cons y ys =>
                                            simpa [translateHE, translateHE.translateHEList] using hgeneric
                                      · simpa [translateHE, translateHE.translateHEList, hreturn] using hgeneric
                                    | _ =>
                                      simpa [translateHE, translateHE.translateHEList] using hgeneric
                              | cons y ys =>
                                simpa [translateHE, translateHE.translateHEList] using hgeneric
                          · simpa [translateHE, translateHE.translateHEList, hswitch, hswitchm, hchain,
                              hcollapse, hsuperpose, hatomsubst, hnop, hfunction] using hgeneric
          | _ =>
            exfalso
            obtain ⟨_, hp, _⟩ := ht
            simp [atomToPattern] at hp
  exact this (sizeOf a) a (Nat.le_refl _) s h

/-- Executable translation stays inside the proved HE↔PeTTa bridge domain:
    if the input is in the `PureTranslatable` fragment used by
    `HEPeTTaSound.lean`, the output still admits an `atomToPattern` witness. -/
theorem translateHE_preserves_soundness_domain (a : Atom) (s : Nat)
    (h : PureTranslatable a) :
    Translatable (translateHE a s).1 :=
  PureTranslatable.toTranslatable (translateHE_preserves_pureTranslatable a s h)

/-- Concrete pattern witness for the translated output, useful as a theorem-level
    guard that the executable translator stays aligned with the proved fragment. -/
theorem translateHE_pattern_witness (a : Atom) (s : Nat)
    (h : PureTranslatable a) :
    ∃ p, atomToPattern (translateHE a s).1 = some p := by
  exact translatable_witness _ (translateHE_preserves_soundness_domain a s h)

/-! ## Task 1: translatePeTTa alignment -/

/-- translatePeTTaList preserves list length. -/
private theorem translatePeTTaList_length (xs : List Atom) (s : Nat) :
    (translatePeTTa.translatePeTTaList xs s).1.length = xs.length := by
  induction xs generalizing s with
  | nil => simp [translatePeTTa.translatePeTTaList]
  | cons a as ih => simp [translatePeTTa.translatePeTTaList, ih]

/-- translatePeTTaList preserves Translatable on each element (given IH). -/
private theorem translatePeTTaList_mem_translatable
    (ih : ∀ a' : Atom, sizeOf a' < bound → ∀ s, Translatable a' → Translatable (translatePeTTa a' s).1)
    (xs : List Atom) (s : Nat)
    (hsize : ∀ x ∈ xs, sizeOf x < bound)
    (hall : ∀ x ∈ xs, Translatable x) :
    ∀ x ∈ (translatePeTTa.translatePeTTaList xs s).1, Translatable x := by
  induction xs generalizing s with
  | nil => simp [translatePeTTa.translatePeTTaList]
  | cons a as ih_list =>
    simp only [translatePeTTa.translatePeTTaList]
    intro x hx
    cases hx with
    | head _ => exact ih a (hsize a (.head _)) s (hall a (.head _))
    | tail _ hx' =>
      exact ih_list _
        (fun x hx => hsize x (.tail _ hx))
        (fun x hx => hall x (.tail _ hx)) x hx'

/-- Variadic `progn` translation preserves `Translatable`. -/
private theorem translatePeTTaProgn_translatable
    (args : List Atom)
    (step : ∀ a ∈ args, ∀ s, Translatable a → Translatable (translatePeTTa a s).1)
    (s : Nat)
    (hall : ∀ a ∈ args, Translatable a) :
    Translatable (translatePeTTa.translatePeTTaProgn args s).1 := by
  induction args generalizing s with
  | nil =>
      simp [translatePeTTa.translatePeTTaProgn, Translatable, atomToPattern]
  | cons a rest ih =>
      cases rest with
      | nil =>
          simpa [translatePeTTa.translatePeTTaProgn] using
            step a (by simp) s (hall a (by simp))
      | cons b bs =>
          have hfresh : Translatable (freshVar "discard" s).1 := by
            simp [freshVar, Translatable, atomToPattern]
          have ha : Translatable (translatePeTTa a (freshVar "discard" s).2).1 := by
            exact step a (by simp) _ (hall a (by simp))
          have hrest :
              Translatable
                (translatePeTTa.translatePeTTaProgn (b :: bs)
                  (translatePeTTa a (freshVar "discard" s).2).2).1 := by
            exact ih
              (fun x hx s' hxtr => step x (by simp [hx]) s' hxtr)
              _
              (fun x hx => hall x (by simp [hx]))
          exact translatable_expr_of_args "let"
            [(freshVar "discard" s).1,
             (translatePeTTa a (freshVar "discard" s).2).1,
             (translatePeTTa.translatePeTTaProgn (b :: bs)
               (translatePeTTa a (freshVar "discard" s).2).2).1]
            (by decide) (by decide) (by
              intro x hx
              simp at hx
              rcases hx with rfl | rfl | rfl
              · exact hfresh
              · exact ha
              · exact hrest)

/-- The tail of a variadic `prog1` translation preserves `Translatable`. -/
private theorem translatePeTTaProg1Rest_translatable
    (args : List Atom) (resultVar : Atom)
    (hresult : Translatable resultVar)
    (step : ∀ a ∈ args, ∀ s, Translatable a → Translatable (translatePeTTa a s).1)
    (s : Nat)
    (hall : ∀ a ∈ args, Translatable a) :
    Translatable (translatePeTTa.translatePeTTaProg1Rest args resultVar s).1 := by
  induction args generalizing resultVar s with
  | nil =>
      simpa [translatePeTTa.translatePeTTaProg1Rest] using hresult
  | cons a rest ih =>
      have hfresh : Translatable (freshVar "discard" s).1 := by
        simp [freshVar, Translatable, atomToPattern]
      have ha : Translatable (translatePeTTa a (freshVar "discard" s).2).1 := by
        exact step a (by simp) _ (hall a (by simp))
      have hrest :
          Translatable
            (translatePeTTa.translatePeTTaProg1Rest rest resultVar
              (translatePeTTa a (freshVar "discard" s).2).2).1 := by
        exact ih resultVar hresult
          (fun x hx s' hxtr => step x (by simp [hx]) s' hxtr)
          _
          (fun x hx => hall x (by simp [hx]))
      exact translatable_expr_of_args "let"
        [(freshVar "discard" s).1,
         (translatePeTTa a (freshVar "discard" s).2).1,
         (translatePeTTa.translatePeTTaProg1Rest rest resultVar
           (translatePeTTa a (freshVar "discard" s).2).2).1]
        (by decide) (by decide) (by
          intro x hx
          simp at hx
          rcases hx with rfl | rfl | rfl
          · exact hfresh
          · exact ha
          · exact hrest)

/-- Variadic `prog1` translation preserves `Translatable`. -/
private theorem translatePeTTaProg1_translatable
    (args : List Atom)
    (step : ∀ a ∈ args, ∀ s, Translatable a → Translatable (translatePeTTa a s).1)
    (s : Nat)
    (hall : ∀ a ∈ args, Translatable a) :
    Translatable (translatePeTTa.translatePeTTaProg1 args s).1 := by
  induction args generalizing s with
  | nil =>
      simp [translatePeTTa.translatePeTTaProg1, Translatable, atomToPattern]
  | cons a rest ih =>
      cases rest with
      | nil =>
          simpa [translatePeTTa.translatePeTTaProg1] using
            step a (by simp) s (hall a (by simp))
      | cons b bs =>
          have hresult : Translatable (freshVar "result" s).1 := by
            simp [freshVar, Translatable, atomToPattern]
          have ha : Translatable (translatePeTTa a (freshVar "result" s).2).1 := by
            exact step a (by simp) _ (hall a (by simp))
          have hrest :
              Translatable
                (translatePeTTa.translatePeTTaProg1Rest (b :: bs)
                  (freshVar "result" s).1
                  (translatePeTTa a (freshVar "result" s).2).2).1 := by
            exact translatePeTTaProg1Rest_translatable (b :: bs)
              (freshVar "result" s).1 hresult
              (fun x hx s' hxtr => step x (by simp [hx]) s' hxtr)
              _
              (fun x hx => hall x (by simp [hx]))
          exact translatable_expr_of_args "let"
            [(freshVar "result" s).1,
             (translatePeTTa a (freshVar "result" s).2).1,
             (translatePeTTa.translatePeTTaProg1Rest (b :: bs)
               (freshVar "result" s).1
               (translatePeTTa a (freshVar "result" s).2).2).1]
            (by decide) (by decide) (by
              intro x hx
              simp at hx
              rcases hx with rfl | rfl | rfl
              · exact hresult
              · exact ha
              · exact hrest)

/-!
The old universal theorem

```
Translatable a → Translatable (translatePeTTa a s).1
```

is no longer honest once `foldall` is executable. A source such as
`(foldall $f goal init)` is syntactically translatable, but lowers to an HE term
whose reducer position is not pattern-translatable unless `$f` is restricted to a
first-order callable fragment. The validated PeTTa-side theorem therefore appears
later, after the first-order reducer predicate is defined.
-/

/-! ## Roundtrip: HE → PeTTa → HE idempotence

The roundtrip `translatePeTTa ∘ translateHE` does NOT recover the original term.
It produces the PeTTa-normalized form:
- `(chain E V B)` → `(let V E B)` (head rename, not reversed)
- `(nop X)` → `(let $fresh X ())` (administrative let, not reversed)
- `(function (return X))` → `X` (unwrap, not reversed)

But the roundtrip is **idempotent**: after one HE→PeTTa pass, the result is
already in PeTTa normal form, so `translateHE (translatePeTTa (translateHE a s).1 s').1 s''`
produces the same PeTTa normal form as `translateHE a s`.

More precisely: `translateHE` is idempotent on PeTTa-normal terms, because
PeTTa-normal terms have no `chain`, `nop`, `collapse-bind`, `superpose-bind`,
`atom-subst`, or `function/return` heads — so `translateHE` is identity on them. -/

/-- A term is in **PeTTa normal form**: no HE-specific constructs that
    `translateHE` would rewrite. `translateHE` is identity on such terms. -/
def isPeTTaNormal : Atom → Bool
  | .expression (.symbol "chain" :: _) => false
  | .expression [.symbol "collapse-bind", _] => false
  | .expression [.symbol "superpose-bind", _] => false
  | .expression (.symbol "switch" :: _ :: _) => false
  | .expression (.symbol "switch-minimal" :: _ :: _) => false
  | .expression [.symbol "atom-subst", _, _, _] => false
  | .expression [.symbol "nop", _] => false
  | .expression [.symbol "function", .expression [.symbol "return", _]] => false
  | _ => true

/-- `translateHE` is identity on PeTTa-normal atoms (non-expression case). -/
theorem translateHE_id_var (v : String) (s : Nat) :
    translateHE (.var v) s = (.var v, s) := rfl

theorem translateHE_id_symbol (nm : String) (s : Nat) :
    translateHE (.symbol nm) s = (.symbol nm, s) := rfl

/-- Binder atoms preserved verbatim by the HE↔PeTTa translators.
    This matches the upstream HE typing of `chain` / `atom-subst`, whose
    second argument is a `Variable`, with `_` also allowed by the scope contract. -/
def isHEBinderAtom : Atom → Bool
  | .var _ => true
  | .symbol "_" => true
  | _ => false

set_option maxHeartbeats 800000

mutual
/-- A recursive common fragment that neither translator rewrites.
    Positive example: shared `let`/`match` terms whose subterms are also stable.
    Negative example: any nested `chain`, `progn`, or `@<` headed expression. -/
def isStableCommonForm : Atom → Bool
  | .expression (.symbol "chain" :: _) => false
  | .expression (.symbol "collapse-bind" :: _) => false
  | .expression (.symbol "superpose-bind" :: _) => false
  | .expression (.symbol "switch" :: _) => false
  | .expression (.symbol "switch-minimal" :: _) => false
  | .expression (.symbol "atom-subst" :: _) => false
  | .expression (.symbol "nop" :: _) => false
  | .expression (.symbol "function" :: _) => false
  | .expression (.symbol "progn" :: _) => false
  | .expression (.symbol "prog1" :: _) => false
  | .expression (.symbol "foldall" :: _) => false
  | .expression (.symbol "@<" :: _) => false
  | .expression (.symbol "@>" :: _) => false
  | .expression es => isStableCommonExpr es
  | _ => true

/-- Raw symbols that would trigger a rewrite when used as expression heads. -/
def isForbiddenHeadSymbol : Atom → Bool
  | .symbol "chain" => true
  | .symbol "collapse-bind" => true
  | .symbol "superpose-bind" => true
  | .symbol "switch" => true
  | .symbol "switch-minimal" => true
  | .symbol "atom-subst" => true
  | .symbol "nop" => true
  | .symbol "function" => true
  | .symbol "progn" => true
  | .symbol "prog1" => true
  | .symbol "foldall" => true
  | .symbol "@<" => true
  | .symbol "@>" => true
  | _ => false

/-- Stability required specifically in expression-head position. -/
def isStableCommonHead (a : Atom) : Bool :=
  !isForbiddenHeadSymbol a && isStableCommonForm a

/-- Stability of a translated expression node: the head is stricter than args. -/
def isStableCommonExpr : List Atom → Bool
  | [] => true
  | hd :: args => isStableCommonHead hd && isStableCommonList args

/-- List helper for ordinary subterms. -/
def isStableCommonList : List Atom → Bool
  | [] => true
  | x :: xs => isStableCommonForm x && isStableCommonList xs
end

mutual
/-- Executable validator for the HE source fragment on which the roundtrip
    fixed-point theorem is actually true.

    It enforces two semantic side conditions:
    1. HE binder slots contain only variables or `_`.
    2. PeTTa-only heads (`progn`, `prog1`, `@<`, `@>`) do not already appear in
       the source tree.

    Positive example: `(chain e $x body)` with recursively validated subterms.
    Negative example: a `chain` whose binder slot itself contains another
    expression. -/
def isValidatedHESource : Atom → Bool
  | .expression [.symbol "chain", e, v, body] =>
      isValidatedHESource e && isHEBinderAtom v && isValidatedHESource body
  | .expression [.symbol "collapse-bind", inner] =>
      isValidatedHESource inner
  | .expression [.symbol "superpose-bind", inner] =>
      isValidatedHESource inner
  | .expression (.symbol "switch" :: scrut :: branches) =>
      isValidatedHESource scrut && isValidatedHEList branches
  | .expression (.symbol "switch-minimal" :: scrut :: branches) =>
      isValidatedHESource scrut && isValidatedHEList branches
  | .expression [.symbol "atom-subst", atom, v, tmpl] =>
      isValidatedHESource atom && isHEBinderAtom v && isValidatedHESource tmpl
  | .expression [.symbol "nop", x] =>
      isValidatedHESource x
  | .expression [.symbol "function", .expression [.symbol "return", x]] =>
      isValidatedHESource x
  | .expression (.symbol "chain" :: _) => false
  | .expression (.symbol "collapse-bind" :: _) => false
  | .expression (.symbol "superpose-bind" :: _) => false
  | .expression (.symbol "switch" :: _) => false
  | .expression (.symbol "switch-minimal" :: _) => false
  | .expression (.symbol "atom-subst" :: _) => false
  | .expression (.symbol "nop" :: _) => false
  | .expression (.symbol "function" :: _) => false
  | .expression (.symbol "progn" :: _) => false
  | .expression (.symbol "prog1" :: _) => false
  | .expression (.symbol "foldall" :: _) => false
  | .expression (.symbol "@<" :: _) => false
  | .expression (.symbol "@>" :: _) => false
  | .expression [] => true
  | .expression (hd :: args) => isValidatedHEHeadSource hd && isValidatedHEList args
  | _ => true

/-- Validator for terms that are safe in operator position after `translateHE`. -/
def isValidatedHEHeadSource : Atom → Bool
  | .symbol "chain" => false
  | .symbol "collapse-bind" => false
  | .symbol "superpose-bind" => false
  | .symbol "switch" => false
  | .symbol "switch-minimal" => false
  | .symbol "atom-subst" => false
  | .symbol "nop" => false
  | .symbol "function" => false
  | .symbol "progn" => false
  | .symbol "prog1" => false
  | .symbol "foldall" => false
  | .symbol "@<" => false
  | .symbol "@>" => false
  | .expression [.symbol "function", .expression [.symbol "return", x]] =>
      isValidatedHEHeadSource x
  | a => isValidatedHESource a

/-- List helper for `isValidatedHESource`. -/
def isValidatedHEList : List Atom → Bool
  | [] => true
  | x :: xs => isValidatedHESource x && isValidatedHEList xs
end

example : isStableCommonForm (.expression [.symbol "let", .var "$x", .symbol "a", .symbol "b"]) = true := by
  native_decide

example : isStableCommonForm (.expression [.symbol "progn", .symbol "a", .symbol "b"]) = false := by
  native_decide

example : isStableCommonForm (.expression [.symbol "foldall",
    .symbol "merge", .symbol "goal", .symbol "0"]) = false := by
  native_decide

example : isValidatedHESource (.expression [.symbol "chain",
    .symbol "e", .var "$x", .symbol "b"]) = true := by
  native_decide

example : isValidatedHESource (.expression [.symbol "chain",
    .symbol "e",
    .expression [.symbol "chain", .symbol "x", .var "$y", .symbol "z"],
    .symbol "b"]) = false := by
  native_decide

example : isValidatedHESource (.expression
    [.expression [.symbol "function", .expression [.symbol "return", .symbol "chain"]],
     .symbol "arg"]) = false := by
  native_decide

/-- PeTTa `foldall` reducers that remain first-order callable after lowering to
    HE's ordinary application surface. -/
def isFirstOrderReducerAtom : Atom → Bool
  | .symbol name => !isForbiddenHeadSymbol (.symbol name)
  | _ => false

mutual
/-- Executable validator for the PeTTa source fragment on which the new
    `foldall` lowering stays inside the common stable form.

    The key extra side condition is that `foldall` reducers must be first-order
    symbols, so the lowered HE application `(Agg acc item)` stays symbol-headed.
-/
def isValidatedPeTTaSource : Atom → Bool
  | .expression (.symbol "progn" :: args) => isValidatedPeTTaList args
  | .expression (.symbol "prog1" :: args) => isValidatedPeTTaList args
  | .expression [.symbol "foldall", agg, goal, init] =>
      isFirstOrderReducerAtom agg && isValidatedPeTTaSource goal && isValidatedPeTTaSource init
  | .expression [.symbol "@<", a, b] =>
      isValidatedPeTTaSource a && isValidatedPeTTaSource b
  | .expression [.symbol "@>", a, b] =>
      isValidatedPeTTaSource a && isValidatedPeTTaSource b
  | .expression (.symbol "chain" :: _) => false
  | .expression (.symbol "collapse-bind" :: _) => false
  | .expression (.symbol "superpose-bind" :: _) => false
  | .expression (.symbol "switch" :: _) => false
  | .expression (.symbol "switch-minimal" :: _) => false
  | .expression (.symbol "atom-subst" :: _) => false
  | .expression (.symbol "nop" :: _) => false
  | .expression (.symbol "function" :: _) => false
  | .expression (.symbol "foldall" :: _) => false
  | .expression (.symbol "@<" :: _) => false
  | .expression (.symbol "@>" :: _) => false
  | .expression [] => true
  | .expression (hd :: args) => isValidatedPeTTaHeadSource hd && isValidatedPeTTaList args
  | _ => true

/-- `progn` in operator position returns its final argument, so every earlier
    term need only be source-valid while the final term must itself be head-safe. -/
def isValidatedPeTTaPrognHeadArgs : List Atom → Bool
  | [] => true
  | [last] => isValidatedPeTTaHeadSource last
  | x :: xs => isValidatedPeTTaSource x && isValidatedPeTTaPrognHeadArgs xs

/-- `prog1` in operator position returns its first argument, so only that first
    term must be head-safe; the rest are evaluated for side effects. -/
def isValidatedPeTTaProg1HeadArgs : List Atom → Bool
  | [] => true
  | [first] => isValidatedPeTTaHeadSource first
  | first :: rest => isValidatedPeTTaHeadSource first && isValidatedPeTTaList rest

/-- Validator for terms that are safe in operator position after `translatePeTTa`. -/
def isValidatedPeTTaHeadSource : Atom → Bool
  | .symbol "chain" => false
  | .symbol "collapse-bind" => false
  | .symbol "superpose-bind" => false
  | .symbol "switch" => false
  | .symbol "switch-minimal" => false
  | .symbol "atom-subst" => false
  | .symbol "nop" => false
  | .symbol "function" => false
  | .symbol "progn" => false
  | .symbol "prog1" => false
  | .symbol "foldall" => false
  | .symbol "@<" => false
  | .symbol "@>" => false
  | .expression (.symbol "progn" :: args) => isValidatedPeTTaPrognHeadArgs args
  | .expression (.symbol "prog1" :: args) => isValidatedPeTTaProg1HeadArgs args
  | .expression [.symbol "foldall", agg, goal, init] =>
      isFirstOrderReducerAtom agg && isValidatedPeTTaSource goal && isValidatedPeTTaSource init
  | .expression [.symbol "@<", a, b] =>
      isValidatedPeTTaSource a && isValidatedPeTTaSource b
  | .expression [.symbol "@>", a, b] =>
      isValidatedPeTTaSource a && isValidatedPeTTaSource b
  | a => isValidatedPeTTaSource a

/-- List helper for `isValidatedPeTTaSource`. -/
def isValidatedPeTTaList : List Atom → Bool
  | [] => true
  | x :: xs => isValidatedPeTTaSource x && isValidatedPeTTaList xs
end

example : isValidatedPeTTaSource (.expression
    [.symbol "foldall", .symbol "merge", .expression [.symbol "twohop-item"], .symbol "0"]) = true := by
  native_decide

example : isValidatedPeTTaSource (.expression
    [.symbol "foldall", .var "$f", .expression [.symbol "twohop-item"], .symbol "0"]) = false := by
  native_decide

example : isValidatedPeTTaSource (.expression
    [.symbol "foldall", .symbol "@<", .expression [.symbol "twohop-item"], .symbol "0"]) = false := by
  native_decide

example : isValidatedPeTTaSource (.expression
    [.symbol "prog1", .expression [.symbol "foldall", .symbol "merge",
      .expression [.symbol "twohop-item"], .symbol "0"], .symbol "done"]) = true := by
  native_decide

example : isValidatedPeTTaSource (.expression
    [.expression [.symbol "prog1", .symbol "chain"], .symbol "arg"]) = false := by
  native_decide

example : isValidatedPeTTaSource (.expression
    [.expression [.symbol "progn", .symbol "side", .symbol "prog1"], .symbol "arg"]) = false := by
  native_decide

private theorem firstOrderReducerAtom_eq_symbol (a : Atom)
    (h : isFirstOrderReducerAtom a = true) :
    ∃ name, a = .symbol name := by
  cases a with
  | var _ => cases h
  | symbol name => exact ⟨name, rfl⟩
  | grounded _ => cases h
  | expression _ => cases h

private theorem stableCommon_of_firstOrderReducerAtom (a : Atom)
    (h : isFirstOrderReducerAtom a = true) :
    isStableCommonForm a = true := by
  obtain ⟨name, rfl⟩ := firstOrderReducerAtom_eq_symbol a h
  simp [isFirstOrderReducerAtom, isStableCommonForm, isForbiddenHeadSymbol] at h ⊢

private theorem stableCommon_of_heBinderAtom (v : Atom)
    (h : isHEBinderAtom v = true) :
    isStableCommonForm v = true := by
  cases v with
  | var _ => simp [isStableCommonForm]
  | symbol _ => simp [isStableCommonForm]
  | grounded _ => cases h
  | expression _ => cases h

private theorem stableCommonHead_of_stableCommonForm (a : Atom)
    (h : isStableCommonForm a = true)
    (hnot : isForbiddenHeadSymbol a = false) :
    isStableCommonHead a = true := by
  simp [isStableCommonHead, h, hnot]

private theorem stableCommonForm_cons_of_head (hd : Atom) (args : List Atom)
    (hhd : isStableCommonHead hd = true) :
    isStableCommonForm (.expression (hd :: args)) = isStableCommonList args := by
  cases hd with
  | var _ =>
      simp [isStableCommonForm, isStableCommonExpr, isStableCommonHead, isForbiddenHeadSymbol]
  | symbol c =>
      by_cases hchain : c = "chain"
      · subst hchain
        have hfalse : False := by
          simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
        exact False.elim hfalse
      · by_cases hcollapse : c = "collapse-bind"
        · subst hcollapse
          have hfalse : False := by
            simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
          exact False.elim hfalse
        · by_cases hsuperpose : c = "superpose-bind"
          · subst hsuperpose
            have hfalse : False := by
              simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
            exact False.elim hfalse
          · by_cases hswitch : c = "switch"
            · subst hswitch
              have hfalse : False := by
                simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
              exact False.elim hfalse
            · by_cases hswitchm : c = "switch-minimal"
              · subst hswitchm
                have hfalse : False := by
                  simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                exact False.elim hfalse
              · by_cases hatomsubst : c = "atom-subst"
                · subst hatomsubst
                  have hfalse : False := by
                    simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                  exact False.elim hfalse
                · by_cases hnop : c = "nop"
                  · subst hnop
                    have hfalse : False := by
                      simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                    exact False.elim hfalse
                  · by_cases hfunction : c = "function"
                    · subst hfunction
                      have hfalse : False := by
                        simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                      exact False.elim hfalse
                    · by_cases hprogn : c = "progn"
                      · subst hprogn
                        have hfalse : False := by
                          simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                        exact False.elim hfalse
                      · by_cases hprog1 : c = "prog1"
                        · subst hprog1
                          have hfalse : False := by
                            simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                          exact False.elim hfalse
                        · by_cases hfoldall : c = "foldall"
                          · subst hfoldall
                            have hfalse : False := by
                              simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                            exact False.elim hfalse
                          · by_cases hlt : c = "@<"
                            · subst hlt
                              have hfalse : False := by
                                simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                              exact False.elim hfalse
                            · by_cases hgt : c = "@>"
                              · subst hgt
                                have hfalse : False := by
                                  simpa [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol] using hhd
                                exact False.elim hfalse
                              · simp [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                                  isForbiddenHeadSymbol, isStableCommonList, hchain, hcollapse,
                                  hsuperpose, hswitch, hswitchm, hatomsubst, hnop, hfunction,
                                  hprogn, hprog1, hfoldall, hlt, hgt]
  | grounded _ =>
      simp [isStableCommonForm, isStableCommonExpr, isStableCommonHead, isForbiddenHeadSymbol]
  | expression es =>
      have hform : isStableCommonForm (.expression es) = true := by
        simpa [isStableCommonHead, isForbiddenHeadSymbol] using hhd
      simp [isStableCommonForm, isStableCommonExpr, isStableCommonHead, isForbiddenHeadSymbol, hform]

mutual

private theorem validatedPeTTaSource_of_headSource_aux
    (a : Atom) (h : isValidatedPeTTaHeadSource a = true) :
    isValidatedPeTTaSource a = true := by
  cases a with
  | var _ => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource]
  | symbol c =>
      by_cases hchain : c = "chain"
      · subst hchain
        simp [isValidatedPeTTaHeadSource] at h
      · by_cases hcollapse : c = "collapse-bind"
        · subst hcollapse
          simp [isValidatedPeTTaHeadSource] at h
        · by_cases hsuperpose : c = "superpose-bind"
          · subst hsuperpose
            simp [isValidatedPeTTaHeadSource] at h
          · by_cases hswitch : c = "switch"
            · subst hswitch
              simp [isValidatedPeTTaHeadSource] at h
            · by_cases hswitchm : c = "switch-minimal"
              · subst hswitchm
                simp [isValidatedPeTTaHeadSource] at h
              · by_cases hatomsubst : c = "atom-subst"
                · subst hatomsubst
                  simp [isValidatedPeTTaHeadSource] at h
                · by_cases hnop : c = "nop"
                  · subst hnop
                    simp [isValidatedPeTTaHeadSource] at h
                  · by_cases hfunction : c = "function"
                    · subst hfunction
                      simp [isValidatedPeTTaHeadSource] at h
                    · by_cases hprogn : c = "progn"
                      · subst hprogn
                        simp [isValidatedPeTTaHeadSource] at h
                      · by_cases hprog1 : c = "prog1"
                        · subst hprog1
                          simp [isValidatedPeTTaHeadSource] at h
                        · by_cases hfoldall : c = "foldall"
                          · subst hfoldall
                            simp [isValidatedPeTTaHeadSource] at h
                          · by_cases hlt : c = "@<"
                            · subst hlt
                              simp [isValidatedPeTTaHeadSource] at h
                            · by_cases hgt : c = "@>"
                              · subst hgt
                                simp [isValidatedPeTTaHeadSource] at h
                              · simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                  hchain, hcollapse, hsuperpose, hswitch, hswitchm,
                                  hatomsubst, hnop, hfunction, hprogn, hprog1,
                                  hfoldall, hlt, hgt] at h ⊢
  | grounded _ => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource]
  | expression es =>
      cases es with
      | nil => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource]
      | cons hd args =>
          cases hd with
          | symbol c =>
              by_cases hprogn : c = "progn"
              · subst hprogn
                have hargs : isValidatedPeTTaPrognHeadArgs args = true := by
                  simpa [isValidatedPeTTaHeadSource] using h
                simpa [isValidatedPeTTaSource] using
                  validatedPeTTaList_of_prognHeadArgs_aux args hargs
              · by_cases hprog1 : c = "prog1"
                · subst hprog1
                  have hargs : isValidatedPeTTaProg1HeadArgs args = true := by
                    simpa [isValidatedPeTTaHeadSource, hprogn] using h
                  simpa [isValidatedPeTTaSource] using
                    validatedPeTTaList_of_prog1HeadArgs_aux args hargs
                · by_cases hfoldall : c = "foldall"
                  · subst hfoldall
                    cases args with
                    | nil =>
                        simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource, hprogn, hprog1] at h
                    | cons agg rest =>
                        cases rest with
                        | nil =>
                            simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource, hprogn, hprog1] at h
                        | cons goal rest =>
                            cases rest with
                            | nil =>
                                simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource, hprogn, hprog1] at h
                            | cons init rest =>
                                cases rest with
                                | nil =>
                                    simpa [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                      hprogn, hprog1]
                                      using h
                                | cons _ _ =>
                                    simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                      hprogn, hprog1] at h
                  · by_cases hlt : c = "@<"
                    · subst hlt
                      cases args with
                      | nil =>
                          simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                            hprogn, hprog1, hfoldall] at h
                      | cons a rest =>
                          cases rest with
                          | nil =>
                              simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                hprogn, hprog1, hfoldall] at h
                          | cons b rest =>
                              cases rest with
                              | nil =>
                                  simpa [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                    hprogn, hprog1, hfoldall] using h
                              | cons _ _ =>
                                  simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                    hprogn, hprog1, hfoldall] at h
                    · by_cases hgt : c = "@>"
                      · subst hgt
                        cases args with
                        | nil =>
                            simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                              hprogn, hprog1, hfoldall, hlt] at h
                        | cons a rest =>
                            cases rest with
                            | nil =>
                                simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                  hprogn, hprog1, hfoldall, hlt] at h
                            | cons b rest =>
                                cases rest with
                                | nil =>
                                    simpa [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                      hprogn, hprog1, hfoldall, hlt] using h
                                | cons _ _ =>
                                    simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                                      hprogn, hprog1, hfoldall, hlt] at h
                      · simpa [isValidatedPeTTaHeadSource, isValidatedPeTTaSource,
                          hprogn, hprog1, hfoldall, hlt, hgt] using h
          | var _ => simpa [isValidatedPeTTaHeadSource] using h
          | grounded _ => simpa [isValidatedPeTTaHeadSource] using h
          | expression _ => simpa [isValidatedPeTTaHeadSource] using h

private theorem validatedPeTTaList_of_prognHeadArgs_aux
    (args : List Atom) (h : isValidatedPeTTaPrognHeadArgs args = true) :
    isValidatedPeTTaList args = true := by
  cases args with
  | nil => simp [isValidatedPeTTaPrognHeadArgs, isValidatedPeTTaList]
  | cons x xs =>
      cases xs with
      | nil =>
          have hx : isValidatedPeTTaSource x = true := by
            exact validatedPeTTaSource_of_headSource_aux x (by simpa [isValidatedPeTTaPrognHeadArgs] using h)
          simp [isValidatedPeTTaList, hx]
      | cons y ys =>
          simp [isValidatedPeTTaPrognHeadArgs, Bool.and_eq_true] at h
          have htail : isValidatedPeTTaList (y :: ys) = true :=
            validatedPeTTaList_of_prognHeadArgs_aux (y :: ys) h.2
          simpa [isValidatedPeTTaList, h.1] using htail

private theorem validatedPeTTaList_of_prog1HeadArgs_aux
    (args : List Atom) (h : isValidatedPeTTaProg1HeadArgs args = true) :
    isValidatedPeTTaList args = true := by
  cases args with
  | nil => simp [isValidatedPeTTaProg1HeadArgs, isValidatedPeTTaList]
  | cons x xs =>
      cases xs with
      | nil =>
          have hx : isValidatedPeTTaSource x = true := by
            exact validatedPeTTaSource_of_headSource_aux x (by simpa [isValidatedPeTTaProg1HeadArgs] using h)
          simp [isValidatedPeTTaList, hx]
      | cons y ys =>
          simp [isValidatedPeTTaProg1HeadArgs, isValidatedPeTTaList, Bool.and_eq_true] at h ⊢
          have hx : isValidatedPeTTaSource x = true :=
            validatedPeTTaSource_of_headSource_aux x h.1
          exact ⟨hx, h.2⟩
end

private theorem headSourcePeTTaSymbol_notForbidden_aux
    (c : String) (h : isValidatedPeTTaHeadSource (.symbol c) = true) :
    isForbiddenHeadSymbol (.symbol c) = false := by
  by_cases hchain : c = "chain"
  · subst hchain
    simp [isValidatedPeTTaHeadSource] at h
  · by_cases hcollapse : c = "collapse-bind"
    · subst hcollapse
      simp [isValidatedPeTTaHeadSource] at h
    · by_cases hsuperpose : c = "superpose-bind"
      · subst hsuperpose
        simp [isValidatedPeTTaHeadSource] at h
      · by_cases hswitch : c = "switch"
        · subst hswitch
          simp [isValidatedPeTTaHeadSource] at h
        · by_cases hswitchm : c = "switch-minimal"
          · subst hswitchm
            simp [isValidatedPeTTaHeadSource] at h
          · by_cases hatomsubst : c = "atom-subst"
            · subst hatomsubst
              simp [isValidatedPeTTaHeadSource] at h
            · by_cases hnop : c = "nop"
              · subst hnop
                simp [isValidatedPeTTaHeadSource] at h
              · by_cases hfunction : c = "function"
                · subst hfunction
                  simp [isValidatedPeTTaHeadSource] at h
                · by_cases hprogn : c = "progn"
                  · subst hprogn
                    simp [isValidatedPeTTaHeadSource] at h
                  · by_cases hprog1 : c = "prog1"
                    · subst hprog1
                      simp [isValidatedPeTTaHeadSource] at h
                    · by_cases hfoldall : c = "foldall"
                      · subst hfoldall
                        simp [isValidatedPeTTaHeadSource] at h
                      · by_cases hlt : c = "@<"
                        · subst hlt
                          simp [isValidatedPeTTaHeadSource] at h
                        · by_cases hgt : c = "@>"
                          · subst hgt
                            simp [isValidatedPeTTaHeadSource] at h
                          · simp [isForbiddenHeadSymbol, hchain, hcollapse, hsuperpose,
                              hswitch, hswitchm, hatomsubst, hnop, hfunction, hprogn,
                              hprog1, hfoldall, hlt, hgt]

mutual

private theorem translateHE_preserves_stableCommonForm_aux
    (a : Atom) (s : Nat) (h : isValidatedHESource a = true) :
    isStableCommonForm (translateHE a s).1 = true := by
  cases a with
  | var _ => simp [translateHE, isStableCommonForm]
  | symbol _ => simp [translateHE, isStableCommonForm]
  | grounded _ => simp [translateHE, isStableCommonForm]
  | expression es =>
    cases es with
    | nil => simp [translateHE, translateHE.translateHEList, isStableCommonForm, isStableCommonExpr]
    | cons hd args =>
      cases hd with
      | symbol c =>
        by_cases hchain : c = "chain"
        · subst hchain
          cases args with
          | nil => simp [isValidatedHESource] at h
          | cons e rest =>
            cases rest with
            | nil => simp [isValidatedHESource] at h
            | cons v rest =>
              cases rest with
              | nil => simp [isValidatedHESource] at h
              | cons body rest =>
                cases rest with
                | nil =>
                  simp [isValidatedHESource, Bool.and_eq_true] at h
                  have he := translateHE_preserves_stableCommonForm_aux e s h.1.1
                  have hv := stableCommon_of_heBinderAtom v h.1.2
                  have hbody :=
                    translateHE_preserves_stableCommonForm_aux body (translateHE e s).2 h.2
                  simp [translateHE, isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                    isForbiddenHeadSymbol, isStableCommonList, he, hv, hbody]
                | cons _ _ => simp [isValidatedHESource] at h
        · by_cases hcollapse : c = "collapse-bind"
          · subst hcollapse
            cases args with
            | nil => simp [isValidatedHESource] at h
            | cons inner rest =>
              cases rest with
              | nil =>
                have hinner :=
                  translateHE_preserves_stableCommonForm_aux inner s
                    (by simpa [isValidatedHESource] using h)
                simp [translateHE, isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                  isForbiddenHeadSymbol, isStableCommonList, hinner]
              | cons _ _ => simp [isValidatedHESource] at h
          · by_cases hsuperpose : c = "superpose-bind"
            · subst hsuperpose
              cases args with
              | nil => simp [isValidatedHESource] at h
              | cons inner rest =>
                cases rest with
                | nil =>
                  have hinner :=
                    translateHE_preserves_stableCommonForm_aux inner s
                      (by simpa [isValidatedHESource] using h)
                  simp [translateHE, isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                    isForbiddenHeadSymbol, isStableCommonList, hinner]
                | cons _ _ => simp [isValidatedHESource] at h
            · by_cases hswitch : c = "switch"
              · subst hswitch
                cases args with
                | nil => simp [isValidatedHESource] at h
                | cons scrut branches =>
                  simp [isValidatedHESource, Bool.and_eq_true] at h
                  have hscrut := translateHE_preserves_stableCommonForm_aux scrut s h.1
                  have hbranches :=
                    translateHEList_preserves_stableCommonList_aux branches (translateHE scrut s).2 h.2
                  simp [translateHE, isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                    isForbiddenHeadSymbol, isStableCommonList, hscrut, hbranches]
              · by_cases hswitchm : c = "switch-minimal"
                · subst hswitchm
                  cases args with
                  | nil => simp [isValidatedHESource] at h
                  | cons scrut branches =>
                    simp [isValidatedHESource, Bool.and_eq_true] at h
                    have hscrut := translateHE_preserves_stableCommonForm_aux scrut s h.1
                    have hbranches :=
                      translateHEList_preserves_stableCommonList_aux branches (translateHE scrut s).2 h.2
                    simp [translateHE, isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                      isForbiddenHeadSymbol, isStableCommonList, hscrut, hbranches]
                · by_cases hatomsubst : c = "atom-subst"
                  · subst hatomsubst
                    cases args with
                    | nil => simp [isValidatedHESource] at h
                    | cons atom rest =>
                      cases rest with
                      | nil => simp [isValidatedHESource] at h
                      | cons v rest =>
                        cases rest with
                        | nil => simp [isValidatedHESource] at h
                        | cons tmpl rest =>
                          cases rest with
                          | nil =>
                            simp [isValidatedHESource, Bool.and_eq_true] at h
                            have hatom :=
                              translateHE_preserves_stableCommonForm_aux atom s h.1.1
                            have hv := stableCommon_of_heBinderAtom v h.1.2
                            have htmpl :=
                              translateHE_preserves_stableCommonForm_aux tmpl (translateHE atom s).2 h.2
                            simp [translateHE, isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                              isForbiddenHeadSymbol, isStableCommonList, hatom, hv, htmpl]
                          | cons _ _ => simp [isValidatedHESource] at h
                  · by_cases hnop : c = "nop"
                    · subst hnop
                      cases args with
                      | nil => simp [isValidatedHESource] at h
                      | cons x rest =>
                        cases rest with
                        | nil =>
                          have hx :=
                            translateHE_preserves_stableCommonForm_aux x (freshVar "discard" s).2
                              (by simpa [isValidatedHESource] using h)
                          have hx' : isStableCommonForm (translateHE x (s + 1)).1 = true := by
                            simpa [freshVar] using hx
                          simp [translateHE, freshVar, isStableCommonForm, isStableCommonExpr,
                            isStableCommonHead, isForbiddenHeadSymbol, isStableCommonList, hx']
                        | cons _ _ => simp [isValidatedHESource] at h
                    · by_cases hfunction : c = "function"
                      · subst hfunction
                        cases args with
                        | nil => simp [isValidatedHESource] at h
                        | cons x rest =>
                          cases rest with
                          | nil =>
                            cases x with
                            | expression es' =>
                              cases es' with
                              | nil => simp [isValidatedHESource] at h
                              | cons hd' tail' =>
                                cases hd' with
                                | symbol c' =>
                                  by_cases hreturn : c' = "return"
                                  · subst hreturn
                                    cases tail' with
                                    | nil => simp [isValidatedHESource] at h
                                    | cons inner rest' =>
                                      cases rest' with
                                      | nil =>
                                        simpa [translateHE, isValidatedHESource] using
                                          translateHE_preserves_stableCommonForm_aux inner s
                                            (by simpa [isValidatedHESource] using h)
                                      | cons _ _ => simp [isValidatedHESource] at h
                                  · simp [isValidatedHESource, hreturn] at h
                                | var _ => simp [isValidatedHESource] at h
                                | grounded _ => simp [isValidatedHESource] at h
                                | expression _ => simp [isValidatedHESource] at h
                            | var _ => simp [isValidatedHESource] at h
                            | symbol _ => simp [isValidatedHESource] at h
                            | grounded _ => simp [isValidatedHESource] at h
                          | cons _ _ => simp [isValidatedHESource] at h
                      · by_cases hfoldall : c = "foldall"
                        · subst hfoldall
                          simp [isValidatedHESource] at h
                        · by_cases hprogn : c = "progn"
                          · subst hprogn
                            have hfalse : False := by
                              simpa [isValidatedHESource] using h
                            exact False.elim hfalse
                          · by_cases hprog1 : c = "prog1"
                            · subst hprog1
                              have hfalse : False := by
                                simpa [isValidatedHESource] using h
                              exact False.elim hfalse
                            · by_cases hlt : c = "@<"
                              · subst hlt
                                have hfalse : False := by
                                  simpa [isValidatedHESource] using h
                                exact False.elim hfalse
                              · by_cases hgt : c = "@>"
                                · subst hgt
                                  have hfalse : False := by
                                    simpa [isValidatedHESource] using h
                                  exact False.elim hfalse
                                · have hpair :
                                      isValidatedHEHeadSource (.symbol c) = true ∧
                                        isValidatedHEList args = true := by
                                    simpa [isValidatedHESource, isValidatedHEHeadSource,
                                      Bool.and_eq_true, hchain, hcollapse, hsuperpose, hswitch,
                                      hswitchm, hatomsubst, hnop, hfunction, hfoldall, hprogn,
                                      hprog1, hlt, hgt] using h
                                  have hargs : isValidatedHEList args = true := hpair.2
                                  have htail :
                                      isStableCommonList (translateHE.translateHEList args s).1 = true :=
                                    translateHEList_preserves_stableCommonList_aux args s hargs
                                  have hhead : isStableCommonHead (.symbol c) = true := by
                                    simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol,
                                      hchain, hcollapse, hsuperpose, hswitch, hswitchm, hatomsubst,
                                      hnop, hfunction, hprogn, hprog1, hfoldall, hlt, hgt]
                                  have hcons :=
                                    stableCommonForm_cons_of_head (.symbol c)
                                      (translateHE.translateHEList args s).1 hhead
                                  have hbody :
                                      isStableCommonForm
                                        (Atom.expression
                                          (.symbol c :: (translateHE.translateHEList args s).1)) = true := by
                                    rw [hcons]
                                    exact htail
                                  simpa [translateHE, translateHE.translateHEList, hchain,
                                    hcollapse, hsuperpose, hswitch, hswitchm, hatomsubst, hnop,
                                    hfunction, hfoldall, hprogn, hprog1, hlt, hgt] using hbody
      | var v =>
        have hargs : isValidatedHEList args = true := by
          simpa [isValidatedHESource, isValidatedHEHeadSource] using h
        have htail := translateHEList_preserves_stableCommonList_aux args s hargs
        simpa [translateHE, translateHE.translateHEList, isStableCommonForm, isStableCommonExpr,
          isStableCommonHead, isForbiddenHeadSymbol, isStableCommonList, htail]
      | grounded g =>
        have hargs : isValidatedHEList args = true := by
          simpa [isValidatedHESource, isValidatedHEHeadSource] using h
        have htail := translateHEList_preserves_stableCommonList_aux args s hargs
        simpa [translateHE, translateHE.translateHEList, isStableCommonForm, isStableCommonExpr,
          isStableCommonHead, isForbiddenHeadSymbol, isStableCommonList, htail]
      | expression es' =>
        have hparts :
            isValidatedHEHeadSource (.expression es') = true ∧ isValidatedHEList args = true := by
          simpa [isValidatedHESource] using h
        have hhead :=
          translateHE_preserves_stableCommonHead_aux (.expression es') s hparts.1
        have htail :=
          translateHEList_preserves_stableCommonList_aux args (translateHE (.expression es') s).2 hparts.2
        have hcons :=
          stableCommonForm_cons_of_head (translateHE (.expression es') s).1
            (translateHE.translateHEList args (translateHE (.expression es') s).2).1 hhead
        have hbody :
            isStableCommonForm
              (Atom.expression
                ((translateHE (.expression es') s).1 ::
                  (translateHE.translateHEList args (translateHE (.expression es') s).2).1)) = true := by
          rw [hcons]
          exact htail
        simpa [translateHE, translateHE.translateHEList] using hbody

private theorem validatedHESource_of_headSource_aux
    (a : Atom) (h : isValidatedHEHeadSource a = true) :
    isValidatedHESource a = true := by
  cases a with
  | var _ => simp [isValidatedHEHeadSource, isValidatedHESource]
  | symbol _ => simp [isValidatedHESource]
  | grounded _ => simp [isValidatedHEHeadSource, isValidatedHESource]
  | expression es =>
      cases es with
      | nil => simp [isValidatedHEHeadSource, isValidatedHESource]
      | cons hd args =>
          cases hd with
          | symbol c =>
              by_cases hfunction : c = "function"
              · subst hfunction
                cases args with
                | nil => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                | cons ret rest =>
                    cases rest with
                    | nil =>
                        cases ret with
                        | expression esx =>
                            cases esx with
                            | nil => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                            | cons hdx tailx =>
                                cases hdx with
                                | symbol c' =>
                                    by_cases hreturn : c' = "return"
                                    · subst hreturn
                                      cases tailx with
                                      | nil => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                                      | cons inner restx =>
                                          cases restx with
                                          | nil =>
                                              have hinner : isValidatedHEHeadSource inner = true := by
                                                simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                                              simpa [isValidatedHESource] using
                                                validatedHESource_of_headSource_aux inner hinner
                                          | cons _ _ => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                                    · simp [isValidatedHEHeadSource, isValidatedHESource, hreturn] at h
                                | var _ => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                                | grounded _ => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                                | expression _ => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                        | var _ => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                        | symbol _ => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                        | grounded _ => simp [isValidatedHEHeadSource, isValidatedHESource] at h
                    | cons _ _ => simp [isValidatedHEHeadSource, isValidatedHESource] at h
              · simpa [isValidatedHEHeadSource, hfunction] using h
          | var _ => simpa [isValidatedHEHeadSource] using h
          | grounded _ => simpa [isValidatedHEHeadSource] using h
          | expression _ => simpa [isValidatedHEHeadSource] using h

private theorem headSourceSymbol_notForbidden_aux
    (c : String) (h : isValidatedHEHeadSource (.symbol c) = true) :
    isForbiddenHeadSymbol (.symbol c) = false := by
  by_cases hchain : c = "chain"
  · subst hchain
    have hfalse : False := by
      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
    exact False.elim hfalse
  · by_cases hcollapse : c = "collapse-bind"
    · subst hcollapse
      have hfalse : False := by
        simpa [isValidatedHEHeadSource, isValidatedHESource] using h
      exact False.elim hfalse
    · by_cases hsuperpose : c = "superpose-bind"
      · subst hsuperpose
        have hfalse : False := by
          simpa [isValidatedHEHeadSource, isValidatedHESource] using h
        exact False.elim hfalse
      · by_cases hswitch : c = "switch"
        · subst hswitch
          have hfalse : False := by
            simpa [isValidatedHEHeadSource, isValidatedHESource] using h
          exact False.elim hfalse
        · by_cases hswitchm : c = "switch-minimal"
          · subst hswitchm
            have hfalse : False := by
              simpa [isValidatedHEHeadSource, isValidatedHESource] using h
            exact False.elim hfalse
          · by_cases hatomsubst : c = "atom-subst"
            · subst hatomsubst
              have hfalse : False := by
                simpa [isValidatedHEHeadSource, isValidatedHESource] using h
              exact False.elim hfalse
            · by_cases hnop : c = "nop"
              · subst hnop
                have hfalse : False := by
                  simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                exact False.elim hfalse
              · by_cases hfunction : c = "function"
                · subst hfunction
                  have hfalse : False := by
                    simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                  exact False.elim hfalse
                · by_cases hprogn : c = "progn"
                  · subst hprogn
                    have hfalse : False := by
                      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                    exact False.elim hfalse
                  · by_cases hprog1 : c = "prog1"
                    · subst hprog1
                      have hfalse : False := by
                        simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                      exact False.elim hfalse
                    · by_cases hfoldall : c = "foldall"
                      · subst hfoldall
                        have hfalse : False := by
                          simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                        exact False.elim hfalse
                      · by_cases hlt : c = "@<"
                        · subst hlt
                          have hfalse : False := by
                            simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                          exact False.elim hfalse
                        · by_cases hgt : c = "@>"
                          · subst hgt
                            have hfalse : False := by
                              simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                            exact False.elim hfalse
                          · simp [isForbiddenHeadSymbol, hchain, hcollapse, hsuperpose, hswitch,
                              hswitchm, hatomsubst, hnop, hfunction, hprogn, hprog1, hfoldall,
                              hlt, hgt]

private theorem translateHE_notForbidden_of_headSymbolExpr_aux
    (c : String) (args : List Atom) (s : Nat)
    (h : isValidatedHEHeadSource (.expression (.symbol c :: args)) = true) :
    isForbiddenHeadSymbol (translateHE (.expression (.symbol c :: args)) s).1 = false := by
  by_cases hchain : c = "chain"
  · subst hchain
    cases args with
    | nil =>
        have hfalse : False := by
          simpa [isValidatedHEHeadSource, isValidatedHESource] using h
        exact False.elim hfalse
    | cons e rest =>
        cases rest with
        | nil =>
            have hfalse : False := by
              simpa [isValidatedHEHeadSource, isValidatedHESource] using h
            exact False.elim hfalse
        | cons v rest =>
            cases rest with
            | nil =>
                have hfalse : False := by
                  simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                exact False.elim hfalse
            | cons body rest =>
                cases rest with
                | nil => simp [translateHE, isForbiddenHeadSymbol]
                | cons _ _ =>
                    have hfalse : False := by
                      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                    exact False.elim hfalse
  · by_cases hcollapse : c = "collapse-bind"
    · subst hcollapse
      cases args with
      | nil =>
          have hfalse : False := by
            simpa [isValidatedHEHeadSource, isValidatedHESource] using h
          exact False.elim hfalse
      | cons inner rest =>
          cases rest with
          | nil => simp [translateHE, isForbiddenHeadSymbol]
          | cons _ _ =>
              have hfalse : False := by
                simpa [isValidatedHEHeadSource, isValidatedHESource] using h
              exact False.elim hfalse
    · by_cases hsuperpose : c = "superpose-bind"
      · subst hsuperpose
        cases args with
        | nil =>
            have hfalse : False := by
              simpa [isValidatedHEHeadSource, isValidatedHESource] using h
            exact False.elim hfalse
        | cons inner rest =>
            cases rest with
            | nil => simp [translateHE, isForbiddenHeadSymbol]
            | cons _ _ =>
                have hfalse : False := by
                  simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                exact False.elim hfalse
      · by_cases hswitch : c = "switch"
        · subst hswitch
          cases args with
          | nil =>
              have hfalse : False := by
                simpa [isValidatedHEHeadSource, isValidatedHESource] using h
              exact False.elim hfalse
          | cons scrut branches =>
              simp [translateHE, isForbiddenHeadSymbol]
        · by_cases hswitchm : c = "switch-minimal"
          · subst hswitchm
            cases args with
            | nil =>
                have hfalse : False := by
                  simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                exact False.elim hfalse
            | cons scrut branches =>
                simp [translateHE, isForbiddenHeadSymbol]
          · by_cases hatomsubst : c = "atom-subst"
            · subst hatomsubst
              cases args with
              | nil =>
                  have hfalse : False := by
                    simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                  exact False.elim hfalse
              | cons atom rest =>
                  cases rest with
                  | nil =>
                      have hfalse : False := by
                        simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                      exact False.elim hfalse
                  | cons v rest =>
                      cases rest with
                      | nil =>
                          have hfalse : False := by
                            simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                          exact False.elim hfalse
                      | cons tmpl rest =>
                          cases rest with
                          | nil => simp [translateHE, isForbiddenHeadSymbol]
                          | cons _ _ =>
                              have hfalse : False := by
                                simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                              exact False.elim hfalse
            · by_cases hnop : c = "nop"
              · subst hnop
                cases args with
                | nil =>
                    have hfalse : False := by
                      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                    exact False.elim hfalse
                | cons x rest =>
                    cases rest with
                    | nil => simp [translateHE, isForbiddenHeadSymbol]
                    | cons _ _ =>
                        have hfalse : False := by
                          simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                        exact False.elim hfalse
              · by_cases hfunction : c = "function"
                · subst hfunction
                  cases args with
                  | nil =>
                      have hfalse : False := by
                        simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                      exact False.elim hfalse
                  | cons ret rest =>
                      cases rest with
                      | nil =>
                          cases ret with
                          | expression esx =>
                              cases esx with
                              | nil =>
                                  have hfalse : False := by
                                    simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                                  exact False.elim hfalse
                              | cons hdx tailx =>
                                  cases hdx with
                                  | symbol c' =>
                                      by_cases hreturn : c' = "return"
                                      · subst hreturn
                                        cases tailx with
                                        | nil =>
                                            have hfalse : False := by
                                              simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                                            exact False.elim hfalse
                                        | cons inner restx =>
                                            cases restx with
                                            | nil =>
                                                have hinner : isValidatedHEHeadSource inner = true := by
                                                  simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                                                simpa [translateHE] using
                                                  translateHE_notForbidden_of_headSource_aux inner s hinner
                                            | cons _ _ =>
                                                have hfalse : False := by
                                                  simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                                                exact False.elim hfalse
                                      · have hfalse : False := by
                                          simpa [isValidatedHEHeadSource, isValidatedHESource, hreturn] using h
                                        exact False.elim hfalse
                                  | var _ =>
                                      have hfalse : False := by
                                        simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                                      exact False.elim hfalse
                                  | grounded _ =>
                                      have hfalse : False := by
                                        simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                                      exact False.elim hfalse
                                  | expression _ =>
                                      have hfalse : False := by
                                        simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                                      exact False.elim hfalse
                          | var _ =>
                              have hfalse : False := by
                                simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                              exact False.elim hfalse
                          | symbol _ =>
                              have hfalse : False := by
                                simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                              exact False.elim hfalse
                          | grounded _ =>
                              have hfalse : False := by
                                simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                              exact False.elim hfalse
                      | cons _ _ =>
                          have hfalse : False := by
                            simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                          exact False.elim hfalse
                · have hprogn : c ≠ "progn" := by
                    intro hc
                    subst hc
                    have hfalse : False := by
                      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                    exact hfalse
                  have hprog1 : c ≠ "prog1" := by
                    intro hc
                    subst hc
                    have hfalse : False := by
                      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                    exact hfalse
                  have hfoldall : c ≠ "foldall" := by
                    intro hc
                    subst hc
                    have hfalse : False := by
                      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                    exact hfalse
                  have hlt : c ≠ "@<" := by
                    intro hc
                    subst hc
                    have hfalse : False := by
                      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                    exact hfalse
                  have hgt : c ≠ "@>" := by
                    intro hc
                    subst hc
                    have hfalse : False := by
                      simpa [isValidatedHEHeadSource, isValidatedHESource] using h
                    exact hfalse
                  simp [translateHE, isForbiddenHeadSymbol, hchain, hcollapse, hsuperpose,
                    hswitch, hswitchm, hatomsubst, hnop, hfunction, hprogn, hprog1,
                    hfoldall, hlt, hgt]

private theorem translateHE_notForbidden_of_headSource_aux
    (a : Atom) (s : Nat) (h : isValidatedHEHeadSource a = true) :
    isForbiddenHeadSymbol (translateHE a s).1 = false := by
  cases a with
  | var _ => simp [translateHE, isForbiddenHeadSymbol]
  | symbol c => simpa [translateHE] using headSourceSymbol_notForbidden_aux c h
  | grounded _ => simp [translateHE, isForbiddenHeadSymbol]
  | expression es =>
      cases es with
      | nil => simp [translateHE, isForbiddenHeadSymbol]
      | cons hd args =>
          cases hd with
          | symbol c => simpa using translateHE_notForbidden_of_headSymbolExpr_aux c args s h
          | var _ => simp [translateHE, isForbiddenHeadSymbol]
          | grounded _ => simp [translateHE, isForbiddenHeadSymbol]
          | expression _ => simp [translateHE, isForbiddenHeadSymbol]

private theorem translateHE_preserves_stableCommonHead_aux
    (a : Atom) (s : Nat) (h : isValidatedHEHeadSource a = true) :
    isStableCommonHead (translateHE a s).1 = true := by
  have hsrc := validatedHESource_of_headSource_aux a h
  have hform := translateHE_preserves_stableCommonForm_aux a s hsrc
  have hnot := translateHE_notForbidden_of_headSource_aux a s h
  simp [isStableCommonHead, hform, hnot]

private theorem translateHEList_preserves_stableCommonList_aux
    (xs : List Atom) (s : Nat) (h : isValidatedHEList xs = true) :
    isStableCommonList (translateHE.translateHEList xs s).1 = true := by
  cases xs with
  | nil => simp [translateHE.translateHEList, isStableCommonList]
  | cons x xs =>
    simp [isValidatedHEList, Bool.and_eq_true] at h
    have hx : isStableCommonForm (translateHE x s).1 = true :=
      translateHE_preserves_stableCommonForm_aux x s h.1
    have hxs :
        isStableCommonList (translateHE.translateHEList xs (translateHE x s).2).1 = true :=
      translateHEList_preserves_stableCommonList_aux xs (translateHE x s).2 h.2
    simp [translateHE.translateHEList, isStableCommonList, hx, hxs]
end

set_option maxHeartbeats 200000

theorem translateHE_preserves_stableCommonForm (a : Atom) (s : Nat)
    (h : isValidatedHESource a = true) :
    isStableCommonForm (translateHE a s).1 = true :=
  translateHE_preserves_stableCommonForm_aux a s h

mutual

private theorem translateHE_id_of_stableCommonForm_aux
    (a : Atom) (s : Nat) (h : isStableCommonForm a = true) :
    translateHE a s = (a, s) := by
  cases a with
  | var _ => rfl
  | symbol _ => rfl
  | grounded _ => rfl
  | expression es =>
    cases es with
    | nil => rfl
    | cons hd args =>
      cases hd with
      | symbol c =>
        by_cases hchain : c = "chain"
        · subst hchain; simp [isStableCommonForm] at h
        · by_cases hcollapse : c = "collapse-bind"
          · subst hcollapse; simp [isStableCommonForm] at h
          · by_cases hsuperpose : c = "superpose-bind"
            · subst hsuperpose; simp [isStableCommonForm] at h
            · by_cases hswitch : c = "switch"
              · subst hswitch; simp [isStableCommonForm] at h
              · by_cases hswitchm : c = "switch-minimal"
                · subst hswitchm; simp [isStableCommonForm] at h
                · by_cases hatomsubst : c = "atom-subst"
                  · subst hatomsubst; simp [isStableCommonForm] at h
                  · by_cases hnop : c = "nop"
                    · subst hnop; simp [isStableCommonForm] at h
                    · by_cases hfunction : c = "function"
                      · subst hfunction; simp [isStableCommonForm] at h
                      · by_cases hfoldall : c = "foldall"
                        · subst hfoldall
                          simp [isStableCommonForm] at h
                        · have hargs : isStableCommonList args = true := by
                            have hprogn : c ≠ "progn" := by
                              intro hc
                              subst hc
                              simp [isStableCommonForm] at h
                            have hprog1 : c ≠ "prog1" := by
                              intro hc
                              subst hc
                              simp [isStableCommonForm] at h
                            have hlt : c ≠ "@<" := by
                              intro hc
                              subst hc
                              simp [isStableCommonForm] at h
                            have hgt : c ≠ "@>" := by
                              intro hc
                              subst hc
                              simp [isStableCommonForm] at h
                            have hparts :
                                isStableCommonHead (.symbol c) = true ∧
                                  isStableCommonList args = true := by
                              simpa [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                                isForbiddenHeadSymbol, hchain, hcollapse, hsuperpose, hswitch,
                                hswitchm, hatomsubst, hnop, hfunction, hfoldall, hprogn,
                                hprog1, hlt, hgt] using h
                            exact hparts.2
                          have htail := translateHEList_id_of_stableCommonList_aux args s hargs
                          have htail₁ : (translateHE.translateHEList args s).1 = args := by
                            exact congrArg Prod.fst htail
                          have htail₂ : (translateHE.translateHEList args s).2 = s := by
                            exact congrArg Prod.snd htail
                          simp [translateHE, translateHE.translateHEList, hchain, hcollapse,
                            hsuperpose, hswitch, hswitchm, hatomsubst, hnop, hfunction,
                            hfoldall, htail₁, htail₂]
      | var v =>
        have hargs : isStableCommonList args = true := by
          simpa [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
            isForbiddenHeadSymbol] using h
        have htail := translateHEList_id_of_stableCommonList_aux args s hargs
        simp [translateHE, translateHE.translateHEList, htail]
      | grounded g =>
        have hargs : isStableCommonList args = true := by
          simpa [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
            isForbiddenHeadSymbol] using h
        have htail := translateHEList_id_of_stableCommonList_aux args s hargs
        simp [translateHE, translateHE.translateHEList, htail]
      | expression es' =>
        have hparts : isStableCommonForm (.expression es') = true ∧ isStableCommonList args = true := by
          simpa [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
            isForbiddenHeadSymbol] using h
        have hhd := translateHE_id_of_stableCommonForm_aux (.expression es') s hparts.1
        have htail := translateHEList_id_of_stableCommonList_aux args s hparts.2
        simp [translateHE, translateHE.translateHEList, hhd, htail]

private theorem translateHEList_id_of_stableCommonList_aux
    (xs : List Atom) (s : Nat) (h : isStableCommonList xs = true) :
    translateHE.translateHEList xs s = (xs, s) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp [isStableCommonList, Bool.and_eq_true] at h
    have hx := translateHE_id_of_stableCommonForm_aux x s h.1
    have hxs := translateHEList_id_of_stableCommonList_aux xs s h.2
    simp [translateHE.translateHEList, hx, hxs]
end

/-- `translateHE` is identity on the stable common fragment. -/
theorem translateHE_id_of_stableCommonForm (a : Atom) (s : Nat)
    (h : isStableCommonForm a = true) :
    translateHE a s = (a, s) := by
  exact translateHE_id_of_stableCommonForm_aux a s h

mutual

private theorem translatePeTTa_id_of_stableCommonForm_aux
    (a : Atom) (s : Nat) (h : isStableCommonForm a = true) :
    translatePeTTa a s = (a, s) := by
  cases a with
  | var _ => rfl
  | symbol _ => rfl
  | grounded _ => rfl
  | expression es =>
    cases es with
    | nil => rfl
    | cons hd args =>
      cases hd with
      | symbol c =>
        by_cases hprogn : c = "progn"
        · subst hprogn; simp [isStableCommonForm] at h
        · by_cases hprog1 : c = "prog1"
          · subst hprog1; simp [isStableCommonForm] at h
          · by_cases hfoldall : c = "foldall"
            · subst hfoldall; simp [isStableCommonForm] at h
            · by_cases hlt : c = "@<"
              · subst hlt; simp [isStableCommonForm] at h
              · by_cases hgt : c = "@>"
                · subst hgt; simp [isStableCommonForm] at h
                · have hchain : c ≠ "chain" := by
                    intro hc
                    subst hc
                    simp [isStableCommonForm] at h
                  have hcollapse : c ≠ "collapse-bind" := by
                    intro hc
                    subst hc
                    simp [isStableCommonForm] at h
                  have hsuperpose : c ≠ "superpose-bind" := by
                    intro hc
                    subst hc
                    simp [isStableCommonForm] at h
                  have hswitch : c ≠ "switch" := by
                    intro hc
                    subst hc
                    simp [isStableCommonForm] at h
                  have hswitchm : c ≠ "switch-minimal" := by
                    intro hc
                    subst hc
                    simp [isStableCommonForm] at h
                  have hatomsubst : c ≠ "atom-subst" := by
                    intro hc
                    subst hc
                    simp [isStableCommonForm] at h
                  have hnop : c ≠ "nop" := by
                    intro hc
                    subst hc
                    simp [isStableCommonForm] at h
                  have hfunction : c ≠ "function" := by
                    intro hc
                    subst hc
                    simp [isStableCommonForm] at h
                  have hparts :
                      isStableCommonHead (.symbol c) = true ∧
                        isStableCommonList args = true := by
                    simpa [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
                      isForbiddenHeadSymbol, hchain, hcollapse, hsuperpose, hswitch,
                      hswitchm, hatomsubst, hnop, hfunction, hprogn, hprog1, hfoldall,
                      hlt, hgt] using h
                  have htail := translatePeTTaList_id_of_stableCommonList_aux args s hparts.2
                  have htail₁ : (translatePeTTa.translatePeTTaList args s).1 = args := by
                    exact congrArg Prod.fst htail
                  have htail₂ : (translatePeTTa.translatePeTTaList args s).2 = s := by
                    exact congrArg Prod.snd htail
                  simp [translatePeTTa, translatePeTTa.translatePeTTaList, hprogn, hprog1,
                    hfoldall, hlt, hgt, htail₁, htail₂]
      | var v =>
        have hargs : isStableCommonList args = true := by
          simpa [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
            isForbiddenHeadSymbol] using h
        have htail := translatePeTTaList_id_of_stableCommonList_aux args s hargs
        simp [translatePeTTa, translatePeTTa.translatePeTTaList, htail]
      | grounded g =>
        have hargs : isStableCommonList args = true := by
          simpa [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
            isForbiddenHeadSymbol] using h
        have htail := translatePeTTaList_id_of_stableCommonList_aux args s hargs
        simp [translatePeTTa, translatePeTTa.translatePeTTaList, htail]
      | expression es' =>
        have hparts : isStableCommonForm (.expression es') = true ∧ isStableCommonList args = true := by
          simpa [isStableCommonForm, isStableCommonExpr, isStableCommonHead,
            isForbiddenHeadSymbol] using h
        have hhd := translatePeTTa_id_of_stableCommonForm_aux (.expression es') s hparts.1
        have htail := translatePeTTaList_id_of_stableCommonList_aux args s hparts.2
        simp [translatePeTTa, translatePeTTa.translatePeTTaList, hhd, htail]

private theorem translatePeTTaList_id_of_stableCommonList_aux
    (xs : List Atom) (s : Nat) (h : isStableCommonList xs = true) :
    translatePeTTa.translatePeTTaList xs s = (xs, s) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp [isStableCommonList, Bool.and_eq_true] at h
    have hx := translatePeTTa_id_of_stableCommonForm_aux x s h.1
    have hxs := translatePeTTaList_id_of_stableCommonList_aux xs s h.2
    simp [translatePeTTa.translatePeTTaList, hx, hxs]
end

/-- `translatePeTTa` is identity on the stable common fragment. -/
theorem translatePeTTa_id_of_stableCommonForm (a : Atom) (s : Nat)
    (h : isStableCommonForm a = true) :
    translatePeTTa a s = (a, s) := by
  exact translatePeTTa_id_of_stableCommonForm_aux a s h

/-- First-order `foldall` lowering lands in the stable common fragment as soon
    as the recursively translated goal and init pieces do. -/
theorem translatePeTTa_foldall_preserves_stableCommonForm
    (agg goal init : Atom) (s : Nat)
    (hagg : isFirstOrderReducerAtom agg = true)
    (hgoal : isStableCommonForm (translatePeTTa goal s).1 = true)
    (hinit : isStableCommonForm (translatePeTTa init (translatePeTTa goal s).2).1 = true) :
    isStableCommonForm
      (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).1 = true := by
  obtain ⟨name, rfl⟩ := firstOrderReducerAtom_eq_symbol agg hagg
  have hnot : isForbiddenHeadSymbol (.symbol name) = false := by
    simpa [isFirstOrderReducerAtom] using hagg
  have hhead : isStableCommonHead (.symbol name) = true := by
    simpa [isStableCommonHead, isStableCommonForm] using hnot
  let accVar : Atom :=
    .var ("$__tr_acc_" ++ toString ((translatePeTTa init (translatePeTTa goal s).2).2 + 1 + 1))
  let itemVar : Atom :=
    .var ("$__tr_item_" ++ toString ((translatePeTTa init (translatePeTTa goal s).2).2 + 1 + 1 + 1))
  have happ : isStableCommonForm (.expression [.symbol name, accVar, itemVar]) = true := by
    have hcons := stableCommonForm_cons_of_head (.symbol name) [accVar, itemVar] hhead
    rw [hcons]
    simp [accVar, itemVar, isStableCommonList, isStableCommonForm]
  simp [translatePeTTa, freshVar, isStableCommonForm, isStableCommonExpr,
    isStableCommonHead, isForbiddenHeadSymbol, isStableCommonList, hgoal, hinit,
    hnot, accVar, itemVar, happ]

/-- The lowered first-order `foldall` term is already a fixed point for the
    HE↔PeTTa roundtrip. -/
theorem translatePeTTa_foldall_roundtrip_fixedPoint
    (agg goal init : Atom) (s : Nat)
    (hagg : isFirstOrderReducerAtom agg = true)
    (hgoal : isStableCommonForm (translatePeTTa goal s).1 = true)
    (hinit : isStableCommonForm (translatePeTTa init (translatePeTTa goal s).2).1 = true) :
    let (he, s1) := translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s
    let (petta2, s2) := translateHE he s1
    let (he2, _) := translatePeTTa petta2 s2
    he2 = he := by
  let hs : isStableCommonForm
      (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).1 = true :=
    translatePeTTa_foldall_preserves_stableCommonForm agg goal init s hagg hgoal hinit
  have hhe :
      translateHE
        (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).1
        (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).2
      =
      ((translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).1,
        (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).2) :=
    translateHE_id_of_stableCommonForm
      (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).1
      (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).2 hs
  have hpe :
      translatePeTTa
        (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).1
        (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).2
      =
      ((translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).1,
        (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).2) :=
    translatePeTTa_id_of_stableCommonForm
      (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).1
      (translatePeTTa (.expression [.symbol "foldall", agg, goal, init]) s).2 hs
  simpa [hs, hhe, hpe]

private theorem translatePeTTa_notForbidden_of_headSource_aux
    (a : Atom) (s : Nat) (h : isValidatedPeTTaHeadSource a = true) :
    isForbiddenHeadSymbol (translatePeTTa a s).1 = false := by
  cases a with
  | var _ => simp [translatePeTTa, isForbiddenHeadSymbol]
  | symbol c => simpa [translatePeTTa] using headSourcePeTTaSymbol_notForbidden_aux c h
  | grounded _ => simp [translatePeTTa, isForbiddenHeadSymbol]
  | expression es =>
      cases es with
      | nil => simp [translatePeTTa, isForbiddenHeadSymbol]
      | cons hd args =>
          cases hd with
          | symbol c =>
              by_cases hprogn : c = "progn"
              · subst hprogn
                cases args with
                | nil =>
                    simp [translatePeTTa, translatePeTTa.translatePeTTaProgn, isForbiddenHeadSymbol]
                | cons x xs =>
                    cases xs with
                    | nil =>
                        have hx : isValidatedPeTTaHeadSource x = true := by
                          simpa [isValidatedPeTTaHeadSource, isValidatedPeTTaPrognHeadArgs] using h
                        simpa [translatePeTTa, translatePeTTa.translatePeTTaProgn] using
                          translatePeTTa_notForbidden_of_headSource_aux x s hx
                    | cons _ _ =>
                        simp [translatePeTTa, translatePeTTa.translatePeTTaProgn,
                          freshVar, isForbiddenHeadSymbol]
              · by_cases hprog1 : c = "prog1"
                · subst hprog1
                  cases args with
                  | nil =>
                      simp [translatePeTTa, translatePeTTa.translatePeTTaProg1, isForbiddenHeadSymbol]
                  | cons x xs =>
                      cases xs with
                      | nil =>
                          have hx : isValidatedPeTTaHeadSource x = true := by
                            simpa [isValidatedPeTTaHeadSource, isValidatedPeTTaProg1HeadArgs] using h
                          simpa [translatePeTTa, translatePeTTa.translatePeTTaProg1] using
                            translatePeTTa_notForbidden_of_headSource_aux x s hx
                      | cons _ _ =>
                          simp [translatePeTTa, translatePeTTa.translatePeTTaProg1,
                            freshVar, isForbiddenHeadSymbol]
                · by_cases hfoldall : c = "foldall"
                  · subst hfoldall
                    cases args with
                    | nil => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                    | cons _ rest =>
                        cases rest with
                        | nil => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                        | cons _ rest =>
                            cases rest with
                            | nil => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                            | cons _ rest =>
                                cases rest with
                                | nil => simp [translatePeTTa, isForbiddenHeadSymbol]
                                | cons _ _ =>
                                    simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                  · by_cases hlt : c = "@<"
                    · subst hlt
                      cases args with
                      | nil => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                      | cons _ rest =>
                          cases rest with
                          | nil => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                          | cons _ rest =>
                              cases rest with
                              | nil => simp [translatePeTTa, isForbiddenHeadSymbol]
                              | cons _ _ =>
                                  simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                    · by_cases hgt : c = "@>"
                      · subst hgt
                        cases args with
                        | nil => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                        | cons _ rest =>
                            cases rest with
                            | nil => simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                            | cons _ rest =>
                                cases rest with
                                | nil => simp [translatePeTTa, isForbiddenHeadSymbol]
                                | cons _ _ =>
                                    simp [isValidatedPeTTaHeadSource, isValidatedPeTTaSource] at h
                      · simp [translatePeTTa, translatePeTTa.translatePeTTaList, hprogn,
                          hprog1, hfoldall, hlt, hgt, isForbiddenHeadSymbol]
          | var _ =>
              simp [translatePeTTa, translatePeTTa.translatePeTTaList, isForbiddenHeadSymbol]
          | grounded _ =>
              simp [translatePeTTa, translatePeTTa.translatePeTTaList, isForbiddenHeadSymbol]
          | expression _ =>
              simp [translatePeTTa, translatePeTTa.translatePeTTaList, isForbiddenHeadSymbol]

private theorem sizeOf_tail_lt_cons_atom (x : Atom) (xs : List Atom) :
    sizeOf xs < sizeOf (x :: xs) := by
  simp_wf

private theorem sizeOf_args_lt_expression_cons (hd : Atom) (args : List Atom) :
    sizeOf args < sizeOf (Atom.expression (hd :: args)) := by
  simp_wf

private theorem sizeOf_mem_lt_expression_cons
    (x hd : Atom) (args : List Atom) (hx : x ∈ hd :: args) :
    sizeOf x < sizeOf (Atom.expression (hd :: args)) := by
  have h1 : sizeOf x < sizeOf (hd :: args) := List.sizeOf_lt_of_mem hx
  have h2 : sizeOf (hd :: args) < sizeOf (Atom.expression (hd :: args)) := by
    simp_wf
  exact lt_trans h1 h2

private theorem translatePeTTaProgn_preserves_stableCommonForm_with
    (bound : Nat)
    (step : ∀ (a : Atom) (s : Nat),
      isValidatedPeTTaSource a = true →
      sizeOf a < bound →
      isStableCommonForm (translatePeTTa a s).1 = true)
    (args : List Atom) (s : Nat) (h : isValidatedPeTTaList args = true)
    (hbound : ∀ {a : Atom}, a ∈ args → sizeOf a < bound) :
    isStableCommonForm (translatePeTTa.translatePeTTaProgn args s).1 = true := by
  induction args generalizing s with
  | nil =>
      simp [translatePeTTa.translatePeTTaProgn, isStableCommonForm]
  | cons x xs ih =>
      cases xs with
      | nil =>
          have hxsrc : isValidatedPeTTaSource x = true := by
            simpa [isValidatedPeTTaList, Bool.and_eq_true] using h
          have hx := step x s hxsrc (hbound (by simp))
          simpa [translatePeTTa.translatePeTTaProgn] using hx
      | cons y ys =>
          have hvalid : isValidatedPeTTaList (x :: y :: ys) = true := by
            simpa using h
          simp [isValidatedPeTTaList, Bool.and_eq_true] at hvalid
          have hx := step x (freshVar "discard" s).2 hvalid.1 (hbound (by simp))
          have htailvalid : isValidatedPeTTaList (y :: ys) = true := by
            simpa [isValidatedPeTTaList, Bool.and_eq_true] using hvalid.2
          have hrest :=
            ih (translatePeTTa x (freshVar "discard" s).2).2 htailvalid (by
              intro a ha
              exact hbound (by simp [ha]))
          have hhead : isStableCommonHead (.symbol "let") = true := by
            simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
          have hcons :=
            stableCommonForm_cons_of_head (.symbol "let")
              [(freshVar "discard" s).1,
               (translatePeTTa x (freshVar "discard" s).2).1,
               (translatePeTTa.translatePeTTaProgn (y :: ys)
                  (translatePeTTa x (freshVar "discard" s).2).2).1] hhead
          have hbody :
              isStableCommonForm
                (.expression
                  [.symbol "let",
                   (freshVar "discard" s).1,
                   (translatePeTTa x (freshVar "discard" s).2).1,
                   (translatePeTTa.translatePeTTaProgn (y :: ys)
                      (translatePeTTa x (freshVar "discard" s).2).2).1]) = true := by
            rw [hcons]
            have hx' : isStableCommonForm (translatePeTTa x (s + 1)).1 = true := by
              simpa [freshVar] using hx
            simpa [freshVar, isStableCommonList, isStableCommonForm] using
              And.intro hx' hrest
          simpa [translatePeTTa.translatePeTTaProgn, freshVar] using hbody

private theorem translatePeTTaProg1Rest_preserves_stableCommonForm_with
    (bound : Nat)
    (step : ∀ (a : Atom) (s : Nat),
      isValidatedPeTTaSource a = true →
      sizeOf a < bound →
      isStableCommonForm (translatePeTTa a s).1 = true)
    (args : List Atom) (resultVar : Atom) (s : Nat)
    (hresult : isStableCommonForm resultVar = true)
    (h : isValidatedPeTTaList args = true)
    (hbound : ∀ {a : Atom}, a ∈ args → sizeOf a < bound) :
    isStableCommonForm (translatePeTTa.translatePeTTaProg1Rest args resultVar s).1 = true := by
  induction args generalizing resultVar s with
  | nil =>
      simpa [translatePeTTa.translatePeTTaProg1Rest] using hresult
  | cons x xs ih =>
      simp [isValidatedPeTTaList, Bool.and_eq_true] at h
      have hx := step x (freshVar "discard" s).2 h.1 (hbound (by simp))
      have hrest :=
        ih _ (translatePeTTa x (freshVar "discard" s).2).2 hresult h.2 (by
          intro a ha
          exact hbound (by simp [ha]))
      have hhead : isStableCommonHead (.symbol "let") = true := by
        simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
      have hcons :=
        stableCommonForm_cons_of_head (.symbol "let")
          [(freshVar "discard" s).1,
           (translatePeTTa x (freshVar "discard" s).2).1,
           (translatePeTTa.translatePeTTaProg1Rest xs resultVar
             (translatePeTTa x (freshVar "discard" s).2).2).1] hhead
      have hbody :
          isStableCommonForm
            (.expression
              [.symbol "let",
               (freshVar "discard" s).1,
               (translatePeTTa x (freshVar "discard" s).2).1,
               (translatePeTTa.translatePeTTaProg1Rest xs resultVar
                 (translatePeTTa x (freshVar "discard" s).2).2).1]) = true := by
        rw [hcons]
        have hx' : isStableCommonForm (translatePeTTa x (s + 1)).1 = true := by
          simpa [freshVar] using hx
        simpa [freshVar, isStableCommonList, isStableCommonForm] using
          And.intro hx' hrest
      simpa [translatePeTTa.translatePeTTaProg1Rest, freshVar] using hbody

private theorem translatePeTTaProg1_preserves_stableCommonForm_with
    (bound : Nat)
    (step : ∀ (a : Atom) (s : Nat),
      isValidatedPeTTaSource a = true →
      sizeOf a < bound →
      isStableCommonForm (translatePeTTa a s).1 = true)
    (args : List Atom) (s : Nat) (h : isValidatedPeTTaList args = true)
    (hbound : ∀ {a : Atom}, a ∈ args → sizeOf a < bound) :
    isStableCommonForm (translatePeTTa.translatePeTTaProg1 args s).1 = true := by
  induction args generalizing s with
  | nil =>
      simp [translatePeTTa.translatePeTTaProg1, isStableCommonForm]
  | cons x xs ih =>
      cases xs with
      | nil =>
          have hxsrc : isValidatedPeTTaSource x = true := by
            simpa [isValidatedPeTTaList, Bool.and_eq_true] using h
          have hx := step x s hxsrc (hbound (by simp))
          simpa [translatePeTTa.translatePeTTaProg1] using hx
      | cons y ys =>
          have hvalid : isValidatedPeTTaList (x :: y :: ys) = true := by
            simpa using h
          simp [isValidatedPeTTaList, Bool.and_eq_true] at hvalid
          have hresult : isStableCommonForm (freshVar "result" s).1 = true := by
            simp [freshVar, isStableCommonForm]
          have hx := step x (freshVar "result" s).2 hvalid.1 (hbound (by simp))
          have htailvalid : isValidatedPeTTaList (y :: ys) = true := by
            simpa [isValidatedPeTTaList, Bool.and_eq_true] using hvalid.2
          have htailbound : ∀ {a : Atom}, a ∈ (y :: ys) → sizeOf a < bound := by
            intro a ha
            exact hbound (by simp [ha])
          have hrest :=
            translatePeTTaProg1Rest_preserves_stableCommonForm_with bound step
              (y :: ys) (freshVar "result" s).1
              (translatePeTTa x (freshVar "result" s).2).2 hresult htailvalid htailbound
          have hhead : isStableCommonHead (.symbol "let") = true := by
            simp [isStableCommonHead, isStableCommonForm, isForbiddenHeadSymbol]
          have hcons :=
            stableCommonForm_cons_of_head (.symbol "let")
              [(freshVar "result" s).1,
               (translatePeTTa x (freshVar "result" s).2).1,
               (translatePeTTa.translatePeTTaProg1Rest (y :: ys)
                  (freshVar "result" s).1
                  (translatePeTTa x (freshVar "result" s).2).2).1] hhead
          have hbody :
              isStableCommonForm
                (.expression
                  [.symbol "let",
                   (freshVar "result" s).1,
                   (translatePeTTa x (freshVar "result" s).2).1,
                   (translatePeTTa.translatePeTTaProg1Rest (y :: ys)
                      (freshVar "result" s).1
                      (translatePeTTa x (freshVar "result" s).2).2).1]) = true := by
            rw [hcons]
            have hx' : isStableCommonForm (translatePeTTa x (s + 1)).1 = true := by
              simpa [freshVar] using hx
            simpa [freshVar, isStableCommonList, isStableCommonForm, hresult] using
              And.intro hx' hrest
          simpa [translatePeTTa.translatePeTTaProg1, freshVar] using hbody

mutual

private theorem translatePeTTa_preserves_stableCommonForm_aux
    (a : Atom) (s : Nat) (h : isValidatedPeTTaSource a = true) :
    isStableCommonForm (translatePeTTa a s).1 = true := by
  cases a with
  | var _ => simp [translatePeTTa, isStableCommonForm]
  | symbol _ => simp [translatePeTTa, isStableCommonForm]
  | grounded _ => simp [translatePeTTa, isStableCommonForm]
  | expression es =>
      cases es with
      | nil =>
          simp [translatePeTTa, translatePeTTa.translatePeTTaList,
            isStableCommonForm, isStableCommonExpr]
      | cons hd args =>
          cases hd with
          | symbol c =>
              by_cases hprogn : c = "progn"
              · subst hprogn
                have hargs : isValidatedPeTTaList args = true := by
                  simpa [isValidatedPeTTaSource] using h
                have hbound :
                    ∀ {a : Atom}, a ∈ args →
                      sizeOf a < sizeOf (Atom.expression (.symbol "progn" :: args)) := by
                  intro a ha
                  exact sizeOf_mem_lt_expression_cons a (.symbol "progn") args (by simp [ha])
                have hprognForm :
                    isStableCommonForm (translatePeTTa.translatePeTTaProgn args s).1 = true :=
                  translatePeTTaProgn_preserves_stableCommonForm_with
                    (sizeOf (Atom.expression (.symbol "progn" :: args)))
                    (fun a s ha hsmall => by
                      have _ : sizeOf a < sizeOf (Atom.expression (.symbol "progn" :: args)) := hsmall
                      exact translatePeTTa_preserves_stableCommonForm_aux a s ha)
                    args s hargs hbound
                simpa [translatePeTTa] using hprognForm
              · by_cases hprog1 : c = "prog1"
                · subst hprog1
                  have hargs : isValidatedPeTTaList args = true := by
                    simpa [isValidatedPeTTaSource, hprogn] using h
                  have hbound :
                      ∀ {a : Atom}, a ∈ args →
                        sizeOf a < sizeOf (Atom.expression (.symbol "prog1" :: args)) := by
                    intro a ha
                    exact sizeOf_mem_lt_expression_cons a (.symbol "prog1") args (by simp [ha])
                  have hprog1Form :
                      isStableCommonForm (translatePeTTa.translatePeTTaProg1 args s).1 = true :=
                    translatePeTTaProg1_preserves_stableCommonForm_with
                      (sizeOf (Atom.expression (.symbol "prog1" :: args)))
                      (fun a s ha hsmall => by
                        have _ : sizeOf a < sizeOf (Atom.expression (.symbol "prog1" :: args)) := hsmall
                        exact translatePeTTa_preserves_stableCommonForm_aux a s ha)
                      args s hargs hbound
                  simpa [translatePeTTa] using hprog1Form
                · by_cases hfoldall : c = "foldall"
                  · subst hfoldall
                    cases args with
                    | nil => simp [isValidatedPeTTaSource] at h
                    | cons agg rest =>
                        cases rest with
                        | nil => simp [isValidatedPeTTaSource] at h
                        | cons goal rest =>
                            cases rest with
                            | nil => simp [isValidatedPeTTaSource] at h
                            | cons init rest =>
                                cases rest with
                                | nil =>
                                    have hparts :
                                        (isFirstOrderReducerAtom agg = true ∧
                                          isValidatedPeTTaSource goal = true) ∧
                                            isValidatedPeTTaSource init = true := by
                                      simpa [isValidatedPeTTaSource, Bool.and_eq_true] using h
                                    have hgoal :=
                                      translatePeTTa_preserves_stableCommonForm_aux goal s hparts.1.2
                                    have hinit :=
                                      translatePeTTa_preserves_stableCommonForm_aux init
                                        (translatePeTTa goal s).2 hparts.2
                                    exact translatePeTTa_foldall_preserves_stableCommonForm
                                      agg goal init s hparts.1.1 hgoal hinit
                                | cons _ _ => simp [isValidatedPeTTaSource] at h
                  · by_cases hlt : c = "@<"
                    · subst hlt
                      cases args with
                      | nil => simp [isValidatedPeTTaSource] at h
                      | cons a rest =>
                          cases rest with
                          | nil => simp [isValidatedPeTTaSource] at h
                          | cons b rest =>
                              cases rest with
                              | nil =>
                                  have hpair :
                                      isValidatedPeTTaSource a = true ∧
                                        isValidatedPeTTaSource b = true := by
                                    simpa [isValidatedPeTTaSource, Bool.and_eq_true] using h
                                  have ha :=
                                    translatePeTTa_preserves_stableCommonForm_aux a s hpair.1
                                  have hb :=
                                    translatePeTTa_preserves_stableCommonForm_aux b
                                      (translatePeTTa a s).2 hpair.2
                                  simp [translatePeTTa, isStableCommonForm, isStableCommonExpr,
                                    isStableCommonHead, isForbiddenHeadSymbol,
                                    isStableCommonList, ha, hb]
                              | cons _ _ => simp [isValidatedPeTTaSource] at h
                    · by_cases hgt : c = "@>"
                      · subst hgt
                        cases args with
                        | nil => simp [isValidatedPeTTaSource] at h
                        | cons a rest =>
                            cases rest with
                            | nil => simp [isValidatedPeTTaSource] at h
                            | cons b rest =>
                                cases rest with
                                | nil =>
                                    have hpair :
                                        isValidatedPeTTaSource a = true ∧
                                          isValidatedPeTTaSource b = true := by
                                      simpa [isValidatedPeTTaSource, Bool.and_eq_true] using h
                                    have ha :=
                                      translatePeTTa_preserves_stableCommonForm_aux a s hpair.1
                                    have hb :=
                                      translatePeTTa_preserves_stableCommonForm_aux b
                                        (translatePeTTa a s).2 hpair.2
                                    simp [translatePeTTa, isStableCommonForm, isStableCommonExpr,
                                      isStableCommonHead, isForbiddenHeadSymbol,
                                      isStableCommonList, ha, hb]
                                | cons _ _ => simp [isValidatedPeTTaSource] at h
                      · have hchain : c ≠ "chain" := by
                          intro hc
                          subst hc
                          simp [isValidatedPeTTaSource] at h
                        have hcollapse : c ≠ "collapse-bind" := by
                          intro hc
                          subst hc
                          simp [isValidatedPeTTaSource] at h
                        have hsuperpose : c ≠ "superpose-bind" := by
                          intro hc
                          subst hc
                          simp [isValidatedPeTTaSource] at h
                        have hswitch : c ≠ "switch" := by
                          intro hc
                          subst hc
                          simp [isValidatedPeTTaSource] at h
                        have hswitchm : c ≠ "switch-minimal" := by
                          intro hc
                          subst hc
                          simp [isValidatedPeTTaSource] at h
                        have hatomsubst : c ≠ "atom-subst" := by
                          intro hc
                          subst hc
                          simp [isValidatedPeTTaSource] at h
                        have hnop : c ≠ "nop" := by
                          intro hc
                          subst hc
                          simp [isValidatedPeTTaSource] at h
                        have hfunction : c ≠ "function" := by
                          intro hc
                          subst hc
                          simp [isValidatedPeTTaSource] at h
                        have hparts :
                            isValidatedPeTTaHeadSource (.symbol c) = true ∧
                              isValidatedPeTTaList args = true := by
                          simpa [isValidatedPeTTaSource, isValidatedPeTTaHeadSource,
                            Bool.and_eq_true, hchain, hcollapse, hsuperpose, hswitch,
                            hswitchm, hatomsubst, hnop, hfunction, hprogn, hprog1,
                            hfoldall, hlt, hgt] using h
                        have htail :
                            isStableCommonList (translatePeTTa.translatePeTTaList args s).1 = true :=
                          translatePeTTaList_preserves_stableCommonList_aux args s hparts.2
                        have hnot : isForbiddenHeadSymbol (.symbol c) = false :=
                          headSourcePeTTaSymbol_notForbidden_aux c hparts.1
                        have hhead : isStableCommonHead (.symbol c) = true := by
                          simpa [isStableCommonHead, isStableCommonForm] using hnot
                        have hcons :=
                          stableCommonForm_cons_of_head (.symbol c)
                            (translatePeTTa.translatePeTTaList args s).1 hhead
                        have hbody :
                            isStableCommonForm
                              (.expression
                                (.symbol c :: (translatePeTTa.translatePeTTaList args s).1)) = true := by
                          rw [hcons]
                          exact htail
                        simpa [translatePeTTa, translatePeTTa.translatePeTTaList,
                          hprogn, hprog1, hfoldall, hlt, hgt] using hbody
          | var _ =>
              have hargs : isValidatedPeTTaList args = true := by
                simpa [isValidatedPeTTaSource, isValidatedPeTTaHeadSource] using h
              have htail := translatePeTTaList_preserves_stableCommonList_aux args s hargs
              simp [translatePeTTa, translatePeTTa.translatePeTTaList, isStableCommonForm,
                isStableCommonExpr, isStableCommonHead, isForbiddenHeadSymbol,
                isStableCommonList, htail]
          | grounded _ =>
              have hargs : isValidatedPeTTaList args = true := by
                simpa [isValidatedPeTTaSource, isValidatedPeTTaHeadSource] using h
              have htail := translatePeTTaList_preserves_stableCommonList_aux args s hargs
              simp [translatePeTTa, translatePeTTa.translatePeTTaList, isStableCommonForm,
                isStableCommonExpr, isStableCommonHead, isForbiddenHeadSymbol,
                isStableCommonList, htail]
          | expression es' =>
              have hparts :
                  isValidatedPeTTaHeadSource (.expression es') = true ∧
                    isValidatedPeTTaList args = true := by
                simpa [isValidatedPeTTaSource] using h
              have hhdsrc :=
                validatedPeTTaSource_of_headSource_aux (.expression es') hparts.1
              have hhdform :=
                translatePeTTa_preserves_stableCommonForm_aux (.expression es') s hhdsrc
              have hhdnot :=
                translatePeTTa_notForbidden_of_headSource_aux (.expression es') s hparts.1
              have hhd : isStableCommonHead (translatePeTTa (.expression es') s).1 = true := by
                simpa [isStableCommonHead] using
                  stableCommonHead_of_stableCommonForm _ hhdform hhdnot
              have htail :=
                translatePeTTaList_preserves_stableCommonList_aux args
                  (translatePeTTa (.expression es') s).2 hparts.2
              have hcons :=
                stableCommonForm_cons_of_head (translatePeTTa (.expression es') s).1
                  (translatePeTTa.translatePeTTaList args (translatePeTTa (.expression es') s).2).1
                  hhd
              have hbody :
                  isStableCommonForm
                    (.expression
                      ((translatePeTTa (.expression es') s).1 ::
                        (translatePeTTa.translatePeTTaList args
                          (translatePeTTa (.expression es') s).2).1)) = true := by
                rw [hcons]
                exact htail
              simpa [translatePeTTa, translatePeTTa.translatePeTTaList] using hbody
  termination_by sizeOf a
  decreasing_by
    all_goals
      subst_vars
      try simpa using hsmall
      try
        have hmem := List.sizeOf_lt_of_mem hxInArgs
        omega
      simp_wf
      try omega

private theorem translatePeTTaList_preserves_stableCommonList_aux
    (xs : List Atom) (s : Nat) (h : isValidatedPeTTaList xs = true) :
    isStableCommonList (translatePeTTa.translatePeTTaList xs s).1 = true := by
  cases xs with
  | nil => simp [translatePeTTa.translatePeTTaList, isStableCommonList]
  | cons x xs =>
      simp [isValidatedPeTTaList, Bool.and_eq_true] at h
      have hx : isStableCommonForm (translatePeTTa x s).1 = true :=
        translatePeTTa_preserves_stableCommonForm_aux x s h.1
      have hxs :
          isStableCommonList (translatePeTTa.translatePeTTaList xs (translatePeTTa x s).2).1 = true :=
        translatePeTTaList_preserves_stableCommonList_aux xs (translatePeTTa x s).2 h.2
      simp [translatePeTTa.translatePeTTaList, isStableCommonList, hx, hxs]
  termination_by sizeOf xs
  decreasing_by
    all_goals
      subst_vars
      try simpa using hsmall
      try
        have hmem := List.sizeOf_lt_of_mem hxInArgs
        omega
      simp_wf
      try omega
end

/-- Validated PeTTa inputs translate into the stable common fragment. -/
theorem translatePeTTa_preserves_stableCommonForm (a : Atom) (s : Nat)
    (h : isValidatedPeTTaSource a = true) :
    isStableCommonForm (translatePeTTa a s).1 = true :=
  translatePeTTa_preserves_stableCommonForm_aux a s h

/-- Corrected PeTTa→HE→PeTTa fixed-point theorem on the validated PeTTa fragment. -/
theorem translatePeTTa_roundtrip_fixedPoint_of_validatedPeTTaSource (a : Atom) (s : Nat)
    (h : isValidatedPeTTaSource a = true) :
    let (he, s1) := translatePeTTa a s
    let (petta2, s2) := translateHE he s1
    let (he2, _) := translatePeTTa petta2 s2
    he2 = he := by
  let hs : isStableCommonForm (translatePeTTa a s).1 = true :=
    translatePeTTa_preserves_stableCommonForm a s h
  have hhe : translateHE (translatePeTTa a s).1 (translatePeTTa a s).2 =
      ((translatePeTTa a s).1, (translatePeTTa a s).2) :=
    translateHE_id_of_stableCommonForm (translatePeTTa a s).1 (translatePeTTa a s).2 hs
  have hpe : translatePeTTa (translatePeTTa a s).1 (translatePeTTa a s).2 =
      ((translatePeTTa a s).1, (translatePeTTa a s).2) :=
    translatePeTTa_id_of_stableCommonForm (translatePeTTa a s).1 (translatePeTTa a s).2 hs
  simpa [hs, hhe, hpe]

/-- Corrected HE→PeTTa→HE fixed-point theorem on the validated HE fragment. -/
theorem translateHE_roundtrip_fixedPoint_of_validatedHESource (a : Atom) (s : Nat)
    (h : isValidatedHESource a = true) :
    let (petta, s1) := translateHE a s
    let (he2, s2) := translatePeTTa petta s1
    let (petta2, _) := translateHE he2 s2
    petta2 = petta := by
  let hs : isStableCommonForm (translateHE a s).1 = true :=
    translateHE_preserves_stableCommonForm a s h
  have hpe : translatePeTTa (translateHE a s).1 (translateHE a s).2 =
      ((translateHE a s).1, (translateHE a s).2) :=
    translatePeTTa_id_of_stableCommonForm (translateHE a s).1 (translateHE a s).2 hs
  have hhe : translateHE (translateHE a s).1 (translateHE a s).2 =
      ((translateHE a s).1, (translateHE a s).2) :=
    translateHE_id_of_stableCommonForm (translateHE a s).1 (translateHE a s).2 hs
  simpa [hs, hpe, hhe]

/-- The universal HE→PeTTa→HE idempotence claim over arbitrary `Atom` is false.

The translators intentionally leave binder slots untouched in `chain` and
`atom-subst`.  If such a slot itself contains an HE-only form, the second
`translateHE` pass can still rewrite it.  The correct theorem therefore needs a
well-formed HE fragment with typed binder positions, not bare `Atom`. -/
example :
    let a : Atom := .expression
      [.symbol "chain",
       .symbol "e",
       .expression [.symbol "chain", .symbol "x", .var "$y", .symbol "z"],
       .symbol "b"]
    let (petta, s1) := translateHE a 0
    let (he2, s2) := translatePeTTa petta s1
    (translateHE he2 s2).1 ≠ petta := by
  decide

/-- The HE→PeTTa translation produces PeTTa-normal output on the common fragment.
    Verified computationally. -/
example : isPeTTaNormal (translateHE (.expression [.symbol "chain",
    .symbol "e", .var "$x", .symbol "b"]) 0).1 = true := rfl

example : isPeTTaNormal (translateHE (.expression [.symbol "nop",
    .var "$x"]) 0).1 = true := rfl

example : isPeTTaNormal (translateHE (.expression [.symbol "collapse-bind",
    .symbol "x"]) 0).1 = true := rfl

example : isPeTTaNormal (translateHE (.expression [.symbol "function",
    .expression [.symbol "return", .symbol "42"]]) 0).1 = true := rfl

/-- Similarly, `translatePeTTa` produces HE-compatible output. -/
def isHENormal : Atom → Bool
  | .expression (.symbol "progn" :: _) => false
  | .expression (.symbol "prog1" :: _) => false
  | .expression (.symbol "foldall" :: _) => false
  | .expression [.symbol "@<", _, _] => false
  | .expression [.symbol "@>", _, _] => false
  | _ => true

/-
The tempting universal claims

* `isHENormal (translatePeTTa a s).1 = true`
* `isHENormal a = true -> isHENormal (optimizeTranslatedHE a) = true`

are both false on arbitrary `Atom`.

Positive example: well-formed PeTTa surface forms lower to HE-normal output.
Negative examples:
* malformed heads such as `(foldall)` fall through unchanged, so they are not HE-normal;
* the optimizer can expose a nested non-HE-normal PeTTa term by eliminating a
  translator-generated result `let`.

The honest theorem layer remains the validated/stable-common fragment proved
above, including the first-order `foldall` fixed-point theorem. -/

example : isHENormal (translatePeTTa (.expression [.symbol "progn",
    .symbol "a", .symbol "b"]) 0).1 = true := rfl

example : isHENormal (translatePeTTa (.expression [.symbol "prog1",
    .symbol "a", .symbol "b"]) 0).1 = true := rfl

example : isHENormal (translatePeTTa (.expression [.symbol "progn",
    .symbol "a", .symbol "b", .symbol "c", .symbol "d"]) 0).1 = true := rfl

example : isHENormal (translatePeTTa (.expression
    [.symbol "foldall", .symbol "merge", .expression [.symbol "twohop-item"], .symbol "0"]) 0).1 = true := rfl

example : isHENormal (translatePeTTa (.expression [.symbol "foldall"]) 0).1 = false := rfl

example : isHENormal
    (optimizeTranslatedHE
      (.expression [.symbol "let", .var "$__tr_result_1",
        .expression [.symbol "progn", .symbol "a", .symbol "b"],
        .var "$__tr_result_1"])) = false := by
  native_decide

example : isHENormal (translatePeTTaOptimized (.expression [.symbol "prog1",
    .symbol "a", .symbol "b"]) 0).1 = true := by
  native_decide

/-- The HE→PeTTa→HE roundtrip is idempotent: translating twice gives the same
    PeTTa normal form as translating once. Verified computationally on key cases. -/
example :
    let (petta, s1) := translateHE (.expression [.symbol "chain",
      .symbol "e", .var "$x", .symbol "b"]) 0
    let (he2, s2) := translatePeTTa petta s1
    let (petta2, _) := translateHE he2 s2
    petta = petta2 := rfl

example :
    let (petta, s1) := translateHE (.expression [.symbol "nop", .var "$x"]) 0
    let (he2, s2) := translatePeTTa petta s1
    let (petta2, _) := translateHE he2 s2
    petta = petta2 := rfl

example :
    let (petta, s1) := translateHE (.expression [.symbol "collapse-bind", .symbol "x"]) 0
    let (he2, s2) := translatePeTTa petta s1
    let (petta2, _) := translateHE he2 s2
    petta = petta2 := rfl

/-- The PeTTa→HE→PeTTa roundtrip is also idempotent. -/
example :
    let (he, s1) := translatePeTTa (.expression [.symbol "progn",
      .symbol "a", .symbol "b"]) 0
    let (petta2, s2) := translateHE he s1
    let (he2, _) := translatePeTTa petta2 s2
    he = he2 := rfl

example :
    let (he, s1) := translatePeTTa (.expression [.symbol "prog1",
      .symbol "a", .symbol "b"]) 0
    let (petta2, s2) := translateHE he s1
    let (he2, _) := translatePeTTa petta2 s2
    he = he2 := rfl

/- A future roundtrip theorem should quantify over a typed or validated HE
fragment, not arbitrary `Atom`. The executable examples above still show the
intended behavior on ordinary HE/PeTTa programs. -/

end Mettapedia.Languages.MeTTa.Translation
