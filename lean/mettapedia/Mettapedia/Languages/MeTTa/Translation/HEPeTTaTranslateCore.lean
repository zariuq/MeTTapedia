import Mettapedia.Languages.MeTTa.OSLFCore.Bridge
import Mettapedia.Languages.MeTTa.Translation.HEPeTTaSound
import Mettapedia.Languages.MeTTa.Translation.HEPeTTaValidatedSurface

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

/-- Shared termination script for simple `sizeOf` mutual recursions. -/
macro "decr_sizeof_simple" : tactic =>
  `(tactic|
    all_goals
      first
      | simp_wf; omega
      | simp_wf)

mutual
  /-- Syntactic occurrence check used by the optimizer guards. -/
  def containsAtom (needle : Atom) : Atom → Bool
    | .expression es =>
        if .expression es == needle then true else containsAtomList needle es
    | a => a == needle
  termination_by a => sizeOf a
  decreasing_by
    decr_sizeof_simple

  def containsAtomList (needle : Atom) : List Atom → Bool
    | [] => false
    | x :: xs => containsAtom needle x || containsAtomList needle xs
  termination_by xs => sizeOf xs
  decreasing_by
    decr_sizeof_simple
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
    decr_sizeof_simple

  def containsHeadSymbolList (sym : String) : List Atom → Bool
    | [] => false
    | x :: xs => containsHeadSymbol sym x || containsHeadSymbolList sym xs
  termination_by xs => sizeOf xs
  decreasing_by
    decr_sizeof_simple
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
    decr_sizeof_simple

  /-- Optimize each atom in a list. -/
  def optimizeTranslatedHEList : List Atom → List Atom
    | [] => []
    | x :: xs => optimizeTranslatedHE x :: optimizeTranslatedHEList xs
  termination_by xs => sizeOf xs
  decreasing_by
    decr_sizeof_simple
end

/-- Optimized PeTTa→HE translation used by the executable file translator. -/
def translatePeTTaOptimized (a : Atom) (supply : Nat) : Atom × Nat :=
  let (he, s1) := translatePeTTa a supply
  (optimizeTranslatedHE he, s1)

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


end Mettapedia.Languages.MeTTa.Translation
