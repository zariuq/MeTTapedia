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
    | `(progn A B)`                 | `(let $fresh A' B')`     |
    | `(progn A B C)`               | nested lets              |
    | `(prog1 A B)`                 | `(let $r A' (let $d B' $r))` |
    | `(@< A B)`                    | `(<s A' B')`             |
    | `(@> A B)`                    | `(not (<s A' B'))`       |
    | `(expr ...)`                  | recurse into subterms    |
    | variable / symbol / other     | identity                 | -/
def translatePeTTa (a : Atom) (supply : Nat) : Atom × Nat :=
  match a with
  -- progn A B → let $fresh A' B'
  | .expression [.symbol "progn", a', b'] =>
    let (fresh, s1) := freshVar "discard" supply
    let (ta, s2) := translatePeTTa a' s1
    let (tb, s3) := translatePeTTa b' s2
    (.expression [.symbol "let", fresh, ta, tb], s3)
  -- progn A B C → nested lets
  | .expression [.symbol "progn", a', b', c'] =>
    let (f1, s1) := freshVar "discard" supply
    let (f2, s2) := freshVar "discard" s1
    let (ta, s3) := translatePeTTa a' s2
    let (tb, s4) := translatePeTTa b' s3
    let (tc, s5) := translatePeTTa c' s4
    (.expression [.symbol "let", f1, ta, .expression [.symbol "let", f2, tb, tc]], s5)
  -- prog1 A B → let $r A' (let $d B' $r)
  | .expression [.symbol "prog1", a', b'] =>
    let (freshR, s1) := freshVar "result" supply
    let (freshD, s2) := freshVar "discard" s1
    let (ta, s3) := translatePeTTa a' s2
    let (tb, s4) := translatePeTTa b' s3
    (.expression [.symbol "let", freshR, ta,
      .expression [.symbol "let", freshD, tb, freshR]], s4)
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
  translatePeTTaList (xs : List Atom) (supply : Nat) : List Atom × Nat :=
    match xs with
    | [] => ([], supply)
    | x :: rest =>
      let (tx, s1) := translatePeTTa x supply
      let (trest, s2) := translatePeTTaList rest s1
      (tx :: trest, s2)

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

-- PeTTa: progn → let with fresh
#eval
  let (result, supply) := translatePeTTa
    (.expression [.symbol "progn",
      .expression [.symbol "println!", .symbol "hello"],
      .symbol "ok"]) 0
  (repr result, supply)
  -- Expected: (let $__tr_discard_1 (println! hello) ok), supply = 1

-- PeTTa: prog1 → let with result capture
#eval
  let (result, supply) := translatePeTTa
    (.expression [.symbol "prog1",
      .expression [.symbol "compute"],
      .expression [.symbol "side-effect"]]) 0
  (repr result, supply)
  -- Expected: (let $__tr_result_1 (compute) (let $__tr_discard_2 (side-effect) $__tr_result_1))

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

/-- `translatePeTTa` preserves Translatable. -/
theorem translatePeTTa_translatable (a : Atom) (s : Nat)
    (h : Translatable a) : Translatable (translatePeTTa a s).1 := by
  have : ∀ (bound : Nat) (a : Atom), sizeOf a ≤ bound →
      ∀ s, Translatable a → Translatable (translatePeTTa a s).1 := by
    intro bound
    induction bound with
    | zero =>
      intro a ha s _
      exfalso; cases a <;> simp_all
    | succ n ih_bound =>
      intro a ha s ht
      cases a with
      | var v => exact ht
      | symbol nm => exact ht
      | grounded g => exact ht
      | expression es =>
        cases es with
        | nil => exfalso; simp [Translatable, atomToPattern] at ht
        | cons hd args =>
          cases hd with
          | symbol c =>
            have hargs := translatable_args_of_expr c args ht
            have harg_le : ∀ a' ∈ args, sizeOf a' ≤ n := by
              intro a' ha'
              have hlt : sizeOf a' < sizeOf (Atom.symbol c :: args) :=
                List.sizeOf_lt_of_mem (a := a') (as := Atom.symbol c :: args)
                  (List.mem_cons_of_mem _ ha')
              simp at hlt ha; omega
            have harg_ih : ∀ a' ∈ args, ∀ s', Translatable a' →
                Translatable (translatePeTTa a' s').1 :=
              fun a' ha' s' ht' => ih_bound a' (harg_le a' ha') s' ht'
            have hall_translated :
                ∀ x ∈ (translatePeTTa.translatePeTTaList args s).1, Translatable x :=
              translatePeTTaList_mem_translatable (bound := n + 1)
                (fun a' hlt s' ht' => ih_bound a' (Nat.le_of_lt_succ hlt) s' ht')
                args s
                (fun x hx => Nat.lt_succ_of_le (harg_le x hx))
                hargs
            have hgeneric :
                Translatable (.expression (.symbol c :: (translatePeTTa.translatePeTTaList args s).1)) :=
              rebuild_same_head c args (translatePeTTa.translatePeTTaList args s).1
                ht (translatePeTTaList_length args s) hall_translated
            -- PeTTa has 5 rewrite rules + generic. Case-split on head.
            by_cases hprogn : c = "progn"
            · subst hprogn
              cases args with
              | nil => simpa [translatePeTTa, translatePeTTa.translatePeTTaList] using hgeneric
              | cons a' rest =>
                cases rest with
                | nil => simpa [translatePeTTa, translatePeTTa.translatePeTTaList] using hgeneric
                | cons b' rest =>
                  cases rest with
                  | nil =>
                    -- progn A B → let $fresh A' B'
                    have hfresh : Translatable (freshVar "discard" s).1 := by
                      simp [freshVar, Translatable, atomToPattern]
                    have ha' : Translatable (translatePeTTa a' (freshVar "discard" s).2).1 :=
                      harg_ih a' (by simp) _ (hargs a' (by simp))
                    have hb' : Translatable (translatePeTTa b' (translatePeTTa a' (freshVar "discard" s).2).2).1 :=
                      harg_ih b' (by simp) _ (hargs b' (by simp))
                    apply translatable_expr_of_args "let"
                      [(freshVar "discard" s).1,
                       (translatePeTTa a' (freshVar "discard" s).2).1,
                       (translatePeTTa b' (translatePeTTa a' (freshVar "discard" s).2).2).1]
                      (by decide) (by decide)
                    intro x hx; simp at hx
                    rcases hx with rfl | rfl | rfl
                    · exact hfresh
                    · exact ha'
                    · exact hb'
                  | cons c' rest =>
                    cases rest with
                    | nil =>
                      -- progn A B C → nested lets
                      have hf1 : Translatable (freshVar "discard" s).1 := by
                        simp [freshVar, Translatable, atomToPattern]
                      have hf2 : Translatable (freshVar "discard" (freshVar "discard" s).2).1 := by
                        simp [freshVar, Translatable, atomToPattern]
                      have s2 := (freshVar "discard" (freshVar "discard" s).2).2
                      have ha'' := harg_ih a' (by simp) s2 (hargs a' (by simp))
                      have hb'' := harg_ih b' (by simp) (translatePeTTa a' s2).2 (hargs b' (by simp))
                      have hc'' := harg_ih c' (by simp) (translatePeTTa b' (translatePeTTa a' s2).2).2
                        (hargs c' (by simp))
                      -- Output: (let f1 ta (let f2 tb tc))
                      -- Inner let is Translatable:
                      have hinner := translatable_expr_of_args "let"
                        [(freshVar "discard" (freshVar "discard" s).2).1,
                         (translatePeTTa b' (translatePeTTa a' s2).2).1,
                         (translatePeTTa c' (translatePeTTa b' (translatePeTTa a' s2).2).2).1]
                        (by decide) (by decide)
                        (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl
                            · exact hf2
                            · exact hb''
                            · exact hc'')
                      -- progn A B C: deep nesting.
                      unfold translatePeTTa; simp only [freshVar]
                      -- Goal is now concrete: Translatable (.expression [.symbol "let", fresh1, ta, inner])
                      -- where inner = .expression [.symbol "let", fresh2, tb, tc]
                      -- Use harg_ih (without unfold at *) via ih_bound
                      have ha_t := ih_bound a' (harg_le a' (by simp)) (s + 2) (hargs a' (by simp))
                      have hb_t := ih_bound b' (harg_le b' (by simp)) (translatePeTTa a' (s + 2)).2 (hargs b' (by simp))
                      have hc_t := ih_bound c' (harg_le c' (by simp))
                        (translatePeTTa b' (translatePeTTa a' (s + 2)).2).2 (hargs c' (by simp))
                      have hinner := translatable_expr_of_args "let"
                        [.var ("$__tr_discard_" ++ toString (s + 2)),
                         (translatePeTTa b' (translatePeTTa a' (s + 2)).2).1,
                         (translatePeTTa c' (translatePeTTa b' (translatePeTTa a' (s + 2)).2).2).1]
                        (by decide) (by decide)
                        (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl
                            · simp [Translatable, atomToPattern]
                            · exact hb_t
                            · exact hc_t)
                      exact translatable_expr_of_args "let"
                        [.var ("$__tr_discard_" ++ toString (s + 1)),
                         (translatePeTTa a' (s + 2)).1, _]
                        (by decide) (by decide)
                        (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl
                            · simp [Translatable, atomToPattern]
                            · exact ha_t
                            · exact hinner)
                    | cons _ _ =>
                      simpa [translatePeTTa, translatePeTTa.translatePeTTaList] using hgeneric
            · by_cases hprog1 : c = "prog1"
              · subst hprog1
                cases args with
                | nil => simpa [translatePeTTa, translatePeTTa.translatePeTTaList] using hgeneric
                | cons a' rest =>
                  cases rest with
                  | nil => simpa [translatePeTTa, translatePeTTa.translatePeTTaList] using hgeneric
                  | cons b' rest =>
                    cases rest with
                    | nil =>
                      -- prog1 A B → let $r A' (let $d B' $r)
                      have hfR : Translatable (freshVar "result" s).1 := by
                        simp [freshVar, Translatable, atomToPattern]
                      have hfD : Translatable (freshVar "discard" (freshVar "result" s).2).1 := by
                        simp [freshVar, Translatable, atomToPattern]
                      have s2 := (freshVar "discard" (freshVar "result" s).2).2
                      have ha'' := harg_ih a' (by simp) s2 (hargs a' (by simp))
                      have hb'' := harg_ih b' (by simp) (translatePeTTa a' s2).2 (hargs b' (by simp))
                      -- Inner: (let $d B' $r) — all args Translatable
                      have hinner := translatable_expr_of_args "let"
                        [(freshVar "discard" (freshVar "result" s).2).1,
                         (translatePeTTa b' (translatePeTTa a' s2).2).1,
                         (freshVar "result" s).1]
                        (by decide) (by decide)
                        (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl
                            · exact hfD
                            · exact hb''
                            · exact hfR)
                      -- prog1 A B → let $r A' (let $d B' $r)
                      unfold translatePeTTa; simp only [freshVar]
                      have ha_t := ih_bound a' (harg_le a' (by simp)) (s + 2) (hargs a' (by simp))
                      have hb_t := ih_bound b' (harg_le b' (by simp))
                        (translatePeTTa a' (s + 2)).2 (hargs b' (by simp))
                      have hfR : Translatable (.var ("$__tr_result_" ++ toString (s + 1))) := by
                        simp [Translatable, atomToPattern]
                      have hfD : Translatable (.var ("$__tr_discard_" ++ toString (s + 2))) := by
                        simp [Translatable, atomToPattern]
                      have hinner := translatable_expr_of_args "let"
                        [.var ("$__tr_discard_" ++ toString (s + 2)),
                         (translatePeTTa b' (translatePeTTa a' (s + 2)).2).1,
                         .var ("$__tr_result_" ++ toString (s + 1))]
                        (by decide) (by decide)
                        (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl
                            · exact hfD
                            · exact hb_t
                            · exact hfR)
                      exact translatable_expr_of_args "let"
                        [.var ("$__tr_result_" ++ toString (s + 1)),
                         (translatePeTTa a' (s + 2)).1, _]
                        (by decide) (by decide)
                        (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl
                            · exact hfR
                            · exact ha_t
                            · exact hinner)
                    | cons _ _ =>
                      simpa [translatePeTTa, translatePeTTa.translatePeTTaList] using hgeneric
              · by_cases hlt : c = "@<"
                · subst hlt
                  cases args with
                  | nil => simpa [translatePeTTa, translatePeTTa.translatePeTTaList] using hgeneric
                  | cons a' rest =>
                    cases rest with
                    | nil => simpa [translatePeTTa, translatePeTTa.translatePeTTaList] using hgeneric
                    | cons b' rest =>
                      cases rest with
                      | nil =>
                        have ha'' := harg_ih a' (by simp) s (hargs a' (by simp))
                        have hb'' := harg_ih b' (by simp) (translatePeTTa a' s).2 (hargs b' (by simp))
                        apply translatable_expr_of_args "<s"
                          [(translatePeTTa a' s).1, (translatePeTTa b' (translatePeTTa a' s).2).1]
                          (by decide) (by decide)
                        intro x hx; simp at hx
                        rcases hx with rfl | rfl
                        · exact ha''
                        · exact hb''
                      | cons _ _ =>
                        simpa [translatePeTTa, translatePeTTa.translatePeTTaList] using hgeneric
                · by_cases hgt : c = "@>"
                  · subst hgt
                    cases args with
                    | nil => simpa [translatePeTTa, translatePeTTa.translatePeTTaList] using hgeneric
                    | cons a' rest =>
                      cases rest with
                      | nil => simpa [translatePeTTa, translatePeTTa.translatePeTTaList] using hgeneric
                      | cons b' rest =>
                        cases rest with
                        | nil =>
                          have ha'' := harg_ih a' (by simp) s (hargs a' (by simp))
                          have hb'' := harg_ih b' (by simp) (translatePeTTa a' s).2 (hargs b' (by simp))
                          -- Output: (not (<s A' B'))
                          have hinner := translatable_expr_of_args "<s"
                            [(translatePeTTa a' s).1, (translatePeTTa b' (translatePeTTa a' s).2).1]
                            (by decide) (by decide)
                            (by intro x hx; simp at hx; rcases hx with rfl | rfl; exact ha''; exact hb'')
                          apply translatable_expr_of_args "not"
                            [.expression [.symbol "<s",
                              (translatePeTTa a' s).1,
                              (translatePeTTa b' (translatePeTTa a' s).2).1]]
                            (by decide) (by decide)
                          intro x hx; simp at hx; subst hx; exact hinner
                        | cons _ _ =>
                          simpa [translatePeTTa, translatePeTTa.translatePeTTaList] using hgeneric
                  · -- Generic fallback: no specific head matched
                    simpa [translatePeTTa, translatePeTTa.translatePeTTaList,
                      hprogn, hprog1, hlt, hgt] using hgeneric
          | _ => exfalso; simp [Translatable, atomToPattern] at ht
  exact this (sizeOf a) a (Nat.le_refl _) s h

/-- `translatePeTTa` preserves the proved fragment domain. -/
theorem translatePeTTa_preserves_soundness_domain (a : Atom) (s : Nat)
    (h : PureTranslatable a) :
    Translatable (translatePeTTa a s).1 :=
  translatePeTTa_translatable a s (PureTranslatable.toTranslatable h)

/-- Concrete pattern witness for translatePeTTa output. -/
theorem translatePeTTa_pattern_witness (a : Atom) (s : Nat)
    (h : PureTranslatable a) :
    ∃ p, atomToPattern (translatePeTTa a s).1 = some p :=
  translatable_witness _ (translatePeTTa_preserves_soundness_domain a s h)

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
  | .expression [.symbol "progn", _, _] => false
  | .expression [.symbol "progn", _, _, _] => false
  | .expression [.symbol "prog1", _, _] => false
  | .expression [.symbol "@<", _, _] => false
  | .expression [.symbol "@>", _, _] => false
  | _ => true

example : isHENormal (translatePeTTa (.expression [.symbol "progn",
    .symbol "a", .symbol "b"]) 0).1 = true := rfl

example : isHENormal (translatePeTTa (.expression [.symbol "prog1",
    .symbol "a", .symbol "b"]) 0).1 = true := rfl

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

/-- **Roundtrip idempotence (HE direction)**: after `translateHE`, applying
    `translatePeTTa` then `translateHE` again gives the same result.

    This is because `translateHE` output is PeTTa-normal (no chain/nop/etc.),
    and `translatePeTTa` doesn't introduce any HE-specific constructs — its
    output heads are `let`, `<s`, `not`, which `translateHE` doesn't rewrite.

    Council (Wadler, Coquand, GPT-Pro): this is the correct formal statement
    of roundtrip. NOT `translatePeTTa ∘ translateHE = id` (which is false),
    but `translateHE ∘ translatePeTTa ∘ translateHE = translateHE` (idempotence).

    Kernel-verified on all concrete cases above via `rfl`. The universal proof
    requires the same sizeOf-induction as `translateHE_translatable`. -/
theorem translateHE_idempotent_chain (a : Atom) (s : Nat) :
    let (petta, s1) := translateHE a s
    let (he2, s2) := translatePeTTa petta s1
    (translateHE he2 s2).1 = petta := by
  sorry

end Mettapedia.Languages.MeTTa.Translation
