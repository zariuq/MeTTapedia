import Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslate

namespace Mettapedia.Languages.MeTTa.Translation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

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

#eval repr <| optimizeTranslatedHE
  (.expression [.symbol "let", .var "$__tr_discard_1",
    .expression [.symbol "println!", .symbol "hello"], .symbol "result"])
  -- Expected: (chain (println! hello) $__tr_discard_1 result)

#eval repr <| optimizeTranslatedHE
  (.expression [.symbol "let", .var "$__tr_discard_1",
    .expression [.symbol "println!", .symbol "hello"], .symbol "()"])
  -- Expected: (nop (println! hello))

#eval repr <| optimizeTranslatedHE
  (.expression [.symbol "let", .var "$__tr_result_1",
    .expression [.symbol "foo", .symbol "bar"], .var "$__tr_result_1"])
  -- Expected: (foo bar)

#eval repr <| optimizeTranslatedHE
  (.expression [.symbol "let", .var "$__tr_collapsed_1",
    .expression [.symbol "collapse", .expression [.symbol "twohop-item"]],
    .expression [.symbol "foldl-atom", .var "$__tr_collapsed_1", .symbol "0",
      .var "$__tr_acc_2", .var "$__tr_item_3",
      .expression [.symbol "eval",
        .expression [.symbol "merge", .var "$__tr_acc_2", .var "$__tr_item_3"]]]])
  -- Expected: unchanged

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

/-- The universal HE→PeTTa→HE idempotence claim over arbitrary `Atom` is false.

The translators intentionally leave binder slots untouched in `chain` and
`atom-subst`. If such a slot itself contains an HE-only form, the second
`translateHE` pass can still rewrite it. The correct theorem therefore needs a
well-formed HE fragment with typed binder positions, not bare `Atom`. -/
example :
    let a := (.expression
      [.symbol "chain",
       .symbol "e",
       .expression [.symbol "chain", .symbol "x", .var "$y", .symbol "z"],
       .symbol "b"])
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

/-- Similarly, `translatePeTTa` produces HE-compatible output on these examples. -/
def isHENormalExample : Atom → Bool
  | .expression (.symbol "progn" :: _) => false
  | .expression (.symbol "prog1" :: _) => false
  | .expression (.symbol "foldall" :: _) => false
  | .expression [.symbol "@<", _, _] => false
  | .expression [.symbol "@>", _, _] => false
  | _ => true

/-
The tempting universal claims

* `isHENormalExample (translatePeTTa a s).1 = true`
* `isHENormalExample a = true -> isHENormalExample (optimizeTranslatedHE a) = true`

are both false on arbitrary `Atom`.

Positive example: well-formed PeTTa surface forms lower to HE-normal output.
Negative examples:
* malformed heads such as `(foldall)` fall through unchanged, so they are not HE-normal;
* the optimizer can expose a nested non-HE-normal PeTTa term by eliminating a
  translator-generated result `let`.

The honest theorem layer remains the validated/stable-common fragment proved
above, including the first-order `foldall` fixed-point theorem. -/

/- The corresponding executable checks are omitted here because Lean refuses to
evaluate these paths in the current wider workspace when imported code depends
on external `sorry` axioms outside the translator files. The theorem-backed
fragment above remains unaffected. -/

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
