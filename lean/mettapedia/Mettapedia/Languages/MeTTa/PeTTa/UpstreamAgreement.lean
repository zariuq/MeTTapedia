import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Agreement of the PeTTa machine with upstream answers

Each control runs a small program on the executable machine and states the
answers that upstream SWI-PeTTa gives for the same program and request
(upstream commit `b74af1b`). The controls cover equation alternatives in
order, conditionals and case selection over several answers, destructuring
`let*`, a `let` whose second binding conflicts with the first, `collapse`, and
an effect evaluated once for each alternative of a sibling argument. They also
cover literal `superpose`, `empty` and quotation, including inert quoted code;
argument lists matched element by element; calls with too few arguments, which
answer the partial application, and with too many, which fault; and `match`
bodies, which run once per matching row and do not run a matched value again.

They are checked by kernel evaluation of the machine itself. They are
controls, not a proof that the machine agrees with upstream on other
programs.

Upstream also gives these answers for forms the machine does not yet cover;
the machine currently leaves the unknown heads as data:

* `(progn (superpose (1 2)) 7)` gives `7 7`, and `(progn (empty) 7)` gives no
  answer: a sequence runs its last expression once per earlier answer;
* `(if True yes)` gives `yes`;
* with `(= (f 1) a)`, `(let $r (f $x) ($x $r))` gives `(1 a)`: an open call
  binds the caller's variable, which needs a substitution with each answer;
* `(add-atom &self (= (g) 5))` followed by `(g)` gives `5`: adding an equation
  at run time defines it. The machine's equations are fixed when the program is
  loaded, so it leaves `(g)` as data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.UpstreamAgreement

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program Equation)
open Eval

/-- The answers of a completed run that consumed no input and printed nothing. -/
def answersOf : Outcome → Option (List Atom)
  | .complete _ answers [] [] => some answers
  | _ => none

/-- Two requests run in order, the second in the state left by the first. -/
def answersOfTwo (program : Program) (fuel : Nat) (first second : Atom) :
    Option (List Atom × List Atom) :=
  match evaluate program fuel Effects.empty first with
  | .complete after answers [] [] =>
      (answersOf (evaluate program fuel after second)).map fun later => (answers, later)
  | _ => none

private def int (value : Int) : Atom := .grounded (.int value)
private def sym (name : String) : Atom := .symbol name
private def call (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)

/-- `(= (k) 1) (= (k) 2) (= (two) True) (= (two) False) (= (k2) Q) (= (k2) (Pair B))` -/
def program : Program where
  equations :=
    [⟨"k", [], int 1⟩, ⟨"k", [], int 2⟩,
     ⟨"two", [], Effects.boolean true⟩, ⟨"two", [], Effects.boolean false⟩,
     ⟨"k2", [], sym "Q"⟩, ⟨"k2", [], call "Pair" [sym "B"]⟩]
  declarations := []

/-- `(k)` gives `1 2`. -/
theorem equation_alternatives :
    answersOf (evaluate program 64 Effects.empty (call "k" [])) = some [int 1, int 2] := by
  decide +kernel

/-- `(if (two) yes no)` gives `yes no`. -/
theorem conditional_per_answer :
    answersOf (evaluate program 64 Effects.empty
      (call "if" [call "two" [], sym "yes", sym "no"])) = some [sym "yes", sym "no"] := by
  decide +kernel

/-- `(case (k) ((1 one) (2 two)))` gives `one two`. -/
theorem case_per_answer :
    answersOf (evaluate program 64 Effects.empty
      (call "case" [call "k" [],
        .expression [.expression [int 1, sym "one"], .expression [int 2, sym "two"]]])) =
      some [sym "one", sym "two"] := by
  decide +kernel

/-- `(let* (((Pair $y) (k2))) $y)` gives `B`; the alternative `Q` does not match. -/
theorem destructuring_let_star :
    answersOf (evaluate program 64 Effects.empty
      (call "let*" [.expression [.expression [call "Pair" [.var "y"], call "k2" []]],
        .var "y"])) = some [sym "B"] := by
  decide +kernel

/-- `(let $x 1 (let $x 2 $x))` gives no answer: the second binding tests the
value already captured by `$x`. -/
theorem conflicting_rebinding :
    answersOf (evaluate program 64 Effects.empty
      (call "let" [.var "x", int 1, call "let" [.var "x", int 2, .var "x"]])) = some [] := by
  decide +kernel

/-- A quoted raw `cons` pattern matches raw constructor data. -/
theorem quoted_constructor_binding :
    answersOf (evaluate program 64 Effects.empty
      (call "let"
        [call "quote" [call "cons" [.var "first", .var "rest"]],
         call "quote" [call "cons" [sym "a", sym "nil"]], .var "first"])) =
      some [sym "a"] := by
  decide +kernel

/-- The same quoted pattern does not conflate a native list with raw `cons`. -/
theorem quoted_constructor_native_list_refused :
    answersOf (evaluate program 64 Effects.empty
      (call "let"
        [call "quote" [call "cons" [.var "first", .var "rest"]],
         call "cons" [sym "a", call "quote" [.expression []]], .var "first"])) =
      some [] := by
  decide +kernel

/-- Ordinary `cons` destructuring retains the evaluator's native list view. -/
theorem ordinary_cons_binding :
    answersOf (evaluate program 64 Effects.empty
      (call "let" [call "cons" [.var "first", .var "rest"],
        call "quote" [.expression [sym "a", sym "b"]], .var "first"])) =
      some [sym "a"] := by
  decide +kernel

/-- `(collapse (k))` gives `(1 2)`. -/
theorem collapse_keeps_order :
    answersOf (evaluate program 64 Effects.empty (call "collapse" [call "k" []])) =
      some [.expression [int 1, int 2]] := by
  decide +kernel

/-- `(foo (k) (add-atom &self (mark z)))` gives `(foo 1 true) (foo 2 true)`, and
the effect runs once per alternative: `(collapse (match &self (mark $x) $x))`
then gives `(z z)`. -/
theorem effect_per_alternative :
    answersOfTwo program 128
      (call "foo" [call "k" [], call "add-atom" [sym "&self", call "mark" [sym "z"]]])
      (call "collapse" [call "match" [sym "&self", call "mark" [.var "x"], .var "x"]]) =
      some ([call "foo" [int 1, Effects.boolean true], call "foo" [int 2, Effects.boolean true]],
        [.expression [sym "z", sym "z"]]) := by
  decide +kernel

/-- `(= (visible) 7)`, loaded from source. -/
def visibleProgram : Program where
  equations := [⟨"visible", [], int 7⟩]
  declarations := []
  layout := [.equation]

/-- Loading adds the equation to `&self`, as upstream does:
`(collapse (match &self (= (visible) $body) $body))` gives `(7)`. -/
theorem loaded_equation_matches :
    answersOf (evaluate visibleProgram 64 (Effects.loaded visibleProgram)
      (call "collapse" [call "match" [sym "&self",
        call "=" [call "visible" [], .var "body"], .var "body"]])) =
      some [.expression [int 7]] := by
  decide +kernel

/-- `(get-atoms &self)` lists the loaded equation as a stored atom. -/
theorem loaded_equation_is_stored :
    answersOf (evaluate visibleProgram 64 (Effects.loaded visibleProgram)
      (call "get-atoms" [sym "&self"])) =
      some [call "=" [call "visible" [], int 7]] := by
  decide +kernel

/-- `(superpose ((+ 1 1) 3))` evaluates the alternatives and gives `2 3`. -/
theorem superpose_evaluates_alternatives :
    answersOf (evaluate program 64 Effects.empty
      (call "superpose" [.expression [call "+" [int 1, int 1], int 3]])) =
      some [int 2, int 3] := by
  decide +kernel

/-- Repeated alternatives remain repeated answer occurrences. -/
theorem superpose_keeps_duplicate_answers :
    answersOf (evaluate program 64 Effects.empty
      (call "superpose" [.expression [int 7, int 7]])) = some [int 7, int 7] := by
  decide +kernel

/-- An empty branch contributes no answer; later branches still run. -/
theorem superpose_continues_after_empty :
    answersOf (evaluate program 64 Effects.empty
      (call "superpose" [.expression [call "empty" [], int 7]])) = some [int 7] := by
  decide +kernel

/-- Completed empty answers and the ordinary false value are distinct. -/
theorem empty_is_not_false :
    answersOf (evaluate program 16 Effects.empty (call "empty" [])) = some [] ∧
    answersOf (evaluate program 16 Effects.empty (Effects.boolean false)) =
      some [Effects.boolean false] := by
  decide +kernel

/-- Quoted remainder-by-zero syntax is data and does not raise a primitive fault. -/
theorem quoted_code_is_inert :
    answersOf (evaluate program 16 Effects.empty
      (call "quote" [call "%" [int 1, int 0]])) =
      some [call "%" [int 1, int 0]] := by
  decide +kernel

/-- Unregistered `//` syntax stays data, including signed arguments. -/
theorem floor_division_stays_data :
    answersOf (evaluate program 64 Effects.empty (call "//" [int 7, int (-2)])) =
      some [call "//" [int 7, int (-2)]] := by
  decide +kernel

/-- Quotation retains the distinction between a symbol and its nullary expression. -/
theorem quoted_symbol_is_not_nullary_expression :
    answersOf (evaluate program 16 Effects.empty (call "quote" [sym "Bare"])) =
      some [sym "Bare"] ∧
    answersOf (evaluate program 16 Effects.empty (call "quote" [call "Bare" []])) =
      some [call "Bare" []] ∧ sym "Bare" ≠ call "Bare" [] := by
  decide +kernel

/-! ## Argument lists, arity and `match` bodies

The answers below are the same on SWI-PeTTa `e1db30d` (the corrected-stable
reference), `b74af1b` and upstream main `fea8317`, and on CeTTa's PeTTa lane.
-/

/-- The fault a run ended with, if it ended with one. -/
def faultOf : Outcome → Option Effects.Fault
  | .fault reason _ => some reason
  | _ => none

/-- Two requests run in order from `state`, the second in the state the first leaves. -/
def answersOfTwoFrom (program : Program) (fuel : Nat) (state : Effects.State)
    (first second : Atom) : Option (List Atom × List Atom) :=
  match evaluate program fuel state first with
  | .complete after answers [] [] =>
      (answersOf (evaluate program fuel after second)).map fun later => (answers, later)
  | _ => none

/-- The answers and the printed lines of a completed run that consumed no input. -/
def answersAndOutput : Outcome → Option (List Atom × List Atom)
  | .complete _ answers [] output => some (answers, output)
  | _ => none

/-- `(= (h cons $a $b) $b)` `(= (h3 $a $b $c) ($a $b $c))` `(= (f1 $x) (a $x))`
`(= (g $x) one)` `(= (g $x $y) two)` -/
def arityProgram : Program where
  equations :=
    [⟨"h", [sym "cons", .var "a", .var "b"], .var "b"⟩,
     ⟨"h3", [.var "a", .var "b", .var "c"], .expression [.var "a", .var "b", .var "c"]⟩,
     ⟨"f1", [.var "x"], call "a" [.var "x"]⟩,
     ⟨"g", [.var "x"], sym "one"⟩, ⟨"g", [.var "x", .var "y"], sym "two"⟩]
  declarations := []

/-- An equation's arguments are matched one by one, never through the `cons`
list view: `(h cons 1 2)` gives `2`, and `(h 7 8 9)` gives no answer. -/
theorem argument_list_is_not_a_cons_pattern :
    answersOf (evaluate arityProgram 64 Effects.empty (call "h" [sym "cons", int 1, int 2])) =
      some [int 2] ∧
    answersOf (evaluate arityProgram 64 Effects.empty (call "h" [int 7, int 8, int 9])) =
      some [] := by
  decide +kernel

/-- Fewer arguments than an equation takes give the partial application, with
the argument values held: `(h 1 2)` gives `(partial h (1 2))`, `(h3 (+ 1 1))`
gives `(partial h3 (2))`, and `(g)` gives `(partial g ())`. -/
theorem short_call_is_partial :
    answersOf (evaluate arityProgram 64 Effects.empty (call "h" [int 1, int 2])) =
      some [partialValue "h" [int 1, int 2]] ∧
    answersOf (evaluate arityProgram 64 Effects.empty (call "h3" [int 1, int 2])) =
      some [partialValue "h3" [int 1, int 2]] ∧
    answersOf (evaluate arityProgram 64 Effects.empty (call "h3" [call "+" [int 1, int 1]])) =
      some [partialValue "h3" [int 2]] ∧
    answersOf (evaluate arityProgram 64 Effects.empty (call "g" [])) =
      some [partialValue "g" []] := by
  decide +kernel

/-- The partial application is not the authored data `(partial h (1 2))`. -/
theorem partial_is_not_authored_data :
    partialValue "h" [int 1, int 2] ≠ call "partial" [sym "h", .expression [int 1, int 2]] := by
  decide

/-- Each arity of an overloaded function selects its own equations:
`(g 5)` gives `one` and `(g 5 6)` gives `two`. -/
theorem arity_selects_equations :
    answersOf (evaluate arityProgram 64 Effects.empty (call "g" [int 5])) = some [sym "one"] ∧
    answersOf (evaluate arityProgram 64 Effects.empty (call "g" [int 5, int 6])) =
      some [sym "two"] := by
  decide +kernel

/-- More arguments than every equation takes raise PeTTa's
`domain_error(function_input_arities(f, A), n)`: `(f1 1 2)` with `A = [1]`,
`(g 1 2 3)` with `A = [1, 2]`. -/
theorem long_call_faults :
    faultOf (evaluate arityProgram 64 Effects.empty (call "f1" [int 1, int 2])) =
      some (.overApplication "f1" [1] 2) ∧
    faultOf (evaluate arityProgram 64 Effects.empty (call "g" [int 1, int 2, int 3])) =
      some (.overApplication "g" [1, 2] 3) := by
  decide +kernel

/-- `(row 1) (row 2) (row 3) (rule (+ 1 2))`, loaded from source. -/
def rowsProgram : Program where
  equations := []
  declarations := []
  facts := [call "row" [int 1], call "row" [int 2], call "row" [int 3],
    call "rule" [call "+" [int 1, int 2]]]
  layout := [.fact, .fact, .fact, .fact]

/-- A `match` body is code that runs once per matching row:
`(match &self (row $x) (println! (seen $x)))` prints `(seen 1)`, `(seen 2)`,
`(seen 3)` once each and gives `true` three times. -/
theorem match_body_runs_once_per_row :
    answersAndOutput (evaluate rowsProgram 128 (Effects.loaded rowsProgram)
      (call "match" [sym "&self", call "row" [.var "x"],
        call "println!" [call "seen" [.var "x"]]])) =
      some ([Effects.boolean true, Effects.boolean true, Effects.boolean true],
        [call "seen" [int 1], call "seen" [int 2], call "seen" [int 3]]) := by
  decide +kernel

/-- `(collapse (match &self (row $x) (+ $x 10)))` gives `(11 12 13)`. -/
theorem match_body_computes :
    answersOf (evaluate rowsProgram 128 (Effects.loaded rowsProgram)
      (call "collapse" [call "match" [sym "&self", call "row" [.var "x"],
        call "+" [.var "x", int 10]]])) =
      some [.expression [int 11, int 12, int 13]] := by
  decide +kernel

/-- `(match &self (row $x) (add-atom &self (copy $x)))` adds one row per match,
so `(collapse (match &self (copy $y) $y))` then gives `(1 2 3)`. -/
theorem match_body_effect_once_per_row :
    answersOfTwoFrom rowsProgram 256 (Effects.loaded rowsProgram)
      (call "match" [sym "&self", call "row" [.var "x"],
        call "add-atom" [sym "&self", call "copy" [.var "x"]]])
      (call "collapse" [call "match" [sym "&self", call "copy" [.var "y"], .var "y"]]) =
      some ([Effects.boolean true, Effects.boolean true, Effects.boolean true],
        [.expression [int 1, int 2, int 3]]) := by
  decide +kernel

/-- A matched value is not evaluated again: the inner body `$t` of
`(match &self (rule $t) (match &self (rule $u) $t))` gives `(+ 1 2)`, not `3`. -/
theorem matched_value_is_not_run_again :
    answersOf (evaluate rowsProgram 128 (Effects.loaded rowsProgram)
      (call "match" [sym "&self", call "rule" [.var "t"],
        call "match" [sym "&self", call "rule" [.var "u"], .var "t"]])) =
      some [call "+" [int 1, int 2]] := by
  decide +kernel

/-! ## Recorded differences

Upstream gives other answers for the programs below. The machine's answers are
pinned here so that a change to either is visible.
-/

/-- `(= (f $x) (a $x))` `(= (g $x) (let $x 5 $x))` `(= (z 0) yes)` -/
def differenceProgram : Program where
  equations :=
    [⟨"f", [.var "x"], call "a" [.var "x"]⟩,
     ⟨"g", [.var "x"], call "let" [.var "x", int 5, .var "x"]⟩,
     ⟨"z", [int 0], sym "yes"⟩]
  declarations := []

/-- An equation added at run time. After `(add-atom &self (= (f $x) (b $x)))`,
upstream's `(f 1)` gives `(a 1) (b 1)`. The machine's equations are fixed when the
program loads, so it still gives `(a 1)`. -/
theorem added_equation_not_dispatched :
    answersOfTwo differenceProgram 64
      (call "add-atom" [sym "&self", call "=" [call "f" [.var "x"], call "b" [.var "x"]]])
      (call "f" [int 1]) =
      some ([Effects.boolean true], [call "a" [int 1]]) := by
  decide +kernel

/-- An unbound argument. Upstream's `(g $u)` unifies `$u` with the parameter, and the
body's `let` binds both to `5`: it gives `5`. The machine matches the head, so the
parameter holds the unbound `$u`, the `let` tests it against `5`, and there is no
answer. -/
theorem open_argument_not_bound :
    answersOf (evaluate differenceProgram 64 Effects.empty (call "g" [.var "u"])) = some [] := by
  decide +kernel

/-- A constructor head on an unbound argument. Upstream's
`(let $r (z $u) ($r $u))` unifies `$u` with `0` and gives `(yes 0)`. The machine
matches the head `0` against the unbound `$u`, which fails: there is no answer. -/
theorem constructor_head_open_argument :
    answersOf (evaluate differenceProgram 64 Effects.empty
      (call "let" [.var "r", call "z" [.var "u"], .expression [.var "r", .var "u"]])) =
      some [] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.UpstreamAgreement
