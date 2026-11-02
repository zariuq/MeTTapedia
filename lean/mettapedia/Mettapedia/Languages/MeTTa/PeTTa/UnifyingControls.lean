import Mettapedia.Languages.MeTTa.PeTTa.Unifying

/-!
# Controls for PeTTa by two-way unification

Each control loads a program, runs requests in order on `Unifying.requests`, and
compares what each request answers (or prints) with what SWI-PeTTa `e1db30d`,
`b74af1b` and `fea8317` and CeTTa's PeTTa lane give for the same program, except
where a control says otherwise. The kernel computes every run.

The runtimes print an unbound variable as `$_0`, `$_1`, ... (CeTTa `$V0`, ...);
here it keeps its renamed name, such as `$v#0`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)
open LiveEquations (Observation)

private def int (value : Int) : Atom := .grounded (.int value)
private def sym (name : String) : Atom := .symbol name
private def var (name : String) : Atom := .var name
private def expr (items : List Atom) : Atom := .expression items
private def call (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private def eqn (head : String) (arguments : List Atom) (body : Atom) : Atom :=
  call "=" [call head arguments, body]
private def truth : Atom := Effects.boolean true
private def falsity : Atom := Effects.boolean false
private def letIn (pattern value body : Atom) : Atom := call "let" [pattern, value, body]
private def matchIn (pattern body : Atom) : Atom := call "match" [sym "&self", pattern, body]

/-- The program of the forms, as loading collects them. -/
def load (forms : List Atom) : Program :=
  match SpaceSemantics.collect forms with
  | .ok program => program
  | .error _ => { equations := [], declarations := [] }

/-- What each request answers, run in order on the loaded program. -/
def answers (forms asked : List Atom) : List Observation :=
  (requests (load forms) 400 (Effects.loaded (load forms)) asked).map observed

/-- What each request prints and answers, run in order on the loaded program. -/
def shows (forms asked : List Atom) : List Shown :=
  (requests (load forms) 400 (Effects.loaded (load forms)) asked).map shown

/-! ## Calls bind the caller's variables (c5, c6, u1, u2) -/

/-- c5: `(= (g $x) (let $x 5 $x))`: `!(g $u)` gives `5`, and so does
`!(let $u 5 $u)`. The callee's `let` binds the caller's `$u`. -/
theorem callee_let_binds_caller :
    answers [eqn "g" [var "x"] (letIn (var "x") (int 5) (var "x"))]
      [call "g" [var "u"], letIn (var "u") (int 5) (var "u")] =
      [.answers [int 5], .answers [int 5]] := by
  decide +kernel

/-- c6: `(= (z 0) yes)`. A constant in the head binds the caller's variable
(`(yes 0)`); a body alone leaves it unbound (`(yes $_0)`); a `let` pattern binds
it (`(yes 0)`); a bound argument that the head refuses gives no answer. -/
theorem constructor_head_binds_caller :
    answers [eqn "z" [int 0] (sym "yes")]
      [letIn (var "r") (call "z" [var "u"]) (expr [var "r", var "u"]),
       letIn (var "r") (sym "yes") (expr [var "r", var "u"]),
       letIn (var "r") (letIn (int 0) (var "u") (sym "yes")) (expr [var "r", var "u"]),
       letIn (var "u") (int 1) (call "z" [var "u"])] =
      [.answers [expr [sym "yes", int 0]], .answers [expr [sym "yes", var "u"]],
       .answers [expr [sym "yes", int 0]], .answers []] := by
  decide +kernel

/-- u1: `(= (bindv $x) (let $x 7 ok))`: `!(let $r (bindv $w) ($r $w))` gives
`(ok 7)`. PeTTa's `let` binds through the callee's parameter. -/
theorem let_binds_through_parameter :
    answers [eqn "bindv" [var "x"] (letIn (var "x") (int 7) (sym "ok"))]
      [letIn (var "r") (call "bindv" [var "w"]) (expr [var "r", var "w"])] =
      [.answers [expr [sym "ok", int 7]]] := by
  decide +kernel

/-- u2: `(= (inc $x) (let $x (+ $x 1) $x))`: `!(inc 5)` has no answer: the
`let` unifies `5` with `6`. -/
theorem let_is_a_told_equation :
    answers [eqn "inc" [var "x"] (letIn (var "x") (call "+" [var "x", int 1]) (var "x"))]
      [call "inc" [int 5]] = [.answers []] := by
  decide +kernel

/-! ## Branches keep their own bindings (u5) -/

/-- u5: with `(= (z 0) yes)` and `(= (z 1) no)`, each answer of `(z $u)` comes
with its own binding of `$u`, inside `collapse` too. -/
theorem branches_keep_their_bindings :
    answers [eqn "z" [int 0] (sym "yes"), eqn "z" [int 1] (sym "no")]
      [letIn (var "r") (call "z" [var "u"]) (expr [var "r", var "u"]),
       call "collapse" [letIn (var "r") (call "z" [var "u"]) (expr [var "r", var "u"])],
       letIn (var "r") (call "z" [var "u"])
         (letIn (var "s") (call "z" [var "u"]) (expr [var "r", var "s", var "u"]))] =
      [.answers [expr [sym "yes", int 0], expr [sym "no", int 1]],
       .answers [expr [expr [sym "yes", int 0], expr [sym "no", int 1]]],
       .answers [expr [sym "yes", sym "yes", int 0], expr [sym "no", sym "no", int 1]]] := by
  decide +kernel

/-! ## `match` unifies two ways; rows are fresh at each use (u3) -/

/-- u3: stored rows with variables. `(fact $y 2)` answers `(fact 1 $v)` with
`2`; `(same $z $z)` answers `(same 1 $v)` with `1`; the two uses of `(box $k)`
get separate variables, so `$a` and `$b` take `1` and `2`; and a variable of the
request bound by a row is bound later in the same branch (`(9 2)`). -/
theorem match_unifies_two_ways :
    answers [call "fact" [var "y", int 2], call "same" [var "z", var "z"], call "box" [var "k"]]
      [matchIn (call "fact" [int 1, var "v"]) (var "v"),
       matchIn (call "same" [int 1, var "v"]) (var "v"),
       matchIn (call "box" [var "a"])
         (matchIn (call "box" [var "b"])
           (letIn (var "a") (int 1) (letIn (var "b") (int 2) (expr [var "a", var "b"])))),
       letIn (var "p") (matchIn (call "fact" [var "q", var "w"]) (expr [var "q", var "w"]))
         (letIn (var "q") (int 9) (var "p"))] =
      [.answers [int 2], .answers [int 1], .answers [expr [int 1, int 2]],
       .answers [expr [int 9, int 2]]] := by
  decide +kernel

/-- u11: a `match` pattern has no list view: `(cons $a $b)` does not match the
list `(1 2 3)`, and `($a $b $c)` does. -/
theorem match_pattern_has_no_list_view :
    answers [call "row" [expr [int 1, int 2, int 3]]]
      [call "collapse" [matchIn (call "row" [call "cons" [var "a", var "b"]]) (expr [var "a", var "b"])],
       call "collapse" [matchIn (call "row" [expr [var "a", var "b", var "c"]])
         (expr [var "a", var "b", var "c"])]] =
      [.answers [expr []], .answers [expr [expr [int 1, int 2, int 3]]]] := by
  decide +kernel

/-! ## `remove-atom` removes by unification (u4, u13) -/

/-- u4: `(remove-atom &self (item $x))` removes both `item` rows; the ground
pattern `(gen 5)` removes the stored row `(gen $k)`. -/
theorem removal_by_unification :
    answers [call "item" [int 1], call "item" [int 2], call "other" [int 3], call "gen" [var "k"]]
      [call "remove-atom" [sym "&self", call "item" [var "x"]],
       call "collapse" [matchIn (call "item" [var "y"]) (var "y")],
       call "collapse" [matchIn (call "other" [var "y"]) (var "y")],
       call "remove-atom" [sym "&self", call "gen" [int 5]],
       call "collapse" [matchIn (call "gen" [var "y"]) (sym "found")]] =
      [.answers [truth], .answers [expr []], .answers [expr [int 3]], .answers [truth],
       .answers [expr []]] := by
  decide +kernel

/-- u13: removing an `=` row answers whether a row was removed (SWI-PeTTa;
CeTTa answers `True` both times). `(= (f 1) (a 1))` unifies with the stored
`(= (f $x) (a $x))` and removes it, so a later `(f 2)` is data. -/
theorem equation_removal_answers_whether_removed :
    answers [eqn "f" [var "x"] (call "a" [var "x"])]
      [call "remove-atom" [sym "&self", eqn "g" [var "x"] (call "b" [var "x"])],
       call "remove-atom" [sym "&self", eqn "f" [int 1] (call "a" [int 1])],
       call "f" [int 2]] =
      [.answers [falsity], .answers [truth], .answers [call "f" [int 2]]] := by
  decide +kernel

/-! ## `case`, `let` patterns, fresh variables, `collapse` copies (u7, u9, u12) -/

/-- u7: `case` unifies its key with each pattern in turn and commits to the
first that unifies. -/
theorem case_unifies_and_commits :
    answers []
      [letIn (var "r") (call "case" [var "u", expr [expr [int 0, sym "zero"], expr [int 1, sym "one"]]])
         (expr [var "r", var "u"]),
       letIn (var "r") (call "case" [call "pair" [var "u", int 5],
           expr [expr [call "pair" [int 1, var "v"], expr [var "v", sym "first"]],
                 expr [call "pair" [var "w", var "w"], sym "same"]]])
         (expr [var "r", var "u"])] =
      [.answers [expr [sym "zero", int 0]],
       .answers [expr [expr [int 5, sym "first"], int 1]]] := by
  decide +kernel

/-- u9: a `let` pattern unifies two ways; each call of `(= (mk) $v)` makes a
fresh variable; a variable shared in a callee's result stays shared. -/
theorem let_patterns_and_fresh_variables :
    answers [eqn "mk" [] (var "v"), eqn "two" [] (call "pair" [var "v", var "v"])]
      [letIn (call "pair" [var "a", int 2]) (call "pair" [int 1, var "b"]) (expr [var "a", var "b"]),
       letIn (var "x") (call "mk" [])
         (letIn (var "y") (call "mk" [])
           (letIn (var "x") (int 1) (letIn (var "y") (int 2) (expr [var "x", var "y"])))),
       letIn (call "pair" [var "a", var "b"]) (call "two" []) (letIn (var "a") (int 3) (var "b")),
       call "mk" []] =
      [.answers [expr [int 1, int 2]], .answers [expr [int 1, int 2]], .answers [int 3],
       .answers [var "v#0"]] := by
  decide +kernel

/-- u12: `collapse` collects copies, as `findall`: each answer's variables are
renamed apart, and a later binding of the request's `$u` does not reach them. -/
theorem collapse_collects_copies :
    answers []
      [letIn (var "c") (call "collapse" [call "superpose" [expr [var "u", var "u"]]])
         (letIn (var "u") (int 5) (expr [var "c", var "u"]))] =
      [.answers [expr [expr [var "u#0", var "u#1"], int 5]]] := by
  decide +kernel

/-! ## The occurs check (u6) -/

/-- u6: `(= (self $x $x) ok)` and the row `(p $y (f $y))`. Unifying `$u` with
`(f $u)` has no unifier here, as in CeTTa and in SWI-PeTTa with the Prolog flag
`occurs_check` set to `true`. SWI-PeTTa's default unification builds the cyclic
term instead: it answers `(ok done)` and `(found)` for the first two requests,
and filters the third, whose output is the cyclic term. -/
theorem occurs_check :
    answers [eqn "self" [var "x", var "x"] (sym "ok"), call "p" [var "y", call "f" [var "y"]]]
      [letIn (var "r") (call "self" [var "u", call "f" [var "u"]]) (expr [var "r", sym "done"]),
       call "collapse" [matchIn (call "p" [var "x", var "x"]) (sym "found")],
       call "collapse" [matchIn (call "p" [var "x", var "x"]) (var "x")]] =
      [.answers [], .answers [expr []], .answers [expr []]] := by
  decide +kernel

/-! ## The list view of a head pattern (u10, u10b) -/

/-- u10: `(= (hd (cons $a $b)) $a)`. A list argument is read by its head and
tail. An unbound argument is bound to `(cons $a $b)`, which is how the runtimes
print the open list they build: `($_0 (cons $_0 $_1))`. -/
theorem head_list_view :
    answers [eqn "hd" [call "cons" [var "a", var "b"]] (var "a")]
      [call "hd" [expr [int 1, int 2, int 3]],
       letIn (var "r") (call "hd" [var "u"]) (expr [var "r", var "u"])] =
      [.answers [int 1],
       .answers [expr [var "a#0", call "cons" [var "a#0", var "b#0"]]]] := by
  decide +kernel

/-- u10b, a divergence of the finite carrier: the runtimes later read the open
list `(cons $a $b)` as a list (`1`), while here it is an expression of three
items, which `(1 2)` does not unify with. -/
theorem open_list_tail_is_not_a_list :
    answers [eqn "hd" [call "cons" [var "a", var "b"]] (var "a")]
      [letIn (var "r") (call "hd" [var "u"]) (letIn (var "u") (expr [int 1, int 2]) (var "r"))] =
      [.answers []] := by
  decide +kernel

/-! ## The round-1 corpus on this machine (c1-c4) -/

/-- c1: the argument list is matched element by element. -/
theorem argument_list_element_by_element :
    answers [eqn "h" [sym "cons", var "a", var "b"] (var "b")]
      [call "h" [sym "cons", int 1, int 2], call "h" [int 7, int 8, int 9], call "h" [int 1, int 2]] =
      [.answers [int 2], .answers [], .answers [Eval.partialValue "h" [int 1, int 2]]] := by
  decide +kernel

/-- c2a, c2b: arity first (P-APP-1). -/
theorem arity_first :
    answers [eqn "h3" [var "a", var "b", var "c"] (expr [var "a", var "b", var "c"]),
        eqn "g" [var "x"] (sym "one"), eqn "g" [var "x", var "y"] (sym "two"),
        eqn "f1" [var "x"] (call "a" [var "x"])]
      [call "h3" [int 1, int 2], call "h3" [call "+" [int 1, int 1]], call "g" [],
       call "g" [int 5], call "g" [int 5, int 6], call "f1" [int 1, int 2]] =
      [.answers [Eval.partialValue "h3" [int 1, int 2]], .answers [Eval.partialValue "h3" [int 2]],
       .answers [Eval.partialValue "g" []], .answers [sym "one"], .answers [sym "two"],
       .fault (.overApplication "f1" [1] 2)] := by
  decide +kernel

/-- c3, c3b: a `match` body runs once per row, and a matched value is not run
again. -/
theorem match_bodies :
    shows [call "row" [int 1], call "row" [int 2], call "row" [int 3], call "rule" [call "+" [int 1, int 2]]]
      [matchIn (call "row" [var "x"]) (call "println!" [call "seen" [var "x"]]),
       call "collapse" [matchIn (call "row" [var "x"]) (call "+" [var "x", int 10])],
       matchIn (call "rule" [var "t"]) (matchIn (call "rule" [var "u"]) (var "t"))] =
      [.printed [call "seen" [int 1], call "seen" [int 2], call "seen" [int 3]] [truth, truth, truth],
       .printed [] [expr [int 11, int 12, int 13]],
       .printed [] [call "+" [int 1, int 2]]] := by
  decide +kernel

/-- c4, c4c: equations are live. Adding one defines it for later calls, removing
one withdraws it, and a request is classified when it starts. -/
theorem live_equations :
    answers [eqn "f" [var "x"] (call "a" [var "x"])]
      [call "f" [int 1],
       call "add-atom" [sym "&self", eqn "f" [var "x"] (call "b" [var "x"])],
       call "f" [int 1],
       call "remove-atom" [sym "&self", eqn "f" [var "x"] (call "a" [var "x"])],
       call "f" [int 1],
       letIn (var "u") (call "add-atom" [sym "&self", eqn "g" [] (int 5)]) (call "g" []),
       call "g" []] =
      [.answers [call "a" [int 1]], .answers [truth], .answers [call "a" [int 1], call "b" [int 1]],
       .answers [truth], .answers [call "b" [int 1]], .answers [call "g" []], .answers [int 5]] := by
  decide +kernel

/-- c2c: a call longer than every arity faults, listing the arities. -/
theorem over_application_lists_arities :
    answers [eqn "g" [var "x"] (sym "one"), eqn "g" [var "x", var "y"] (sym "two")]
      [call "g" [int 1, int 2, int 3]] = [.fault (.overApplication "g" [1, 2] 3)] := by
  decide +kernel

/-- c4b, c4d, c4e, c4i: an `=` row in a private space defines nothing in `&self`; a
new arity is a call in a later request; removing the last equation makes the
call data; a stored body is classified with the request that runs it. -/
theorem live_equations_family :
    answers [] [letIn (var "s") (call "new-space" [])
        (call "add-atom" [var "s", eqn "pf" [var "x"] (call "p" [var "x"])]),
      call "pf" [int 1],
      call "collapse" [matchIn (eqn "pf" [var "x"] (var "b")) (var "b")]] =
      [.answers [truth], .answers [call "pf" [int 1]], .answers [expr []]] ∧
    answers [eqn "f" [var "x"] (call "a" [var "x"])]
      [call "add-atom" [sym "&self", eqn "f" [var "x", var "y"] (call "c" [var "x", var "y"])],
       call "f" [int 1, int 2], call "f" [int 1]] =
      [.answers [truth], .answers [call "c" [int 1, int 2]], .answers [call "a" [int 1]]] ∧
    answers [eqn "k" [var "x"] (call "a" [var "x"])]
      [call "remove-atom" [sym "&self", eqn "k" [var "x"] (call "a" [var "x"])], call "k" [int 1]] =
      [.answers [truth], .answers [call "k" [int 1]]] ∧
    answers [eqn "h" [] (call "g" [])]
      [call "h" [], letIn (var "u") (call "add-atom" [sym "&self", eqn "g" [] (int 5)]) (call "h" []),
       call "h" []] =
      [.answers [call "g" []], .answers [call "g" []], .answers [int 5]] := by
  decide +kernel

/-- c4f, c4h: within one request, selection reads the live rows, while the
classification by arity was made when the request started. -/
theorem same_request_live_selection :
    answers [eqn "f" [var "x"] (call "a" [var "x"])]
      [letIn (var "u") (call "add-atom" [sym "&self", eqn "f" [var "x"] (call "b" [var "x"])])
         (call "f" [int 1]),
       letIn (var "u") (call "remove-atom" [sym "&self", eqn "f" [var "x"] (call "a" [var "x"])])
         (call "f" [int 1])] =
      [.answers [call "a" [int 1], call "b" [int 1]], .answers [call "b" [int 1]]] ∧
    answers [eqn "f" [var "x"] (call "a" [var "x"])]
      [letIn (var "u") (call "add-atom" [sym "&self", eqn "f" [var "x", var "y"] (call "c" [var "x", var "y"])])
         (call "f" [int 1, int 2])] =
      [.fault (.overApplication "f" [1] 2)] := by
  decide +kernel

/-- u8: `unify` is defined only in PeTTa's HE-compatibility library, which none
of the four runtimes loads by default: the call is data, its arguments
evaluated. -/
theorem unify_is_not_in_the_prelude :
    answers []
      [call "unify" [call "f" [var "a", int 2], call "f" [int 1, var "b"], expr [var "a", var "b"],
        sym "none"]] =
      [.answers [call "unify" [call "f" [var "a", int 2], call "f" [int 1, var "b"],
        expr [var "a", var "b"], sym "none"]]] := by
  decide +kernel

/-- c3 (rest), c3b (rest): a body that adds a row runs once per row, and the
rows it added are read back; a matched value is a value. -/
theorem match_bodies_effects :
    answers [call "row" [int 1], call "row" [int 2], call "row" [int 3], call "rule" [call "+" [int 1, int 2]]]
      [matchIn (call "row" [var "x"]) (call "add-atom" [sym "&self", call "copy" [var "x"]]),
       call "collapse" [matchIn (call "copy" [var "y"]) (var "y")],
       matchIn (call "rule" [var "t"]) (var "t")] =
      [.answers [truth, truth, truth], .answers [expr [int 1, int 2, int 3]],
       .answers [call "+" [int 1, int 2]]] := by
  decide +kernel

/-- u14: a `let` that would bind `$u` to `(f $u)` has no answer, and neither has
one that would bind `$b` to `(g $b)` through a shared pattern variable, as in
CeTTa and in SWI-PeTTa with `occurs_check` set to `true`; SWI-PeTTa's default
answers `ok` and `done`. -/
theorem let_occurs_check :
    answers []
      [letIn (var "u") (call "f" [var "u"]) (sym "ok"),
       letIn (call "pair" [var "a", var "a"]) (call "pair" [var "b", call "g" [var "b"]]) (sym "done")] =
      [.answers [], .answers []] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Unifying.Controls
