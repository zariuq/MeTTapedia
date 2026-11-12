import Mettapedia.Languages.MeTTa.PeTTa.Unifying

/-!
# A list view of an unknown, met again: where the model and the hosts differ

A pattern `(cons first rest)` against a value that is an unbound variable binds the variable
to the expression `(cons first rest)` itself (`unifyPattern` hands that case to
`unifyTerms`). The expression stands for a list whose first item is `first` and whose other
items are `rest`, a list whose end is not known yet. When a second view meets the same
variable, the model reads the expression as an ordinary three-item list, whose first item is
the symbol `cons`.

Both hosts keep the list. With `(= (two (cons $a $b) (cons $c $d)) (got $a $b $c $d))`, the
call `(two $x $x)` answers `(got $a $b $a $b)` on CeTTa's PeTTa lane and on SWI-PeTTa
(stable-fixed, 2026-11-12): the second view opens the cell the first one made. The model
answers `$c = cons` and `$d = ($a $b)`.

* `Controls.view_of_a_known_list_twice`: on a list that is known, two views agree, as on
  the hosts.
* `Controls.view_of_an_unknown_twice`: what the model answers on an unknown. This theorem
  records the difference; it stops holding when the view is taught to open such a cell.

Consequence: a statement that a call selects exactly the equations whose arguments are
solvable against the values cannot be read off the frames for values with an unknown list.
On values whose lists are known where a view meets them, the selection is the one the
hosts make.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- The pattern `(cons $first $rest)`. -/
def listView (first rest : String) : Atom :=
  .expression [.symbol "cons", .var first, .var rest]

/-- Positive: two views of the same known list `(p q)` agree: `$a` and `$c` are `p`, `$b`
and `$d` are `(q)`. -/
theorem view_of_a_known_list_twice :
    unifyArguments [] [listView "a" "b", listView "c" "d"]
        [.expression [.symbol "p", .symbol "q"], .expression [.symbol "p", .symbol "q"]] =
      .ok [("d", .expression [.symbol "q"]), ("c", .symbol "p"),
        ("b", .expression [.symbol "q"]), ("a", .symbol "p")] := by
  decide +kernel

/-- Negative (the model against the hosts): two views of the same unknown `$x`. The first
binds `$x` to `(cons $a $b)`; the second reads that as a three-item list and binds `$c` to
the symbol `cons` and `$d` to `($a $b)`. The hosts answer `$c = $a` and `$d = $b`. -/
theorem view_of_an_unknown_twice :
    unifyArguments [] [listView "a" "b", listView "c" "d"] [.var "x", .var "x"] =
      .ok [("d", .expression [.var "a", .var "b"]), ("c", .symbol "cons"),
        ("x", .expression [.symbol "cons", .var "a", .var "b"])] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Unifying.Controls
