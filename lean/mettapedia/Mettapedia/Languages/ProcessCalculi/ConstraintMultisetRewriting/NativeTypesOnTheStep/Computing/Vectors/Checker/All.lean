import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Source
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Definitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Synthesis
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Refutation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Check
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Laws
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Acceptance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Guarantee
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.AppendGround
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Coverage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Controls

/-!
# A definition checker over the vectors package, run by the kernel

From a declared type and the rows of a definition to a verdict, with the rows' typings synthesized.

* `Source`: the source form (a declared telescope and result type, rows of patterns with bodies; the
  function in scope at its declared type); a computable elaboration of a row into its frame, what its
  patterns teach, and its made row, certified by the tree's executable checker; the row as a firing of
  the step.
* `Definitions`: `append` with its two rows, the row real HE lets through, the nil row answering nil,
  `head` on a successor length, the interpreter's literal row, and a body outside the synthesized
  class.
* `Synthesis`: the body's type in its own frame, by the tree's executable synthesis with the
  non-dependent pair rule, checked by the tree's executable check: the proof object the admission
  decision needs. Its class, and the abstraction just outside it.
* `Refutation`: a sound refusal at a solution of what the match teaches, from principal types of
  variables and constants against the normal form of the declared type.
* `Check`: the checker, three outcomes per row and per definition; soundness of yes (admitted by the
  converting step, typed after the match) and of no (refused for every settler).
* `Laws`: the checker as the tree's budgeted decision procedure, and the stability of elaboration in
  the budget.
* `Acceptance`: the verdicts by kernel evaluation, with what each one means, and the honesty of "not
  decided".
* `Guarantee`: with the package qualified, an admitted definition whose declared rows are its only rows
  answers every ground call at the call's declared type; a witness, and the second unchecked row that
  breaks it.
* `AppendGround`: every ground call of `append` on written-out vectors answers exactly once, the
  expected vector at `vec A (add n m)`, by induction.
* `Coverage`: coverage by the index, stated; `append` covers and fires a row on every ground call;
  `head` is admitted and partial, and the guarantee says nothing at length zero.
* `Controls`: the elaborated nil, head and literal rows are the audit's hand-written rows under the
  function; the synthesized types, shown; three definitions outside the elaborated class, not decided.
-/
