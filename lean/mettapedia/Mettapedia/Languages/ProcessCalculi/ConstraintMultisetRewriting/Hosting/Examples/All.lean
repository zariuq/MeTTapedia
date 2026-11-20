import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Examples.Fragments
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Examples.SecondOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Examples.Recursion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Examples.UserPrograms

/-!
# Examples of hosted programs

* `Fragments`: which elaborated programs lie in the first fragment, by the reading of their arguments.
* `SecondOrder`: the step does the second-order solving of a schema's left side (`step_solves_F`,
  `not_constant`).
* `Recursion`: a recursive function whose recursive call is under a `let` runs through the translation
  with two pending frames of that `let` at two depths (`two_frames`, `invariant_at_two_frames`).
* `UserPrograms`: `len` and mutual recursion, elaborated by value, satisfy the run theorems'
  hypotheses (`len_hosted`, `evenOdd_hosted`).

Programs whose text contains a call through a function variable are not among these examples.
-/
