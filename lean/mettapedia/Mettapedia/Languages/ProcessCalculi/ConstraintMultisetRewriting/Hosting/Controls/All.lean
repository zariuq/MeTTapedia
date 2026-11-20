import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Controls.Unopened
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Controls.HygieneNotNecessary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Controls.ShadowRun
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Controls.UnusedClauses

/-!
# Controls of the run theorems' hypotheses

* `Unopened`: the hypothesis that the query's names are unopened is needed (`unopened_needed`).
* `HygieneNotNecessary`: hygiene of a frame is sufficient for the correspondence of a bind and is not
  necessary (`not_private`, `transfer_holds`); a `let` query runs through the hygienic run theorem
  (`let_query_hosted`).
* `ShadowRun`: where hygiene fails on a run, the run theorem's conclusion fails (`no_frontier`).
* `UnusedClauses`: a program that is not well formed and satisfies the clauses the run theorems use
  (`not_wellFormed`, `scoped_clauses`, `runs_forward_applies`).

The controls of composition are in `Composition.Controls`.
-/
