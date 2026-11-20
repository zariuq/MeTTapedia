import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Budgets.Laws
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Budgets.Unifier
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Budgets.UnifierControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Budgets.OnTheStep

/-!
# Budgets as outcomes

* `Laws`: the budgeted decision procedure (`Procedure`: yes, no, exhausted, with laws 1 to 3 as fields; law 4 on a
  class, `AnsweredOn`); budget-indexed deciders and their first answer up to the budget (`Decider.procedure`); the
  search with no budget on the answered instances (`Decider.search`); the conversion check as an instance
  (`conversion`), and law 4 false without its hypothesis (`omega_undecided`).
* `Unifier`: the unifier's three remaining budgets as instances: the budget inside one round (`rounds`), the depth
  of phases (`phasesDepth`), the reader's depth (`readerDepth`).
* `UnifierControls`: their controls in the tree's tower, and where a canonical order of declarations does not remove
  the depth of phases.
* `OnTheStep`: exhaustion on the step: an observation beside the semantic step, never a refusal; the step's
  admission as an instance (`admission`).
-/
