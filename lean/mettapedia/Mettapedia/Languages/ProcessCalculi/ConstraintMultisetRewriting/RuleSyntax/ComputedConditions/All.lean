import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Syntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Tables
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Intensional
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Rows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Determined
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Evaluation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Runs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.GraphRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.KernelStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.KernelEvaluation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.MachineRule
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Machine
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.MachineInvariants
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.MachineWords
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Neighbour
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.OpenRow
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.OpenValues
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.StoredRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.TestRules
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Calls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.CallInstances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.PermitCalls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.PermitCallInstances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.FrameEquality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Controls

/-!
# Computed conditions in rules

A rule that depends on the value of a function (`r := f(t̄)`) is read here by rules of `RuleSyntax`, with
`RuleSyntax.step` as its meaning. Two kinds of statement are kept apart: about ONE firing at one state, and
about RUNS, at every state a run reaches.

## One firing at one state

* **Syntax** (`Syntax`): rules with conditions over declared function names, a tabulation (one row former
  per function), the **table read** (`RuleWithCondition.tableRule`: also read the call's row) and the
  **rule at points** (`RuleWithCondition.at`: tell the call's row equal to a point of the graph); the
  program at a graph (`specialized`) is a program of the syntax whose membership is the evaluation.
* **Stored rows and points** (`Tables`): the table firing and the point firing with the same choices have
  the same information and the same result, and the table firing is admitted exactly when the point firing
  is and its table rows are present and not taken (`tableFiring_admits_iff`, `tableFiring_result`). One
  firing for one firing only where each point is stored at most once (`tables_unique`).
* **Range restriction** (`Rows`): the table read is range restricted exactly when every written unknown is
  bound by matching or occurs in a condition (`rangeRestricted_tableRule_iff`, `fragment_tableRule`).
* **Evaluation** (`Evaluation`): host code asks the call row and tells the value. The evaluated firing is
  admitted exactly when the POINT firing with the same choices is and the arguments are determined
  (`evalFiring_admits_iff`), which holds at every state that reads as rows for anchored arguments
  (`eval_iff_point_reads`; at a ground state `eval_iff_point`). The stored row is reached from the point
  through `tableFiring_admits_iff`. Controls: an argument only in an argument (`argumentOnly`), an argument
  that is its own value (`selfCall`), a row that holds an unknown (`OpenRow`).
* **The function in the frame's equality** (`FrameEquality`): with determined arguments the tell of the
  call is the tell of the value (`tell_iff_value`); matching is then matching modulo the equality
  (`take_of_call_admitted`, `rows_take_refused`).

## Along runs

* **States that read as bags** (`Determined`): the notion is `Machines.ReadsBag`. The step keeps it for
  rules whose made unknowns are bound by matching or determined by a tell, a wider fragment than range
  restriction, for programs given as sets (`stepCorrespondence`, `readsBag_of_run`); a made unknown that
  nothing determines leaves a state that reads as no rows (`result_not_reads`).
* **The evaluated program** (`Runs`): for evaluable rules it corresponds, one firing for one evaluation
  each way, to the atomic evaluation on bags (`evaluatedCorrespondence`), and at every state that reads as
  a bag its admitted firings are those of the program at the graph with the same choices
  (`evaluated_to_graph`, `graph_to_evaluated`).
* **The program at the graph** (`GraphRuns`): it corresponds to the same atomic evaluation on bags, with
  nothing asked of the arguments (`graphCorrespondence`), so it and the evaluated program have runs between
  states that read as the same bags (`graph_run_to_evaluated`, `evaluated_run_to_graph`).
* **A machine** (`Machine`, `MachineInvariants`, `MachineWords`): a reference machine on abstract stores,
  with operations of two outputs that may have no value and a destination that is also a source; its
  steps are the evaluations of the bag of rows of the store, and so the firings of the evaluated program
  at every state that reads as that bag (`Machine.hosted`, `Machine.composite`, `Machine.stuck_iff`); the
  store's invariants as properties of the bag (`Machine.Invariants`); an instance on 64-bit words.
  Controls: two cells at one key (`Neighbour`), a wrong function (`KernelEvaluation`,
  `Machine.wrong_value_made`), a made value nothing binds (`KernelEvaluation.kernel_result_not_reads`).
* **Stored tables** (`Intensional`, `StoredRuns`): two restricted relations relative to one set of table
  identities have the same runs (`runs_points_to_stored`, `runs_stored_to_points`, with an instance and a
  control); without identities chosen before the run, on states that read as bags, a run of the table
  reads at a store whose tables are true is a run of evaluations, and a run of evaluations is a run of the
  table reads beside the rows it uses (`StoredRuns.stored_run_to_evaluated`,
  `StoredRuns.evaluated_run_to_stored`).
* **Functions defined by rules** (`Calls`, `PermitCalls`): the call through a pending row. With a request
  that takes nothing the relation to the atomic evaluation is weak and the request fires without bound
  (`Calls`, `CallInstances.request_unbounded`). With a request that takes a permit made with the rule's
  rows the call corresponds to the atomic evaluation, its internal firings stop, and where the function
  has no value the pending row stays (`PermitCalls.permitCorrespondence`,
  `PermitCalls.internal_terminates`, `PermitCalls.undefined_waits_run`).

## Instances and controls

`KernelStep` and `KernelEvaluation` (an arithmetic instruction step, one state); `MachineRule` and
`TestRules` (rules of the machine of transform rules with their helpers as tables, and a test that is no
table read); `CallInstances` and `PermitCallInstances`; `Controls` (a wrong stored row, a rule that is not
blind, interpretations that overlap); `OpenValues` (a value that still holds a variable: what it is on the
step, and why it is none of the step's conditions).
-/
