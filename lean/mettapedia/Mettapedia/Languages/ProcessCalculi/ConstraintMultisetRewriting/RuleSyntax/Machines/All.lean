import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Rewriting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.TermRewriting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.MathlibMachine
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Counter
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Interpreter
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Branching
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Enumerable
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Separations

/-!
# Machines as programs of the step

The step is `RuleSyntax.step` at the one first-order frame over rows with unknowns
(`Presentation.Schematic.schematicStep`). A machine is hosted when its configurations are bags of ground rows,
its steps are rewrites of the bag by finitely many rules, and one machine step is one firing.

* **Runs of any length** (`Rewriting`): a state reads as a bag of ground rows when its knowledge is solvable and
  every solution reads its labels as the rows (`Reads`, `ReadsBag`; the tree's `ReadsAs` with solvable knowledge,
  `readsBag_iff`). For range-restricted positive programs an admitted firing at such a state is one rewrite of
  the bag by matching and its result reads as the rewritten bag (`readsBag_backward`); every rewrite is an
  admitted firing (`readsBag_forward`). The states that read as bags are closed under the step, so this is a
  correspondence of runs: `correspondence`, an `OperationalCorrespondence` from rewriting of bags to the step,
  one rewrite for one firing in each direction. Every bag is read from a state (`exists_reads`).
* **Term-rewriting machines** (`TermRewriting`): a finite list of rewrite schemas over rows, a configuration
  one ground row, a step a rewrite of the whole row. Its program takes one row and makes one row
  (`rootRules`, `rewrites_rootRules_iff`, `rootCorrespondence`).
* **The machine of the partial recursive functions** (`PartialRecursive`): Mathlib's `Turing.ToPartrec`
  machine, as authored in `Mettapedia.Languages.PartrecMachine`, is a term-rewriting machine with nineteen
  schemas. One reduction of the authored machine is one firing (`firing_of_reduction`,
  `reduction_of_firing`); the program halts with `w` from the pending evaluation of a code `c` on `v` exactly
  when `w ∈ c.eval v` (`halts_iff`, the authored machine's adequacy transported along `composite`); hence every
  partial recursive function is computed by this one program, with the code of the function as data
  (`computes_partrec`, by Mathlib's `Turing.ToPartrec.Code.exists_code`).
* **From Mathlib's machine** (`MathlibMachine`): a step of Mathlib's machine is one or more reductions of the
  authored machine; `fromMathlib` is one correspondence from Mathlib's machine to the step of the program, in
  which a firing is read back as no step or one step of Mathlib's machine and a step of Mathlib's machine is a
  path of firings (`halts_from_iff`).
* **Counter machines** (`Counter`): a row for the control and a row per register; an increment is one rule and
  a decrement two, each taking and making two rows; the test for zero is a pattern. One machine step is one
  firing (`Counter.firing_of_step`, `Counter.step_of_firing`, `Counter.machineCorrespondence`).

* **Transition systems with a partial recursive step** (`Interpreter`): the machine's nineteen schemas and a
  restart host the system `n ↦ m` with `[m] ∈ c.eval [n]` (`loopCorrespondence`, `hosts_partrec_system`).
  Where the code has no value the system is stuck and the program runs for ever (`runs_forever_of_none`);
  divergence is preserved (`infinite_run_of_source`); reachable numbers transfer both ways (`reaches_iff`);
  one step costs the machine's reductions and one firing (`step_cost`).
* **Finitely many successors, computed** (`Branching`): a code lists the successors; the computation is
  silent, one firing chooses a candidate, and leftover candidates are counted away. A weak correspondence
  whose silent firings end (`stepWeak`, `divergence_iff`), for a code with a value everywhere; where it has
  none, no weak correspondence exists (`no_weak_of_none`).
* **Recursively enumerable steps** (`Enumerable`): guess, check, commit; hosted in the may sense
  (`hosts_re`); `fromZero` is hosted in that sense and in the weak sense by no finite program
  (`fromZero_may`, `fromZero_not_weak`).
* **Between one firing per step and the weak sense** (`Separations`): `evenToZero` is hosted in the weak sense
  (`evenToZero_weak`) and, through the encoding by constants, one firing for one step by no finite list of rules
  (`evenToZero_not_oneStep`).

No rule of these programs has a read, a tell, an equation guard, a none check, a count check or a query
pattern. The correspondences are stated for the machines and systems above and for rewriting of bags by
range-restricted positive rules.
-/
